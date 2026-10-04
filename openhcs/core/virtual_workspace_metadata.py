"""Typed OpenHCS virtual-workspace metadata carriers."""

from __future__ import annotations

import json
import logging
import os
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType
from typing import Any, Callable, TypeAlias

from polystore.atomic import FileLockError, atomic_update_json
from polystore.metadata_writer import MetadataConfig
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import AllComponents
from openhcs.core.artifacts import ArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_bindings import SourceProjectionRole
from openhcs.core.source_metadata import (
    DurableSourceMetadata,
    SourceMetadataMapping,
    SourceMetadataScalar,
    SourceVoxelSpacing,
)
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourcePlaneProjection,
    SourceProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.source_tile_geometry import SourceTileLayout


@dataclass(frozen=True)
class OpenHCSMetadataConfig(MetadataConfig):
    """Configuration owned by the OpenHCS metadata file contract."""

    METADATA_FILENAME: str = field(
        default_factory=lambda: os.getenv(
            "OPENHCS_METADATA_FILENAME", "openhcs_metadata.json"
        )
    )


METADATA_CONFIG = OpenHCSMetadataConfig()


class MetadataWriteError(Exception):
    """Raised when an OpenHCS metadata transaction fails."""


class AtomicMetadataWriter:
    """Atomically update subdirectory-keyed OpenHCS metadata."""

    def __init__(self, timeout: float = METADATA_CONFIG.DEFAULT_TIMEOUT):
        self.timeout = timeout
        self.logger = logging.getLogger(__name__)

    def update_available_backends(
        self,
        metadata_path: str | Path,
        available_backends: dict[str, bool],
    ) -> None:
        def update(data: dict[str, Any] | None) -> dict[str, Any]:
            if data is None:
                raise MetadataWriteError(
                    "Cannot update backends: metadata file does not exist"
                )
            data[METADATA_CONFIG.AVAILABLE_BACKENDS_KEY] = available_backends
            return data

        self._execute_update(metadata_path, update)

    def merge_subdirectory_metadata(
        self,
        metadata_path: str | Path,
        subdirectory_updates: dict[str, dict[str, Any]],
    ) -> None:
        def update(data: dict[str, Any] | None) -> dict[str, Any]:
            data = self._ensure_subdirectories_structure(data)
            subdirectories = data[METADATA_CONFIG.SUBDIRECTORIES_KEY]
            for subdirectory_name, fields in subdirectory_updates.items():
                subdirectory = subdirectories.setdefault(subdirectory_name, {})
                for key, value in fields.items():
                    if key == METADATA_CONFIG.AVAILABLE_BACKENDS_KEY and isinstance(
                        value, dict
                    ):
                        subdirectory[key] = {
                            **subdirectory.get(key, {}),
                            **value,
                        }
                    else:
                        subdirectory[key] = value
                self._update_projection_geometry(
                    subdirectory,
                    VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
                        subdirectory
                    ).entries.values(),
                )
            return data

        self._execute_update(
            metadata_path,
            update,
            {METADATA_CONFIG.SUBDIRECTORIES_KEY: {}},
        )

    def replace_subdirectory_metadata(
        self,
        metadata_path: str | Path,
        subdirectory_name: str,
        subdirectory_metadata: dict[str, Any],
    ) -> None:
        def update(data: dict[str, Any] | None) -> dict[str, Any]:
            data = self._ensure_subdirectories_structure(data)
            data[METADATA_CONFIG.SUBDIRECTORIES_KEY][subdirectory_name] = dict(
                subdirectory_metadata
            )
            return data

        self._execute_update(
            metadata_path,
            update,
            {METADATA_CONFIG.SUBDIRECTORIES_KEY: {}},
        )

    def merge_source_projection_metadata(
        self,
        metadata_path: str | Path,
        subdirectory_name: str,
        projection_entries: VirtualWorkspaceSourceProjectionEntries,
    ) -> None:
        """Merge exact produced paths under one lock, preserving other wells."""

        def update(data):
            data = self._ensure_subdirectories_structure(data)
            subdirectory = data[METADATA_CONFIG.SUBDIRECTORIES_KEY].setdefault(
                subdirectory_name, {}
            )
            entries = projection_entries.merge_into_subdirectory(subdirectory)
            self._update_projection_geometry(
                subdirectory,
                entries.entries.values(),
            )
            return data

        self._execute_update(metadata_path, update)

    def publish_source_projection_metadata(
        self,
        metadata_path: str | Path,
        subdirectory_name: str,
        projection_entries: VirtualWorkspaceSourceProjectionEntries | None,
        *,
        serializer: SourceProjectionMetadataSerializer,
        saved_image_paths: Sequence[str],
        microscope_handler_name: str,
        source_filename_parser_name: str,
        component_labels: Mapping[AllComponents, Mapping[str, str | None] | None],
        backend: str,
        is_main: bool,
        results_dir: str | None,
    ) -> None:
        """Publish saved inventory from retained addresses, never generated names.

        Final reconciliation uses the same durable typed projections after step
        memory has been released. Missing producer records fail rather than
        inventing coordinates from filenames or the input label cache.
        """
        saved_paths = tuple(saved_image_paths)

        def update(data):
            data = self._ensure_subdirectories_structure(data)
            subdirectory = data[METADATA_CONFIG.SUBDIRECTORIES_KEY].setdefault(
                subdirectory_name, {}
            )
            entries = (
                VirtualWorkspaceSourceProjectionEntries(MappingProxyType({}))
                if projection_entries is None else projection_entries
            ).publish_into_subdirectory(
                subdirectory,
                saved_image_paths=saved_paths,
                reconcile_directory=(
                    subdirectory_name if projection_entries is None else None
                ),
            ).entries
            # Concurrent axes may persist their pixels before publishing their
            # own producer records. A step publishes known saved addresses only;
            # completed-plate reconciliation requires the entire saved inventory.
            published_paths = tuple(path for path in saved_paths if path in entries)
            if published_paths:
                projections = SourceProjectionSet(
                    tuple(entries[path] for path in published_paths)
                )
                subdirectory.update(
                    serializer.component_metadata(projections, labels=component_labels)
                )
            subdirectory[FIELDS.IMAGE_FILES] = list(published_paths)
            subdirectory[FIELDS.MICROSCOPE_HANDLER_NAME] = microscope_handler_name
            subdirectory[FIELDS.SOURCE_FILENAME_PARSER_NAME] = (
                source_filename_parser_name
            )
            subdirectory[FIELDS.AVAILABLE_BACKENDS] = {
                **subdirectory.get(FIELDS.AVAILABLE_BACKENDS, {}),
                backend: True,
            }
            if is_main:
                subdirectory[serializer.MAIN_FIELD] = True
            if results_dir is not None:
                subdirectory[serializer.RESULTS_DIR_FIELD] = results_dir
            self._update_projection_geometry(
                subdirectory,
                entries.values(),
            )
            return data

        self._execute_update(metadata_path, update)

    @staticmethod
    def _update_projection_geometry(
        subdirectory: dict[str, Any],
        source_projections: Iterable[SourceProjection],
    ) -> None:
        """Derive geometry from the transaction's current nominal projections."""
        unique_projections: dict[tuple[object, ...], SourceProjection] = {}
        for projection in source_projections:
            unique_projections.setdefault(projection.identity_key, projection)
        if not unique_projections:
            return
        projections = SourceProjectionSet(tuple(unique_projections.values()))
        subdirectory[FIELDS.GRID_DIMENSIONS] = (
            SourceTileLayout.metadata_grid_dimensions(projections)
        )
        subdirectory[FIELDS.PIXEL_SIZE] = SourceVoxelSpacing.metadata_pixel_size(
            SourceVoxelSpacing.from_source_metadata(projection.source_metadata)
            for projection in projections.execution_anchor_projections
        )

    def _execute_update(
        self,
        metadata_path: str | Path,
        update: Callable[[dict[str, Any] | None], dict[str, Any]],
        default_data: dict[str, Any] | None = None,
    ) -> None:
        try:
            atomic_update_json(metadata_path, update, self.timeout, default_data)
        except FileLockError as exc:
            raise MetadataWriteError(f"Failed to update metadata: {exc}") from exc

    @staticmethod
    def _ensure_subdirectories_structure(
        data: dict[str, Any] | None,
    ) -> dict[str, Any]:
        if data is None:
            data = {}
        data.setdefault(METADATA_CONFIG.SUBDIRECTORIES_KEY, {})
        return data


def get_metadata_path(plate_root: str | Path) -> Path:
    """Return the canonical metadata path for one OpenHCS plate root."""

    return METADATA_CONFIG.metadata_path(plate_root)


def component_metadata_field(component: AllComponents) -> str:
    """Derive the persisted collection field for one declared component."""

    if not isinstance(component, AllComponents):
        raise TypeError("Metadata fields require an exact AllComponents member")
    suffix = "es" if component.value.endswith("x") else "s"
    return f"{component.value}{suffix}"


@dataclass(frozen=True)
class OpenHCSMetadataFields:
    """Field identities declared by the OpenHCS metadata contract.

    Shared keys derive from the source-projection serializer declarations so
    the persisted contract has exactly one spelling per field.
    """

    SUBDIRECTORIES: str = METADATA_CONFIG.SUBDIRECTORIES_KEY
    IMAGE_FILES: str = SourceProjectionMetadataSerializer.IMAGE_FILES_FIELD
    AVAILABLE_BACKENDS: str = (
        SourceProjectionMetadataSerializer.AVAILABLE_BACKENDS_FIELD
    )
    SOURCE_METADATA: str = SourceProjectionMetadataSerializer.SOURCE_METADATA_FIELD
    SOURCE_PROJECTION: str = SourceProjectionMetadataSerializer.SOURCE_PROJECTION_FIELD
    SOURCE_DIAGNOSTICS: str = (
        SourceProjectionMetadataSerializer.SOURCE_DIAGNOSTICS_FIELD
    )
    SOURCE_BINDINGS_DECLARATION_IDENTITY: str = "source_bindings_declaration_identity"
    WORKSPACE_MAPPING: str = SourceProjectionMetadataSerializer.WORKSPACE_MAPPING_FIELD
    GRID_DIMENSIONS: str = SourceProjectionMetadataSerializer.GRID_DIMENSIONS_FIELD
    PIXEL_SIZE: str = SourceProjectionMetadataSerializer.PIXEL_SIZE_FIELD
    SOURCE_FILENAME_PARSER_NAME: str = (
        SourceProjectionMetadataSerializer.SOURCE_FILENAME_PARSER_NAME_FIELD
    )
    MICROSCOPE_HANDLER_NAME: str = (
        SourceProjectionMetadataSerializer.MICROSCOPE_HANDLER_NAME_FIELD
    )
    CHANNELS: str = component_metadata_field(AllComponents.CHANNEL)
    WELLS: str = component_metadata_field(AllComponents.WELL)
    SITES: str = component_metadata_field(AllComponents.SITE)
    Z_INDEXES: str = component_metadata_field(AllComponents.Z_INDEX)
    TIMEPOINTS: str = component_metadata_field(AllComponents.TIMEPOINT)
    # Declared legacy collection fields without a current AllComponents member;
    # readers still consume them from persisted plates.
    OBJECTIVES: str = "objectives"
    ACQUISITION_DATETIME: str = "acquisition_datetime"
    PLATE_NAME: str = "plate_name"
    DEFAULT_SUBDIRECTORY: str = "."
    MICROSCOPE_TYPE: str = "openhcsdata"


FIELDS = OpenHCSMetadataFields()


JsonScalar: TypeAlias = str | int | float | bool | None
JsonValue: TypeAlias = JsonScalar | Mapping[str, "JsonValue"] | Sequence["JsonValue"]
OpenHCSMetadataPayload: TypeAlias = Mapping[str, JsonValue]
OpenHCSSubdirectoryPayload: TypeAlias = Mapping[str, JsonValue]


@dataclass(frozen=True, slots=True)
class OpenHCSMetadataSubdirectories:
    """Typed view over OpenHCS metadata subdirectory payloads."""

    metadata: OpenHCSMetadataPayload

    @classmethod
    def from_path(cls, path: Path) -> OpenHCSMetadataSubdirectories:
        """Load the durable projection document for completed-plate reconciliation."""
        if not path.is_file():
            return cls({})
        with path.open(encoding="utf-8") as stream:
            return cls(json.load(stream))

    def items(self) -> tuple[tuple[str, OpenHCSSubdirectoryPayload], ...]:
        subdirectories = self.metadata.get(FIELDS.SUBDIRECTORIES)
        if subdirectories is None:
            return ()
        if not isinstance(subdirectories, Mapping):
            raise RuntimeError("OpenHCS metadata subdirectories must be a mapping.")
        items: list[tuple[str, OpenHCSSubdirectoryPayload]] = []
        for name, subdirectory in subdirectories.items():
            if not isinstance(subdirectory, Mapping):
                raise RuntimeError(
                    f"OpenHCS metadata subdirectory {name!r} must be a mapping."
                )
            items.append((str(name), subdirectory))
        return tuple(items)

    def values(self) -> tuple[OpenHCSSubdirectoryPayload, ...]:
        return tuple(subdirectory for _, subdirectory in self.items())

    def has_workspace_mapping(self) -> bool:
        return any(
            VirtualWorkspaceMapping.from_subdirectory(subdirectory).has_entries
            for subdirectory in self.values()
        )


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceMapping:
    """Validated virtual-workspace mapping entries for one subdirectory."""

    entries: Mapping[str, SourcePixelRef]

    @classmethod
    def from_subdirectory(
        cls,
        subdirectory: OpenHCSSubdirectoryPayload,
    ) -> "VirtualWorkspaceMapping":
        mapping = subdirectory.get(FIELDS.WORKSPACE_MAPPING)
        if mapping is None:
            return cls(MappingProxyType({}))
        if not isinstance(mapping, Mapping):
            raise RuntimeError("virtual_workspace workspace_mapping must be a mapping.")
        return cls(
            MappingProxyType(
                {
                    str(key): SourcePixelRef.from_workspace_mapping(value)
                    for key, value in mapping.items()
                }
            )
        )

    @property
    def has_entries(self) -> bool:
        return bool(self.entries)

    def source_ref_for(self, virtual_path: str) -> SourcePixelRef | None:
        return self.entries.get(virtual_path)

    def require_source_ref(self, virtual_path: str) -> SourcePixelRef:
        source_ref = self.source_ref_for(virtual_path)
        if source_ref is None:
            raise ValueError(
                "OpenHCS workspace metadata is missing a source mapping for "
                f"{virtual_path!r}."
            )
        return source_ref


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceSourceProjectionEntries:
    """Validated nominal source projections keyed by canonical virtual path."""

    entries: Mapping[str, SourceProjection]

    @property
    def is_empty(self) -> bool:
        """Whether this admitted update contains any source projections."""
        return not self.entries

    @property
    def projection_paths(self) -> tuple[tuple[SourceProjection, str], ...]:
        """Expose serialization order directly from the admitted path owner."""
        return tuple((projection, path) for path, projection in self.entries.items())

    @classmethod
    def from_projection_paths(
        cls,
        projection_paths: Sequence[tuple[SourceProjection, str]],
    ) -> "VirtualWorkspaceSourceProjectionEntries":
        """Admit a producer's typed updates in persisted path order."""
        SourceProjectionSet(
            tuple(projection for projection, _path in projection_paths)
        )
        return cls(
            MappingProxyType(
                {path: projection for projection, path in projection_paths}
            )
        )

    @staticmethod
    def _records_by_path(
        subdirectory: OpenHCSSubdirectoryPayload,
    ) -> dict[str, JsonValue]:
        for key in (FIELDS.WORKSPACE_MAPPING, FIELDS.SOURCE_METADATA):
            if not isinstance(subdirectory.get(key, {}), Mapping):
                raise TypeError(f"virtual_workspace {key} must be a mapping.")
        # Transactions have always replaced duplicate paths before admitting
        # records. In particular, a new producer can repair an invalid old record.
        return {
            record["virtual_path"]: record
            for record in subdirectory.get(FIELDS.SOURCE_PROJECTION, [])
        }

    def merged_with_subdirectory(
        self,
        subdirectory: OpenHCSSubdirectoryPayload,
    ) -> "VirtualWorkspaceSourceProjectionEntries":
        """Admit current durable records, retaining the actual typed replacements."""
        records = self._records_by_path(subdirectory)
        return self._admit_retained_records(records)

    def _admit_retained_records(
        self,
        records: Mapping[str, JsonValue],
    ) -> "VirtualWorkspaceSourceProjectionEntries":
        entries: dict[str, SourceProjection] = {}
        for path, record in records.items():
            virtual_path, projection = (
                (path, self.entries[path])
                if path in self.entries else self._projection_record(record)
            )
            if virtual_path in entries:
                raise RuntimeError(
                    "virtual_workspace source_projection contains duplicate path "
                    f"{virtual_path!r}."
                )
            entries[virtual_path] = projection
        for path, projection in self.entries.items():
            if path not in records:
                if path in entries:
                    raise RuntimeError(
                        "virtual_workspace source_projection contains duplicate path "
                        f"{path!r}."
                    )
                entries[path] = projection
        return type(self)(MappingProxyType(entries))

    def merge_into_subdirectory(
        self,
        subdirectory: dict[str, Any],
    ) -> "VirtualWorkspaceSourceProjectionEntries":
        """Merge producer fields without normalizing opaque retained wire fields."""
        records = self._records_by_path(subdirectory)
        admitted = self._admit_retained_records(records)
        fields = SourceProjectionMetadataSerializer.projection_fields(
            self.projection_paths
        )
        for key in (FIELDS.WORKSPACE_MAPPING, FIELDS.SOURCE_METADATA):
            subdirectory[key] = {**subdirectory.get(key, {}), **fields[key]}
        records.update(
            (record["virtual_path"], record)
            for record in fields[FIELDS.SOURCE_PROJECTION]
        )
        subdirectory[FIELDS.SOURCE_PROJECTION] = list(records.values())
        return admitted

    def publish_into_subdirectory(
        self,
        subdirectory: dict[str, Any],
        *,
        saved_image_paths: Sequence[str],
        reconcile_directory: str | None,
    ) -> "VirtualWorkspaceSourceProjectionEntries":
        """Publish current path views while retaining admitted durable records.

        Step snapshots cannot prune another axis's publication. Only completed
        directory reconciliation requires complete inventory and removes deleted
        paths. Retained records keep their original wire annotations; the two
        workspace maps are independently derived normalized views.
        """
        records = self._records_by_path(subdirectory)
        admitted = self._admit_retained_records(records)
        saved_set = frozenset(saved_image_paths)
        missing = saved_set.difference(admitted.entries)
        if missing and reconcile_directory is not None:
            raise MetadataWriteError(
                f"Saved images lack typed produced addresses: {sorted(missing)!r}."
            )
        retained = type(self)(
            MappingProxyType(
                {
                    path: projection
                    for path, projection in admitted.entries.items()
                    if (
                        reconcile_directory is None
                        or path in saved_set
                        or Path(path).parent != Path(reconcile_directory)
                    )
                }
            )
        )
        workspace_fields = SourceProjectionMetadataSerializer.workspace_fields(
            retained.projection_paths
        )
        retained_records = {}
        for path, record in records.items():
            if path in self.entries:
                continue  # Replacements can repair an invalid durable record.
            canonical_path = self._required_text(record, "virtual_path")
            if canonical_path in retained.entries:
                retained_records[canonical_path] = (
                    record if path == canonical_path
                    else {**record, "virtual_path": canonical_path}
                )
        retained_records.update(
            (record["virtual_path"], record)
            for record in SourceProjectionMetadataSerializer.projection_records(
                tuple(
                    (projection, path)
                    for path, projection in self.entries.items()
                    if path in retained.entries
                )
            )
        )
        subdirectory.update(workspace_fields)
        subdirectory[FIELDS.SOURCE_PROJECTION] = [
            retained_records[path] for path in retained.entries
        ]
        return retained

    @classmethod
    def from_subdirectory(
        cls,
        subdirectory: OpenHCSSubdirectoryPayload,
    ) -> "VirtualWorkspaceSourceProjectionEntries":
        records = subdirectory.get("source_projection")
        if records is None:
            return cls(MappingProxyType({}))
        if not isinstance(records, Sequence) or isinstance(records, str):
            raise RuntimeError("virtual_workspace source_projection must be a list.")
        entries: dict[str, SourceProjection] = {}
        for record in records:
            virtual_path, projection = cls._projection_record(record)
            if virtual_path in entries:
                raise RuntimeError(
                    "virtual_workspace source_projection contains duplicate path "
                    f"{virtual_path!r}."
                )
            entries[virtual_path] = projection
        return cls(MappingProxyType(entries))

    @classmethod
    def _projection_record(
        cls,
        record: JsonValue,
    ) -> tuple[str, SourceProjection]:
        if not isinstance(record, Mapping):
            raise RuntimeError(
                "virtual_workspace source_projection records must be mappings."
            )
        virtual_path = cls._required_text(record, "virtual_path")
        try:
            projection_role = SourceProjectionRole(
                cls._required_text(record, "projection_role")
            )
        except ValueError as exc:
            raise RuntimeError(
                "virtual_workspace source_projection has an unknown projection_role."
            ) from exc
        address_value = record.get("address")
        if address_value is None:
            address = None
        elif isinstance(address_value, Mapping):
            address = OpenHCSPlaneAddress.from_values(
                well=cls._required_text(address_value, "well"),
                site=cls._required_text(address_value, "site"),
                channel=cls._required_text(address_value, "channel"),
                z_index=cls._required_text(address_value, "z_index"),
                timepoint=cls._required_text(address_value, "timepoint"),
            )
        else:
            raise RuntimeError(
                "virtual_workspace source_projection address must be a mapping or "
                "null."
            )
        if projection_role is SourceProjectionRole.PRIMARY_PLANE and address is None:
            raise RuntimeError(
                "Primary source projections require a complete plane address."
            )
        ref_value = record.get("ref")
        ref = SourcePixelRef.from_workspace_mapping(ref_value)
        source_metadata = cls._optional_metadata(record, "source_metadata")
        component_labels = cls._optional_component_labels(record)
        source_alias = cls._optional_text(record, "source_alias")
        if projection_role is SourceProjectionRole.PRIMARY_PLANE:
            image_metadata_value = record.get(
                SourcePlaneProjection.image_metadata_wire_field()
            )
            projection: SourceProjection = SourcePlaneProjection(
                address=address,
                ref=ref,
                source_alias=source_alias,
                source_metadata=source_metadata,
                component_labels=component_labels,
                image_metadata=(
                    None
                    if image_metadata_value is None
                    else ImagePayloadMetadata.from_mapping(image_metadata_value)
                ),
            )
        else:
            if source_alias is None:
                raise RuntimeError(
                    "Source-artifact projection records require source_alias."
                )
            artifact_kind = cls._required_text(record, "artifact_kind")
            image_metadata_value = record.get(
                SourcePlaneProjection.image_metadata_wire_field()
            )
            projection = SourceArtifactProjection(
                address=address,
                ref=ref,
                source_alias=source_alias,
                artifact_kind=ArtifactType.coerce(artifact_kind),
                source_metadata=source_metadata,
                component_labels=component_labels,
                image_metadata=(
                    None
                    if image_metadata_value is None
                    else ImagePayloadMetadata.from_mapping(image_metadata_value)
                ),
                execution_scope=cls._optional_execution_scope(record),
            )
        return virtual_path, projection

    @classmethod
    def _optional_execution_scope(
        cls,
        record: Mapping[str, JsonValue],
    ) -> RuntimeExecutionAxisScope | None:
        value = record.get("execution_scope")
        if value is None:
            return None
        if not isinstance(value, Mapping):
            raise RuntimeError(
                "virtual_workspace source_projection execution_scope must be a "
                "mapping."
            )
        fixed_value = value.get("fixed_component_values", ())
        if not isinstance(fixed_value, Sequence) or isinstance(
            fixed_value, (str, bytes)
        ):
            raise RuntimeError(
                "virtual_workspace source_projection execution_scope fixed "
                "components must be a sequence."
            )
        fixed_components: list[tuple[str, str]] = []
        for item in fixed_value:
            if (
                not isinstance(item, Sequence)
                or isinstance(item, (str, bytes))
                or len(item) != 2
            ):
                raise RuntimeError(
                    "virtual_workspace source_projection execution_scope fixed "
                    "components must be two-item sequences."
                )
            fixed_components.append((str(item[0]), str(item[1])))
        component = value.get("component")
        scope_value = value.get("value")
        return RuntimeExecutionAxisScope.from_raw(
            cls._required_text(value, "axis_id"),
            component=None if component is None else str(component),
            value=None if scope_value is None else str(scope_value),
            fixed_component_values=tuple(fixed_components),
        )

    @staticmethod
    def _required_text(record: Mapping[str, JsonValue], field: str) -> str:
        value = record.get(field)
        if not isinstance(value, (str, int)) or isinstance(value, bool):
            raise RuntimeError(
                f"virtual_workspace source_projection field {field!r} must be text."
            )
        text = str(value).strip()
        if not text:
            raise RuntimeError(
                f"virtual_workspace source_projection field {field!r} cannot be empty."
            )
        return text

    @classmethod
    def _optional_text(
        cls,
        record: Mapping[str, JsonValue],
        field: str,
    ) -> str | None:
        if field not in record:
            return None
        return cls._required_text(record, field)

    @staticmethod
    def _optional_metadata(
        record: Mapping[str, JsonValue],
        field: str,
    ) -> SourceMetadataMapping:
        if field not in record:
            return MappingProxyType({})
        return VirtualWorkspaceSourceMetadataEntries.normalize_metadata_fields(
            record[field]
        )

    @classmethod
    def _optional_component_labels(
        cls,
        record: Mapping[str, JsonValue],
    ) -> Mapping[str, str | None]:
        labels = record.get("component_labels")
        if labels is None:
            return MappingProxyType({})
        if not isinstance(labels, Mapping):
            raise RuntimeError(
                "virtual_workspace source_projection component_labels must be a mapping."
            )
        normalized: dict[str, str | None] = {}
        for key, value in labels.items():
            if value is not None and not isinstance(value, str):
                raise RuntimeError(
                    "virtual_workspace source_projection component label values "
                    "must be text or null."
                )
            normalized[str(key)] = value
        return MappingProxyType(normalized)


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceSourceMetadataEntries:
    """Validated source metadata entries for one virtual-workspace subdirectory."""

    entries: Mapping[str, SourceMetadataMapping]

    @classmethod
    def from_subdirectory(
        cls,
        subdirectory: OpenHCSSubdirectoryPayload,
    ) -> "VirtualWorkspaceSourceMetadataEntries":
        source_metadata = subdirectory.get(FIELDS.SOURCE_METADATA)
        if source_metadata is None:
            return cls(MappingProxyType({}))
        if not isinstance(source_metadata, Mapping):
            raise RuntimeError(
                "virtual_workspace source metadata must be a path-keyed mapping."
            )
        return cls(
            MappingProxyType(
                {
                    str(virtual_path): cls.normalize_metadata_fields(metadata_fields)
                    for virtual_path, metadata_fields in source_metadata.items()
                }
            )
        )

    @staticmethod
    def normalize_metadata_fields(metadata_fields: JsonValue) -> SourceMetadataMapping:
        if not isinstance(metadata_fields, Mapping):
            raise RuntimeError(
                "virtual_workspace source metadata values must be mappings."
            )
        return DurableSourceMetadata.from_mapping(metadata_fields)

    def metadata_for(self, virtual_path: str) -> SourceMetadataMapping:
        metadata = self.entries.get(virtual_path)
        if metadata is None:
            return MappingProxyType({})
        return metadata


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceChannelLabels:
    """Validated channel labels for one virtual-workspace subdirectory."""

    entries: Mapping[str, str]

    @classmethod
    def from_subdirectory(
        cls,
        subdirectory: OpenHCSSubdirectoryPayload,
    ) -> "VirtualWorkspaceChannelLabels":
        channels = subdirectory.get(FIELDS.CHANNELS)
        if channels is None:
            return cls(MappingProxyType({}))
        if not isinstance(channels, Mapping):
            raise RuntimeError("virtual_workspace channels must be a mapping.")
        return cls(
            MappingProxyType({str(key): str(value) for key, value in channels.items()})
        )

    def label_for(self, channel_value: SourceMetadataScalar) -> str | None:
        return self.entries.get(str(channel_value))
