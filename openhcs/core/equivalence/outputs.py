"""Runtime output snapshot construction for equivalence checks."""

from __future__ import annotations
from openhcs.core.runtime_measurements import MeasurementRowAxisField

from abc import ABC, abstractmethod
from dataclasses import dataclass, replace
from os.path import commonprefix
from pathlib import Path
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.equivalence.images import RuntimeImageSnapshot
from openhcs.core.equivalence.policy import normalize_runtime_identifier
from openhcs.core.equivalence.policy import (
    DEFAULT_RUNTIME_MEASUREMENT_DIALECT,
    RuntimeMeasurementDialect,
)
from openhcs.core.equivalence.tables import RuntimeTableSnapshot
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.runtime_execution_validation import (
    RuntimeArtifactExecutionObservation,
)
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.constants.constants import AllComponents
from openhcs.core.source_bindings import SourceProjectionRole
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_projection import SourceProjectionSet
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.virtual_workspace_metadata import (
    METADATA_CONFIG,
    OpenHCSMetadataSubdirectories,
)


@dataclass(frozen=True, slots=True)
class RuntimeOutputSnapshot:
    """Semantic snapshot of runtime file outputs."""

    tables: tuple[RuntimeTableSnapshot, ...] = ()
    images: tuple[RuntimeImageSnapshot, ...] = ()

    @classmethod
    def from_export_observation(
        cls,
        observation: RuntimeExportObservation,
        *,
        source_workspaces: tuple[Path, ...] = (),
        image_set_policy: SourceImageSetIdentityPolicy = SourceImageSetIdentityPolicy(),
        execution_axis_id: str | None = None,
        measurement_dialect: RuntimeMeasurementDialect = DEFAULT_RUNTIME_MEASUREMENT_DIALECT,
    ) -> "RuntimeOutputSnapshot":
        """Build a semantic output snapshot from observed runtime exports."""
        tables = RuntimeTableNamespaceAdapter.normalize(
            tuple(
                RuntimeTableSnapshot.from_csv(path)
                for path in observation.table_outputs
            )
        )
        if execution_axis_id is not None:
            for path in observation.table_outputs:
                if path not in observation.outputs.image_numbers_by_export_path:
                    continue
                numbers = observation.outputs.image_numbers_by_export_path[path][
                    execution_axis_id
                ]
                if tuple(sorted(numbers)) != tuple(
                    range(min(numbers), max(numbers) + 1)
                ):
                    raise ValueError(
                        "Comparison requires an exporter-admitted contiguous local image domain."
                    )
            tables = tuple(
                (
                    table.for_image_numbers(
                        observation.outputs.image_numbers_by_export_path[table.path][
                            execution_axis_id
                        ],
                        dialect=measurement_dialect,
                        image_number_domain=tuple(
                            number
                            for numbers in observation.outputs.image_numbers_by_export_path[
                                table.path
                            ].values()
                            for number in numbers
                        ),
                    )
                    if table.path in observation.outputs.image_numbers_by_export_path
                    else table
                )
                for table in tables
            )
        return cls(
            tables=tables,
            images=cls.image_snapshots(
                observation.image_outputs,
                source_workspaces=source_workspaces,
                image_set_policy=image_set_policy,
            ),
        )

    @classmethod
    def image_snapshots(
        cls,
        paths: tuple[Path, ...],
        *,
        source_workspaces: tuple[Path, ...],
        image_set_policy: SourceImageSetIdentityPolicy,
    ) -> tuple[RuntimeImageSnapshot, ...]:
        """Compare declared Z image sets while retaining every physical export."""
        if (
            not paths
            or not source_workspaces
            or image_set_policy.is_identity_component(AllComponents.Z_INDEX)
        ):
            return tuple(RuntimeImageSnapshot.from_image_file(path) for path in paths)
        expected_paths = frozenset(path.absolute() for path in paths)
        images = []
        for root in dict.fromkeys(Path(root).absolute() for root in source_workspaces):
            metadata = OpenHCSMetadataSubdirectories.from_path(
                METADATA_CONFIG.metadata_path(root)
            ).metadata
            workspace = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
                root, metadata
            )
            projections = tuple(
                projection
                for virtual_path in workspace.relative_virtual_paths()
                for projection in (
                    workspace.source_projections_by_virtual_path[virtual_path],
                )
                if projection.projection_role is SourceProjectionRole.SOURCE_ARTIFACT
                and (root / projection.ref.backend_address).absolute() in expected_paths
            )
            if not projections:
                continue
            whole_images, plane_groups = SourceProjectionSet(
                projections
            ).image_export_groups(image_set_policy)
            for projection in whole_images:
                if projection.ref.source_axis_indices:
                    raise ValueError(
                        "Whole image exports cannot select hidden source axes."
                    )
                images.append(
                    RuntimeImageSnapshot.from_image_file(
                        (root / projection.ref.backend_address).absolute()
                    )
                )
            for group in plane_groups:
                images.append(
                    RuntimeImageSnapshot.from_source_planes(group, workspace_root=root)
                )
        snapshot = cls(images=tuple(images))
        snapshot.require_image_file_coverage(expected_paths)
        return snapshot.images

    def require_image_file_coverage(self, paths: frozenset[Path]) -> None:
        """Require each physical image export to own exactly one compared image."""
        covered = tuple(
            path.absolute() for image in self.images for path in image.physical_paths
        )
        if len(covered) != len(set(covered)) or frozenset(covered) != frozenset(
            path.absolute() for path in paths
        ):
            raise ValueError(
                "Compared images must cover every physical image file exactly once."
            )

    @classmethod
    def from_artifact_execution_observation(
        cls,
        observation: RuntimeArtifactExecutionObservation,
        *,
        source_workspaces: tuple[Path, ...] = (),
    ) -> "RuntimeOutputSnapshot":
        """Build a snapshot from files owned by observed runtime artifacts."""
        return cls.from_export_observation(
            observation.exports.with_runtime_artifact_tables(
                observation.records_by_axis
            ),
            source_workspaces=source_workspaces,
            image_set_policy=observation.source_image_set_identity_policy,
        )

    @classmethod
    def from_output_root(
        cls,
        output_root: Path,
        *,
        image_set_policy: SourceImageSetIdentityPolicy = SourceImageSetIdentityPolicy(),
    ) -> "RuntimeOutputSnapshot":
        """Build a semantic output snapshot from an output directory."""
        root = Path(output_root)
        if not root.exists():
            raise FileNotFoundError(f"Runtime output root does not exist: {root}")
        return cls.from_export_observation(
            RuntimeExportObservation.from_output_root(root),
            source_workspaces=(root,),
            image_set_policy=image_set_policy,
        )


def table_paths(output_root: Path) -> tuple[Path, ...]:
    """Return non-empty CSV output paths under an output root."""
    root = Path(output_root)
    return tuple(
        path
        for path in sorted(root.rglob("*.csv"))
        if path.is_file() and path.stat().st_size > 0
    )


class RuntimeTableNamespaceAdapter(ABC, metaclass=AutoRegisterMeta):
    """Normalize file-export table namespace without changing table contents."""

    __registry_key__ = "namespace_adapter"
    __registry__: ClassVar[dict[str, type["RuntimeTableNamespaceAdapter"]]] = {}
    namespace_adapter: ClassVar[str | None] = None

    @classmethod
    def normalize(
        cls,
        tables: tuple[RuntimeTableSnapshot, ...],
    ) -> tuple[RuntimeTableSnapshot, ...]:
        adapters = tuple(
            adapter_type()
            for adapter_type in cls.__registry__.values()
            if adapter_type().supports(tables)
        )
        if not adapters:
            return tables
        if len(adapters) > 1:
            names = tuple(type(adapter).__name__ for adapter in adapters)
            raise ValueError(
                "Ambiguous runtime table namespace adapters for exported tables: "
                f"{names!r}."
            )
        return adapters[0].normalize_tables(tables)

    @abstractmethod
    def supports(self, tables: tuple[RuntimeTableSnapshot, ...]) -> bool:
        """Return whether this adapter owns the table namespace."""

    @abstractmethod
    def normalize_tables(
        self,
        tables: tuple[RuntimeTableSnapshot, ...],
    ) -> tuple[RuntimeTableSnapshot, ...]:
        """Return semantic table snapshots with normalized path identities."""


class CommonStemRuntimeTableNamespaceAdapter(RuntimeTableNamespaceAdapter):
    """Remove an exporter-wide filename namespace shared by all table outputs."""

    namespace_adapter = "common_stem"

    def supports(self, tables: tuple[RuntimeTableSnapshot, ...]) -> bool:
        return _common_table_namespace_prefix(tables) is not None

    def normalize_tables(
        self,
        tables: tuple[RuntimeTableSnapshot, ...],
    ) -> tuple[RuntimeTableSnapshot, ...]:
        prefix = _common_table_namespace_prefix(tables)
        if prefix is None:
            return tables
        return tuple(
            replace(
                table,
                path=table.path.with_name(
                    f"{table.path.stem[len(prefix):]}{table.path.suffix}"
                ),
            )
            for table in tables
        )


def _common_table_namespace_prefix(
    tables: tuple[RuntimeTableSnapshot, ...],
) -> str | None:
    if len(tables) < 2:
        return None
    stems = tuple(table.path.stem for table in tables)
    shared = commonprefix(stems)
    if "_" not in shared:
        return None
    prefix = shared[: shared.rfind("_") + 1]
    suffixes = tuple(stem[len(prefix) :] for stem in stems)
    if not prefix or any(not suffix for suffix in suffixes):
        return None
    if all(_table_has_object_identity(table) for table in tables):
        return None
    return prefix


def _table_has_object_identity(table: RuntimeTableSnapshot) -> bool:
    normalized_header = {_normalize_table_header_field(field) for field in table.header}
    return bool(
        normalized_header & set(MeasurementRowAxisField.object_id_field_names())
    )


def _normalize_table_header_field(field: str) -> str:
    return normalize_runtime_identifier(field)


def image_paths(output_root: Path) -> tuple[Path, ...]:
    """Return image output paths under an output root."""
    root = Path(output_root)
    return tuple(
        path
        for path in sorted(root.rglob("*"))
        if path.is_file() and _is_image_path(path)
    )


def _is_image_path(path: Path) -> bool:
    return ImageFileFormat.is_image_path(path)
