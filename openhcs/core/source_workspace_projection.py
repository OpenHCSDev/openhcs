"""Project OpenHCS virtual-workspace metadata for runtime source binding."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, TypeVar

from openhcs.core.source_path_identity import source_path_identity, source_path_join
from openhcs.constants import Backend
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.source_bindings import (
    SOURCE_BINDING_ALIAS_METADATA_FIELD,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceProjectionRole,
)
from openhcs.core.source_metadata import (
    SourceMetadataFields,
    SourceMetadataMapping,
)
from openhcs.core.source_matching import (
    source_component_metadata_values,
    source_metadata_value,
    source_metadata_values_equal,
)
from openhcs.core.source_path_identity import source_path_identity_key
from openhcs.core.source_projection import SourceProjection, SourceProjectionMetadataSerializer
from openhcs.core.virtual_workspace_metadata import (
    OpenHCSMetadataPayload,
    OpenHCSMetadataSubdirectories,
    OpenHCSSubdirectoryPayload,
    VirtualWorkspaceMapping,
    VirtualWorkspaceSourceProjectionEntries,
    VirtualWorkspaceSourceMetadataEntries,
)
from polystore.virtual_workspace import SourcePixelRef
from openhcs.core.axes import AxisFamily

if TYPE_CHECKING:
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.microscopes.microscope_interfaces import MetadataHandler
    from openhcs.core.vfs_protocol import FileManagerLike
    from polystore.filemanager import FileManager
    from openhcs.microscopes.openhcs import OpenHCSMetadataHandler


LookupValueT = TypeVar("LookupValueT")


@dataclass(frozen=True, slots=True)
class VirtualWorkspacePathLookup:
    """Virtual workspace path identity for source path and metadata lookup."""

    virtual_path: str
    full_virtual_path: str

    @classmethod
    def from_paths(
        cls,
        virtual_path: str,
        full_virtual_path: str,
    ) -> "VirtualWorkspacePathLookup":
        return cls(str(virtual_path), str(full_virtual_path))

    def candidates(self) -> tuple[str, str]:
        return (self.virtual_path, self.full_virtual_path)


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceSourceProjection:
    """Source-binding projection derived from OpenHCS virtual-workspace metadata."""

    source_refs_by_virtual_path: Mapping[str, SourcePixelRef]
    source_metadata_by_path: Mapping[str, SourceMetadataMapping]
    workspace_root: str | None = None
    source_projections_by_virtual_path: Mapping[str, SourceProjection] = field(
        default_factory=lambda: MappingProxyType({})
    )
    _pipeline_start_files_by_axis: dict[str | None, tuple[str, ...]] = field(
        default_factory=dict,
        init=False,
        repr=False,
        compare=False,
    )

    @classmethod
    def empty(
        cls, plate_path: Path | None = None
    ) -> "VirtualWorkspaceSourceProjection":
        workspace_root = None
        if plate_path is not None:
            workspace_root = str(plate_path)
        return cls(
            source_refs_by_virtual_path=MappingProxyType({}),
            source_metadata_by_path=MappingProxyType({}),
            source_projections_by_virtual_path=MappingProxyType({}),
            workspace_root=workspace_root,
        )

    @classmethod
    def from_openhcs_metadata(
        cls,
        plate_path: Path,
        metadata: OpenHCSMetadataPayload,
    ) -> "VirtualWorkspaceSourceProjection":
        builder = VirtualWorkspaceSourceProjectionBuilder(plate_path)
        for subdirectory in OpenHCSMetadataSubdirectories(metadata).values():
            builder.ingest_subdirectory(subdirectory)
        return builder.projection()

    @classmethod
    def from_openhcs_metadata_if_available(
        cls,
        plate_path: Path,
        metadata: OpenHCSMetadataPayload,
    ) -> "VirtualWorkspaceSourceProjection | None":
        subdirectories = OpenHCSMetadataSubdirectories(metadata)
        if not subdirectories.has_workspace_mapping():
            return None
        builder = VirtualWorkspaceSourceProjectionBuilder(plate_path)
        for subdirectory in subdirectories.values():
            builder.ingest_subdirectory(subdirectory)
        return builder.projection()

    @classmethod
    def openhcs_metadata_has_workspace_mapping(
        cls,
        metadata: OpenHCSMetadataPayload,
    ) -> bool:
        return OpenHCSMetadataSubdirectories(metadata).has_workspace_mapping()

    def first_virtual_path_value(
        self,
        mapping: Mapping[str, LookupValueT],
        lookup: VirtualWorkspacePathLookup,
    ) -> LookupValueT | None:
        """Return the first mapped value for a virtual/full path pair."""
        for key in lookup.candidates():
            value = mapping.get(key)
            if value is not None:
                return value
        return None

    def source_path_for(
        self,
        lookup: VirtualWorkspacePathLookup,
    ) -> str:
        """Return the opaque backend address represented by a virtual path."""
        source_ref = self.source_ref_for(lookup)
        if source_ref is None:
            return lookup.full_virtual_path
        return source_ref.backend_address

    def source_ref_for(
        self,
        lookup: VirtualWorkspacePathLookup,
    ) -> SourcePixelRef | None:
        """Return the complete backend-owned source reference for a virtual path."""

        return self.first_virtual_path_value(
            self.source_refs_by_virtual_path,
            lookup,
        )

    def logical_path_for(self, lookup: VirtualWorkspacePathLookup) -> str:
        """Use the declared workspace identity independently of I/O spelling."""

        projection = self.require_source_projection_for(lookup)
        for path in lookup.candidates():
            if self.source_projections_by_virtual_path.get(path) is not projection:
                continue
            declared_path = source_path_identity(path)
            if self.workspace_root is not None and declared_path.is_relative_to(
                self.workspace_root
            ):
                relative_path = str(declared_path.relative_to(self.workspace_root))
                if (
                    self.source_projections_by_virtual_path.get(relative_path)
                    is projection
                ):
                    return relative_path
            return path
        raise RuntimeError("Admitted workspace projection has no declared path.")

    def resolved_source_path_for(
        self,
        lookup: VirtualWorkspacePathLookup,
        filemanager: "FileManagerLike",
    ) -> str:
        """Resolve one mapped source through its declared storage backend."""

        source_ref = self.source_ref_for(lookup)
        if source_ref is None:
            return lookup.full_virtual_path
        if self.workspace_root is None:
            raise ValueError(
                "Virtual workspace source resolution requires a workspace root."
            )
        return str(
            filemanager.source_path(
                source_ref.backend_address,
                source_ref.backend,
                base_path=self.workspace_root,
            )
        )

    def source_projection_for(
        self,
        lookup: VirtualWorkspacePathLookup,
    ) -> SourceProjection | None:
        """Return the nominal source projection represented by a virtual path."""
        return self.first_virtual_path_value(
            self.source_projections_by_virtual_path,
            lookup,
        )

    def require_source_projection_for(
        self,
        lookup: VirtualWorkspacePathLookup,
    ) -> SourceProjection:
        """Return the nominal projection or fail at the workspace boundary."""
        projection = self.source_projection_for(lookup)
        if projection is None:
            raise ValueError(
                "Virtual workspace source path has no declared source_projection: "
                f"{lookup.virtual_path!r}."
            )
        return projection

    def payload_composition_mode(
        self,
        lookups: tuple[VirtualWorkspacePathLookup, ...],
    ) -> ImagePayloadMetadataCompositionMode:
        """Return the leading-axis topology declared by workspace projections."""
        projections = tuple(
            self.require_source_projection_for(lookup) for lookup in lookups
        )
        source_aliases = tuple(
            projection.payload_composition_alias
            for projection in projections
            if projection.payload_composition_alias is not None
        )
        if (
            len(source_aliases) == len(projections)
            and len(source_aliases) > 1
            and len(set(source_aliases)) == len(source_aliases)
        ):
            return ImagePayloadMetadataCompositionMode.BUNDLE
        return ImagePayloadMetadataCompositionMode.STACK

    def project_payload(
        self,
        lookup: VirtualWorkspacePathLookup,
        payload: RuntimeArrayData,
    ) -> RuntimeArrayData:
        """Carry one nominal source projection into runtime payload provenance."""
        projection = self.require_source_projection_for(lookup)
        source_metadata = self.source_metadata_for(lookup)
        return VirtualWorkspaceImagePayloadProjection(
            source_metadata=source_metadata,
            source_alias=projection.source_alias,
            persisted_metadata=projection.image_metadata,
        ).apply(payload)

    def project_unbound_payload(
        self,
        lookup: VirtualWorkspacePathLookup,
        payload: RuntimeArrayData,
    ) -> RuntimeArrayData:
        """Carry workspace source metadata without requiring a step binding."""

        source_metadata = self.source_metadata_for(lookup)
        projection = self.source_projection_for(lookup)
        source_alias = (
            None
            if source_metadata is None
            else source_metadata_value(
                source_metadata,
                SOURCE_BINDING_ALIAS_METADATA_FIELD,
            )
        )
        return VirtualWorkspaceImagePayloadProjection(
            source_metadata=source_metadata,
            source_alias=source_alias,
            persisted_metadata=(
                None if projection is None else projection.image_metadata
            ),
        ).apply(payload)

    def source_metadata_for(
        self,
        lookup: VirtualWorkspacePathLookup,
    ) -> SourceMetadataMapping | None:
        """Return source metadata represented by a virtual workspace path."""
        metadata = self.first_virtual_path_value(
            self.source_metadata_by_path,
            lookup,
        )
        if metadata is not None:
            return metadata
        source_path = self.source_path_for(lookup)
        metadata = self.source_metadata_by_path.get(source_path)
        if metadata is not None:
            return metadata
        for virtual_path in self.virtual_paths_for_source_path(lookup):
            metadata = self.source_metadata_by_path.get(virtual_path)
            if metadata is not None:
                return metadata
            metadata = self.source_metadata_by_path.get(
                self._loadable_virtual_path(virtual_path)
            )
            if metadata is not None:
                return metadata
            metadata = source_schema_filename_metadata(virtual_path)
            if metadata is not None:
                return metadata
        for key in lookup.candidates():
            metadata = source_schema_filename_metadata(key)
            if metadata is not None:
                return metadata
        return None

    def virtual_paths_for_source_path(
        self,
        lookup: VirtualWorkspacePathLookup,
    ) -> tuple[str, ...]:
        """Return virtual paths whose physical source path matches the lookup."""

        source_path_identities = frozenset(
            source_path_identity_key(candidate) for candidate in lookup.candidates()
        )
        return tuple(
            virtual_path
            for virtual_path, source_ref in self.source_refs_by_virtual_path.items()
            if not source_path_identity(virtual_path).is_absolute()
            and source_path_identity_key(source_ref.backend_address)
            in source_path_identities
        )

    def pipeline_start_files(self, *, axis_id: str | None = None) -> tuple[str, ...]:
        """Return loadable virtual source paths for one runtime source universe."""
        cached = self._pipeline_start_files_by_axis.get(axis_id)
        if cached is not None:
            return cached

        relative_virtual_paths = self.relative_virtual_paths()
        selected = tuple(
            virtual_path
            for virtual_path in relative_virtual_paths
            if self._path_belongs_to_axis(virtual_path, axis_id)
        )
        result = tuple(
            dict.fromkeys(
                self._loadable_virtual_path(virtual_path) for virtual_path in selected
            )
        )
        self._pipeline_start_files_by_axis[axis_id] = result
        return result

    def files_for_projection_role(
        self,
        projection_role: SourceProjectionRole,
        *,
        axis_id: str | None = None,
    ) -> tuple[str, ...]:
        """Return source files belonging to one exact declared projection role."""

        role = (
            projection_role
            if isinstance(projection_role, SourceProjectionRole)
            else SourceProjectionRole(projection_role)
        )
        return tuple(
            self._loadable_virtual_path(virtual_path)
            for virtual_path in self.relative_virtual_paths()
            if self._path_belongs_to_axis(virtual_path, axis_id)
            and self.require_source_projection_for(
                VirtualWorkspacePathLookup.from_paths(
                    virtual_path,
                    self._loadable_virtual_path(virtual_path),
                )
            ).projection_role
            is role
        )

    def source_occurrences_for_binding(
        self,
        binding: NamedSourceBinding,
        *,
        axis_id: str,
    ) -> tuple[tuple[str, SourceProjection], ...]:
        """Select exact declared occurrences without merging physical resources."""

        occurrences = []
        for path in self.files_for_projection_role(
            binding.projection_role, axis_id=axis_id
        ):
            projection = self.require_source_projection_for(
                VirtualWorkspacePathLookup.from_paths(path, path)
            )
            if projection.matches_binding(
                binding
            ) and projection.belongs_to_execution_axis(axis_id):
                occurrences.append((path, projection))
        return tuple(occurrences)

    def load_binding_payloads(
        self,
        paths: Sequence[str],
        *,
        binding: NamedSourceBinding,
        filemanager: FileManagerLike,
    ) -> tuple[RuntimeArrayData, ...]:
        """Load exact selected occurrences with their declared pixel semantics."""
        from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
        from openhcs.core.source_image_provenance import SourceImageIdentity

        payloads = filemanager.load_batch(list(paths), Backend.VIRTUAL_WORKSPACE.value)
        if len(payloads) != len(paths):
            raise ValueError(
                f"Source-bound artifact {binding.input_spec().ref()!r} loaded "
                f"{len(payloads)} payloads for {len(paths)} workspace members."
            )
        projected_payloads = []
        for path, payload in zip(paths, payloads, strict=True):
            lookup = VirtualWorkspacePathLookup.from_paths(path, path)
            projection = self.require_source_projection_for(lookup)
            if not projection.matches_binding(binding):
                raise ValueError(
                    f"Workspace projection for {path!r} does not match compiled "
                    f"source artifact {binding.input_spec().ref()!r}."
                )
            projected_payloads.append(binding.apply_loaded_payload(
                self.project_payload(lookup, payload),
                ImagePayloadSourceMetadataContext(
                    SourceImageIdentity(
                        self.logical_path_for(lookup), self.source_metadata_for(lookup),
                    ),
                    projection.ref.backend,
                    filemanager,
                    projection.ref.backend_address,
                ),
            ))
        return tuple(projected_payloads)

    def validate_runtime_metadata_projection(
        self,
        *,
        axis_id: str | None = None,
    ) -> None:
        """Fail if explicit source metadata cannot survive runtime path spelling."""

        failures: list[str] = []
        for virtual_path in self.relative_virtual_paths():
            if not self._path_belongs_to_axis(virtual_path, axis_id):
                continue
            loadable_path = self._loadable_virtual_path(virtual_path)
            expected_metadata = self.explicit_metadata_for_virtual_path(
                virtual_path,
                loadable_path,
            )
            if not expected_metadata:
                continue
            runtime_metadata = self.source_metadata_for(
                VirtualWorkspacePathLookup.from_paths(
                    loadable_path,
                    loadable_path,
                )
            )
            if runtime_metadata is None:
                failures.append(f"{loadable_path}: missing source metadata")
                continue
            mismatched = tuple(
                key
                for key, expected_value in expected_metadata.items()
                if runtime_metadata.get(key) != expected_value
            )
            if mismatched:
                failures.append(
                    f"{loadable_path}: metadata mismatch for {mismatched!r}"
                )

        if failures:
            preview = "; ".join(failures[:10])
            if len(failures) > 10:
                preview = f"{preview}; ... ({len(failures)} paths total)"
            raise ValueError(
                "Source workspace projection cannot preserve explicit source "
                f"metadata for runtime load paths: {preview}."
            )

    def explicit_metadata_for_virtual_path(
        self,
        virtual_path: str,
        loadable_path: str,
    ) -> SourceMetadataMapping | None:
        """Return metadata explicitly declared for one virtual path spelling."""

        metadata = self.source_metadata_by_path.get(virtual_path)
        if metadata is not None:
            return metadata
        return self.source_metadata_by_path.get(loadable_path)

    def relative_virtual_paths(self) -> tuple[str, ...]:
        """Return canonical relative virtual paths for source projection traversal."""

        relative_virtual_paths = tuple(
            virtual_path
            for virtual_path in self.source_refs_by_virtual_path
            if not source_path_identity(virtual_path).is_absolute()
        )
        if relative_virtual_paths:
            return relative_virtual_paths
        return tuple(self.source_refs_by_virtual_path)

    def component_values(self, component) -> tuple[str, ...]:
        """Derive the execution component domain from admitted source metadata."""
        return tuple(dict.fromkeys(
            value
            for path in self.relative_virtual_paths()
            for value in source_component_metadata_values(
                self.source_metadata_for(VirtualWorkspacePathLookup.from_paths(
                    path, self._loadable_virtual_path(path)
                )) or {}, component,
            )
        ))

    def filtered_by_axis(
        self,
        *,
        axis_id: str | None,
    ) -> "VirtualWorkspaceSourceProjection":
        """Return a projection view restricted to one multiprocessing axis."""
        if axis_id is None:
            return self

        return self.partition_by_axes((axis_id,))[axis_id]

    def partition_by_axes(
        self,
        axis_ids: Sequence[str],
    ) -> Mapping[str, "VirtualWorkspaceSourceProjection"]:
        """Admit all requested axis views in one traversal of this source epoch."""

        source_refs = {axis_id: {} for axis_id in axis_ids}
        source_metadata = {axis_id: {} for axis_id in source_refs}
        source_projections = {axis_id: {} for axis_id in source_refs}
        for virtual_path, source_ref in self.source_refs_by_virtual_path.items():
            metadata = self.source_metadata_for(
                VirtualWorkspacePathLookup.from_paths(
                    virtual_path, self._loadable_virtual_path(virtual_path)
                )
            )
            values = (
                () if metadata is None
                else source_component_metadata_values(
                    metadata, AxisFamily.active().partition_axis()
                )
            )
            selected_axes = (
                tuple(dict.fromkeys(value for value in values if value in source_refs))
                if values else tuple(source_refs)
            )
            if not selected_axes:
                continue
            projection = self.source_projections_by_virtual_path.get(virtual_path)
            metadata_records = tuple(
                (path, self.source_metadata_by_path[path])
                for path in (
                    virtual_path,
                    self._loadable_virtual_path(virtual_path),
                    source_ref.backend_address,
                )
                if path in self.source_metadata_by_path
            )
            for axis_id in selected_axes:
                source_refs[axis_id][virtual_path] = source_ref
                if projection is not None:
                    source_projections[axis_id][virtual_path] = projection
                source_metadata[axis_id].update(metadata_records)

        return MappingProxyType({
            axis_id: VirtualWorkspaceSourceProjection(
                source_refs_by_virtual_path=MappingProxyType(refs),
                source_metadata_by_path=MappingProxyType(source_metadata[axis_id]),
                source_projections_by_virtual_path=MappingProxyType(
                    source_projections[axis_id]
                ),
                workspace_root=self.workspace_root,
            )
            for axis_id, refs in source_refs.items()
        })

    def _path_belongs_to_axis(
        self,
        virtual_path: str,
        axis_id: str | None,
    ) -> bool:
        if axis_id is None:
            return True
        metadata = self.source_metadata_for(
            VirtualWorkspacePathLookup.from_paths(
                virtual_path,
                self._loadable_virtual_path(virtual_path),
            )
        )
        if metadata is None:
            return True

        values = source_component_metadata_values(
            metadata, AxisFamily.active().partition_axis()
        )
        if not values:
            return True
        return any(source_metadata_values_equal(value, axis_id) for value in values)

    def _loadable_virtual_path(self, virtual_path: str) -> str:
        if source_path_identity(virtual_path).is_absolute():
            return virtual_path
        if self.workspace_root is not None:
            return source_path_join(str(self.workspace_root), virtual_path)
        return virtual_path


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceImagePayloadProjection:
    """Join persisted semantics to loaded native headers for one workspace image."""

    source_metadata: SourceMetadataMapping | None = None
    source_alias: str | None = None
    persisted_metadata: ImagePayloadMetadata | None = None

    def metadata(self, loaded: ImagePayloadMetadata) -> ImagePayloadMetadata:
        """Preserve semantic omissions, but not an empty header's lost identity."""
        if self.persisted_metadata is None:
            return loaded
        metadata = self.persisted_metadata.with_source_spatial_context_from(
            loaded
        ).with_missing_intensity_from(loaded)
        provenance = metadata.source_provenance
        if not (
            provenance.source_identity.addressable
            or provenance.source_image_provenance_planes.has_values
        ):
            metadata = metadata.with_source_context_from(loaded)
        return metadata

    def apply(self, payload: RuntimeArrayData) -> RuntimeArrayData:
        """Apply declared component metadata and source aliases to one payload."""
        source_metadata = self.source_metadata
        if source_metadata is not None:
            source_metadata = SourceMetadataFields.with_fields(
                source_metadata, {}, without=(SOURCE_BINDING_ALIAS_METADATA_FIELD,)
            )
        current_metadata = image_payload_metadata(payload)
        metadata = self.metadata(current_metadata)
        metadata = metadata.replace_fields(
            source_spatial_domain=metadata.source_spatial_domain.with_native_image_context(
                current_metadata.source_spatial_domain,
                image_shape_yx=current_metadata.spatial_shape_yx(
                    image_payload_data(payload)
                ),
            )
        )
        if source_metadata is not None and self.persisted_metadata is None:
            metadata = metadata.with_source_component_metadata(source_metadata)
        if self.source_alias is not None:
            metadata = metadata.with_source_provenance(
                metadata.source_provenance.with_source_image_names((self.source_alias,))
            )
        return metadata.payload_with(
            image_payload_data(payload),
            image_payload_mask(payload),
        )


@lru_cache(maxsize=8192)
def source_schema_filename_metadata(path: str) -> SourceMetadataMapping | None:
    """Return component metadata encoded in a normalized virtual source filename."""

    from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

    parsed = SourceSchemaFilenameParser().parse_filename(path)
    if parsed is None:
        return None
    return parsed.wire_mapping()


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceSourceProjectionCacheEntry:
    """One projection bound to the exact metadata document that produced it."""

    metadata: OpenHCSMetadataPayload
    projection: VirtualWorkspaceSourceProjection | None
    axis_filtered_projections: dict[str, VirtualWorkspaceSourceProjection] = field(
        default_factory=dict, compare=False, repr=False,
    )
    source_admitted_entries: dict[
        tuple[SourceFilterClause, ...], VirtualWorkspaceSourceProjectionCacheEntry,
    ] = field(default_factory=dict, compare=False, repr=False)

    def admitted_for(
        self, source_bindings: SourceBindingsConfig | None,
    ) -> VirtualWorkspaceSourceProjectionCacheEntry:
        """Bind prepared-source admission to its document and declarations."""
        if self.projection is None or source_bindings is None:
            return self
        declarations = source_bindings.source_filter_declarations
        if not declarations:
            return self
        admitted = self.source_admitted_entries.get(declarations)
        if admitted is None:
            from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector

            admitted = VirtualWorkspaceSourceProjectionCacheEntry(
                self.metadata,
                SourceBindingWorkspaceProjector(source_bindings).admit_prepared_projection(
                    self.projection
                ),
            )
            self.source_admitted_entries[declarations] = admitted
        return admitted

    def entry_for_projection(
        self, projection: VirtualWorkspaceSourceProjection,
    ) -> VirtualWorkspaceSourceProjectionCacheEntry | None:
        """Recognize only projections retained by this admitted document."""
        if self.projection is projection:
            return self
        return next((
            entry for entry in self.source_admitted_entries.values()
            if entry.projection is projection
        ), None)

    def partition_by_axes(
        self, axis_ids: Sequence[str],
    ) -> Mapping[str, VirtualWorkspaceSourceProjection]:
        """Derive missing axis views together from this retained document."""
        if self.projection is None:
            raise ValueError("Axis views require an admitted source workspace projection.")
        selected = tuple(dict.fromkeys(axis_ids))
        missing = tuple(
            axis_id for axis_id in selected
            if axis_id not in self.axis_filtered_projections
        )
        if missing:
            self.axis_filtered_projections.update(
                self.projection.partition_by_axes(missing)
            )
        return MappingProxyType({
            axis_id: self.axis_filtered_projections[axis_id] for axis_id in selected
        })


@dataclass(slots=True)
class VirtualWorkspaceSourceProjectionCache:
    """Process-local cache for projections keyed by metadata object identity."""

    projections_by_plate_path: dict[
        str,
        VirtualWorkspaceSourceProjectionCacheEntry,
    ] = field(default_factory=dict)

    def projection_for(
        self,
        plate_path: Path,
        metadata: OpenHCSMetadataPayload,
        *,
        source_bindings: SourceBindingsConfig | None = None,
    ) -> VirtualWorkspaceSourceProjection | None:
        plate_key = str(plate_path)
        cached = self.projections_by_plate_path.get(plate_key)
        if cached is None or cached.metadata is not metadata:
            projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata_if_available(
                plate_path,
                metadata,
            )
            cached = VirtualWorkspaceSourceProjectionCacheEntry(metadata, projection)
            self.projections_by_plate_path[plate_key] = cached
        return cached.admitted_for(source_bindings).projection

    def filtered_by_axis(
        self,
        projection: VirtualWorkspaceSourceProjection,
        *,
        axis_id: str | None,
    ) -> VirtualWorkspaceSourceProjection:
        """Reuse axis views only while their admitted document owns the input.

        Runtime overlays and caller-created projections have no retained cache
        authority. Derive them directly instead of retaining old output epochs
        or identifying a released projection by its recyclable object ID.
        """
        if axis_id is None:
            return projection
        return self.partition_by_axes(projection, axis_ids=(axis_id,))[axis_id]

    def partition_by_axes(
        self,
        projection: VirtualWorkspaceSourceProjection,
        *,
        axis_ids: Sequence[str],
    ) -> Mapping[str, VirtualWorkspaceSourceProjection]:
        """Share admitted axis views between compilation and runtime queries."""
        document_entry = self.projections_by_plate_path.get(projection.workspace_root)
        cached = (
            None if document_entry is None
            else document_entry.entry_for_projection(projection)
        )
        if cached is None:
            return projection.partition_by_axes(axis_ids)
        return cached.partition_by_axes(axis_ids)


# One process-level default: the projection authority owns its cache, so
# callers that do not thread one explicitly (per-axis compile initialization)
# reuse the plate's derived projection instead of re-ingesting its metadata
# document for every axis. Document identity is the invalidation signal.
DEFAULT_SOURCE_PROJECTION_CACHE = VirtualWorkspaceSourceProjectionCache()


@dataclass(frozen=True, slots=True)
class VirtualWorkspaceSourceProjectionAuthority:
    """Projection authority for source-workspace metadata owned by a plate handler."""

    plate_path: Path
    metadata_handler: "MetadataHandler"
    filemanager: "FileManager"
    cache: VirtualWorkspaceSourceProjectionCache | None = None
    source_bindings: SourceBindingsConfig | None = None
    _workspace_metadata_handler: "OpenHCSMetadataHandler | None" = field(
        default=None, init=False, compare=False, repr=False,
    )

    @classmethod
    def from_context(
        cls,
        context: "ProcessingContext",
        *,
        cache: VirtualWorkspaceSourceProjectionCache | None = None,
    ) -> "VirtualWorkspaceSourceProjectionAuthority":
        return RuntimeVirtualWorkspaceSourceProjectionAuthority(
            plate_path=Path(context.plate_path),
            metadata_handler=context.microscope_handler.metadata_handler,
            filemanager=context.filemanager,
            cache=DEFAULT_SOURCE_PROJECTION_CACHE if cache is None else cache,
            context=context,
            source_bindings=context.microscope_handler.source_admission_config(),
        )

    @classmethod
    def from_plate_metadata(
        cls,
        *,
        plate_path: Path,
        metadata_handler: "MetadataHandler",
        filemanager: "FileManager",
        cache: VirtualWorkspaceSourceProjectionCache | None = None,
        source_bindings: SourceBindingsConfig | None = None,
    ) -> "VirtualWorkspaceSourceProjectionAuthority":
        """Build projection authority from the plate-level metadata owners."""

        return cls(
            plate_path=plate_path,
            metadata_handler=metadata_handler,
            filemanager=filemanager,
            cache=DEFAULT_SOURCE_PROJECTION_CACHE if cache is None else cache,
            source_bindings=source_bindings,
        )

    def is_bound_to_context(self, context: "ProcessingContext") -> bool:
        """Compare actual owners, never identities of already-released objects."""
        if not (
            self.plate_path == Path(context.plate_path)
            and self.metadata_handler is context.microscope_handler.metadata_handler
            and self.filemanager is context.filemanager
        ):
            return False
        return self.source_bindings == context.microscope_handler.source_admission_config()

    def metadata_handlers(self) -> tuple["MetadataHandler", ...]:
        """Observe workspace eligibility live while retaining admitted providers."""
        from openhcs.microscopes.openhcs import OpenHCSMetadataHandler

        if isinstance(self.metadata_handler, OpenHCSMetadataHandler):
            return (self.metadata_handler,)
        metadata_path = self.plate_path / OpenHCSMetadataHandler.METADATA_FILENAME
        if not self.filemanager.exists(str(metadata_path), Backend.DISK.value):
            return (self.metadata_handler,)
        workspace_handler = self._workspace_metadata_handler
        if workspace_handler is None:
            workspace_handler = OpenHCSMetadataHandler(self.filemanager)
            object.__setattr__(self, "_workspace_metadata_handler", workspace_handler)
        workspace_handler.invalidate_metadata_cache()
        return (self.metadata_handler, workspace_handler)

    def metadata_documents(self) -> tuple[OpenHCSMetadataPayload, ...]:
        documents: list[OpenHCSMetadataPayload] = []
        for metadata_handler in self.metadata_handlers():
            metadata = metadata_handler.source_workspace_metadata_document(
                self.plate_path
            )
            if metadata is None:
                continue
            if not isinstance(metadata, Mapping):
                raise RuntimeError(
                    "Source workspace metadata document must be a mapping."
                )
            documents.append(metadata)
        return tuple(documents)

    def _projection_for_axis(
        self,
        projection: VirtualWorkspaceSourceProjection,
        *,
        axis_id: str | None,
    ) -> VirtualWorkspaceSourceProjection:
        """Derive an explicitly requested axis from this source owner."""
        if self.cache is None:
            return projection.filtered_by_axis(axis_id=axis_id)
        return self.cache.filtered_by_axis(projection, axis_id=axis_id)

    def projection_if_available(
        self, *, axis_id: str | None = None,
    ) -> VirtualWorkspaceSourceProjection | None:
        workspace_root = self.metadata_handler.source_workspace_root(self.plate_path)
        for metadata in self.metadata_documents():
            if self.cache is None:
                projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata_if_available(
                    workspace_root,
                    metadata,
                )
                if projection is not None and self.source_bindings is not None:
                    from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector

                    projection = SourceBindingWorkspaceProjector(
                        self.source_bindings
                    ).admit_prepared_projection(projection)
            else:
                projection = self.cache.projection_for(
                    workspace_root, metadata, source_bindings=self.source_bindings,
                )
            if projection is None:
                continue
            return self._projection_for_axis(projection, axis_id=axis_id)
        return None

    def projection_or_empty(
        self, *, axis_id: str | None = None,
    ) -> VirtualWorkspaceSourceProjection:
        projection = self.projection_if_available(axis_id=axis_id)
        if projection is not None:
            return projection
        return VirtualWorkspaceSourceProjection.empty(self.plate_path)


@dataclass(frozen=True, slots=True)
class RuntimeVirtualWorkspaceSourceProjectionAuthority(
    VirtualWorkspaceSourceProjectionAuthority
):
    """Read completed same-plate outputs from their execution observation owner."""

    context: "ProcessingContext" = field(kw_only=True, compare=False, repr=False)

    def is_bound_to_context(self, context: "ProcessingContext") -> bool:
        return self.context is context and super(
            RuntimeVirtualWorkspaceSourceProjectionAuthority, self
        ).is_bound_to_context(context)

    def projection_if_available(
        self, *, axis_id: str | None = None,
    ) -> VirtualWorkspaceSourceProjection | None:
        projection = super(
            RuntimeVirtualWorkspaceSourceProjectionAuthority, self
        ).projection_if_available()
        produced_entries = tuple(
            entries
            for target, entries in (
                self.context.completed_step_outputs.source_projection_entries_by_target.items()
            )
            if source_path_identity_key(target.plate_root)
            == source_path_identity_key(self.plate_path)
            and not entries.is_empty
        )
        if not produced_entries:
            return (
                None if projection is None
                else self._projection_for_axis(projection, axis_id=axis_id)
            )
        builder = VirtualWorkspaceSourceProjectionBuilder(self.plate_path)
        if projection is not None:
            builder.ingest_workspace_mapping(
                VirtualWorkspaceMapping(projection.source_refs_by_virtual_path)
            )
            builder.ingest_source_projections(
                VirtualWorkspaceSourceProjectionEntries(
                    projection.source_projections_by_virtual_path
                )
            )
            builder.ingest_source_metadata(
                VirtualWorkspaceSourceMetadataEntries(projection.source_metadata_by_path)
            )
        for entries in produced_entries:
            fields = SourceProjectionMetadataSerializer.workspace_fields(
                entries.projection_paths
            )
            builder.ingest_workspace_mapping(
                VirtualWorkspaceMapping.from_subdirectory(fields)
            )
            builder.ingest_admitted_subdirectory(fields, entries)
        return self._projection_for_axis(builder.projection(), axis_id=axis_id)


@dataclass(slots=True)
class VirtualWorkspaceSourceProjectionBuilder:
    """Build source-binding projection data from OpenHCS virtual-workspace metadata."""

    plate_path: Path
    workspace_source_refs: dict[str, SourcePixelRef] = field(default_factory=dict)
    source_metadata_by_path: dict[str, SourceMetadataMapping] = field(
        default_factory=dict
    )
    source_projections_by_virtual_path: dict[str, SourceProjection] = field(
        default_factory=dict
    )

    def ingest_subdirectory(self, subdirectory: OpenHCSSubdirectoryPayload) -> None:
        workspace_mapping = VirtualWorkspaceMapping.from_subdirectory(subdirectory)
        self.ingest_workspace_mapping(workspace_mapping)
        self.ingest_admitted_subdirectory(
            subdirectory,
            VirtualWorkspaceSourceProjectionEntries.from_subdirectory(subdirectory),
        )

    def ingest_workspace_mapping(
        self, workspace_mapping: VirtualWorkspaceMapping
    ) -> None:
        for virtual_path, source_ref in workspace_mapping.entries.items():
            self.record_workspace_source_path(virtual_path, source_ref)

    def record_workspace_source_path(
        self,
        virtual_path: str,
        source_ref: SourcePixelRef,
    ) -> None:
        if not isinstance(source_ref, SourcePixelRef):
            raise TypeError(
                "Workspace source references must be SourcePixelRef values."
            )
        loadable_path = str(self.plate_path / virtual_path)
        self.workspace_source_refs[virtual_path] = source_ref
        self.workspace_source_refs[loadable_path] = source_ref

    def ingest_admitted_subdirectory(
        self,
        subdirectory: OpenHCSSubdirectoryPayload,
        source_projections: VirtualWorkspaceSourceProjectionEntries,
    ) -> None:
        """Ingest admitted projections, then their correlated source fields.

        Workspace mappings must already be ingested. Raw readers admit each
        projection after its mapping; reconciliation admits the whole document's
        projection records before any workspace fields. Both share this tail.
        """
        self.ingest_source_projections(source_projections)
        self.ingest_source_metadata(
            VirtualWorkspaceSourceMetadataEntries.from_subdirectory(subdirectory)
        )

    def ingest_source_projections(
        self,
        source_projections: VirtualWorkspaceSourceProjectionEntries,
    ) -> None:
        """Ingest a projection-only source authority after its workspace mapping."""
        for virtual_path, projection in source_projections.entries.items():
            mapped_ref = self.workspace_source_refs.get(virtual_path)
            if mapped_ref is None:
                raise RuntimeError(
                    "source_projection has no workspace_mapping entry for "
                    f"{virtual_path!r}."
                )
            if projection.ref != mapped_ref:
                raise RuntimeError(
                    "source_projection ref conflicts with workspace_mapping for "
                    f"{virtual_path!r}."
                )
            self.source_projections_by_virtual_path[virtual_path] = projection
            self.source_projections_by_virtual_path[
                str(self.plate_path / virtual_path)
            ] = projection

    def ingest_source_metadata(
        self,
        source_metadata: VirtualWorkspaceSourceMetadataEntries,
    ) -> None:
        for virtual_path, metadata_fields in source_metadata.entries.items():
            self.record_source_metadata(virtual_path, metadata_fields)

    def record_source_metadata(
        self,
        virtual_path: str,
        metadata_fields: SourceMetadataMapping,
    ) -> None:
        normalized_metadata = SourceMetadataFields.readonly_snapshot(metadata_fields)
        self.source_metadata_by_path[virtual_path] = normalized_metadata
        self.source_metadata_by_path[str(self.plate_path / virtual_path)] = (
            normalized_metadata
        )

    def projection(self) -> VirtualWorkspaceSourceProjection:
        if not self.workspace_source_refs:
            raise RuntimeError(
                "virtual_workspace source binding resolution requires "
                "workspace_mapping entries in OpenHCS metadata."
            )
        return VirtualWorkspaceSourceProjection(
            source_refs_by_virtual_path=MappingProxyType(self.workspace_source_refs),
            source_metadata_by_path=MappingProxyType(self.source_metadata_by_path),
            source_projections_by_virtual_path=MappingProxyType(
                self.source_projections_by_virtual_path
            ),
            workspace_root=str(self.plate_path),
        )
