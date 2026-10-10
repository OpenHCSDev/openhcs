"""Processing-context-local source-binding runtime caches."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from types import MappingProxyType
from typing import Any, Hashable, TYPE_CHECKING

from openhcs.core.source_bindings import (
    SourceBindingRuntimeMetadataNormalizer,
    MetadataExtractionRule,
)
from openhcs.core.source_metadata import (
    ResolvedSourceMetadataRecord,
    SourceMetadataMapping,
)
from openhcs.core.source_matching import source_component_metadata_items
from openhcs.core.source_path_identity import source_path_identity_key

if TYPE_CHECKING:
    from openhcs.core.source_binding_selection import (
        SourceCandidatePathResolution,
        SourcePatternResolutionContext,
        SourceUniverseRuntimeState,
    )
    from openhcs.core.source_image_provenance import SourceImageIdentity
    from openhcs.core.axes import Axis
    from openhcs.core.source_workspace_projection import (
        VirtualWorkspaceSourceProjection,
    )
    from openhcs.microscopes.microscope_interfaces import FilenameParser


@dataclass(frozen=True, slots=True)
class RuntimeSourceResolutionSnapshot:
    """A derived resolution view retaining its exact projection and parser owners."""

    projection: "VirtualWorkspaceSourceProjection"
    context: "SourcePatternResolutionContext"
    path_resolutions: Mapping[str, "SourceCandidatePathResolution"]
    component_values: Mapping[str, tuple[Mapping["type[Axis]", str], ...]]

    def context_for_matching(self) -> "SourcePatternResolutionContext":
        """Expose this admitted epoch through the existing matching context."""
        return replace(self.context, resolution_snapshot=self)

    def matching_candidates_for_source_identities(
        self,
        identities: Sequence["SourceImageIdentity"],
        candidates: Sequence[str],
    ) -> tuple[tuple[str, ...], ...]:
        """Join captured paths and correlated component records in query order."""
        positions = self.context.declared_positions_for_candidates(candidates)
        if any(position not in self.path_resolutions for position in positions):
            return self.context.matching_candidates_for_source_identities(
                identities, candidates,
            )
        positions_by_path: dict[str, set[str]] = {}
        for position in positions:
            resolution = self.path_resolutions[position]
            paths = (
                resolution.mapped_source_paths[0]
                if resolution.mapped_source_paths else position,
                *(resolution.virtual_paths or (position,)),
            )
            for path in paths:
                positions_by_path.setdefault(source_path_identity_key(path), set()).add(position)

        queries = tuple(
            source_component_metadata_items(identity.component_metadata or {})
            for identity in identities
        )
        component_indexes = {}
        for query in queries:
            components = tuple(component for component, _ in query)
            if not components or components in component_indexes:
                continue
            index: dict[tuple[str, ...], set[str]] = {}
            for position in positions:
                for record in self.component_values[position]:
                    if all(component in record for component in components):
                        key = tuple(record[component] for component in components)
                        index.setdefault(key, set()).add(position)
            component_indexes[components] = index

        matches = []
        for identity, query in zip(identities, queries, strict=True):
            if not identity.addressable:
                matches.append(())
                continue
            path_positions = (
                None if identity.path is None else positions_by_path.get(
                    source_path_identity_key(identity.path), set(),
                )
            )
            components = tuple(component for component, _ in query)
            component_positions = (
                component_indexes[components].get(
                    tuple(str(value) for _, value in query), set(),
                ) if components else None
            )
            matches.append(tuple(
                position for position in positions
                if (path_positions is None or position in path_positions)
                and (component_positions is None or position in component_positions)
                and (components or identity.path is not None)
            ))
        return tuple(matches)

    @classmethod
    def from_projection(
        cls,
        *,
        parser: "FilenameParser",
        projection: "VirtualWorkspaceSourceProjection",
        metadata_rules: tuple[MetadataExtractionRule, ...],
    ) -> "RuntimeSourceResolutionSnapshot":
        """Resolve declared positions into one independently owned runtime view."""
        from openhcs.core.source_binding_selection import (
            DeclaredSourceMetadataRecord,
            SourceIdentityResolutionContext,
        )

        context = SourceIdentityResolutionContext.from_projection(
            parser=parser,
            projection=projection,
            metadata_rules=metadata_rules,
        )
        normalized_metadata = SourceBindingRuntimeMetadataNormalizer(
            projection.source_metadata_by_path
        ).normalized()
        context = replace(
            context,
            source_metadata_by_path=MappingProxyType(
                {
                    path: DeclaredSourceMetadataRecord.from_mapping(metadata)
                    for path, metadata in normalized_metadata.items()
                }
            ),
            source_projections_by_virtual_path=MappingProxyType(
                dict(context.source_projections_by_virtual_path)
            ),
        )
        paths = dict.fromkeys(
            (
                *context.source_metadata_by_path,
                *context.source_paths_by_virtual_path,
                *context.source_paths_by_virtual_path.values(),
            )
        )
        records = {}
        for path in paths:
            metadata = context.metadata_for_path(path)
            records[path] = ResolvedSourceMetadataRecord.from_mapping(
                {} if metadata is None else metadata
            )
        context = replace(context, source_metadata_by_path=MappingProxyType(records))
        resolutions = {
            path: context._candidate_path_resolution(path)
            for path in context.source_paths_by_virtual_path
        }
        components = {
            path: tuple(
                MappingProxyType({
                    component: str(value)
                    for component, value in source_component_metadata_items(metadata)
                })
                for metadata in context.metadata_for_paths(resolution.metadata_paths())
            )
            for path, resolution in resolutions.items()
        }
        return cls(
            projection=projection, context=context,
            path_resolutions=MappingProxyType(resolutions),
            component_values=MappingProxyType(components),
        )


@dataclass(slots=True)
class RuntimeSourceBindingContextCache:
    """Cache source-binding data that is invariant across runtime contexts."""

    source_metadata_by_mapping_identity: dict[
        int,
        Mapping[str, SourceMetadataMapping],
    ] = field(default_factory=dict)
    runtime_universe_state_by_request_identity: dict[
        tuple[int, tuple[str, ...], object, int | None],
        "SourceUniverseRuntimeState",
    ] = field(default_factory=dict)
    source_resolution_snapshots: dict[
        tuple[int, int, tuple[Hashable, ...], tuple[MetadataExtractionRule, ...]],
        RuntimeSourceResolutionSnapshot,
    ] = field(default_factory=dict)

    def source_pattern_context(
        self,
        *,
        parser: "FilenameParser",
        projection: "VirtualWorkspaceSourceProjection",
        metadata_rules: tuple[MetadataExtractionRule, ...],
    ) -> "SourcePatternResolutionContext":
        """Own one normalized runtime snapshot for exact source declarations."""
        key = (id(projection), id(parser), parser.semantic_identity(), metadata_rules)
        cached = self.source_resolution_snapshots.get(key)
        if cached is not None:
            return cached.context_for_matching()
        snapshot = RuntimeSourceResolutionSnapshot.from_projection(
            parser=parser,
            projection=projection,
            metadata_rules=metadata_rules,
        )
        self.source_resolution_snapshots[key] = snapshot
        return snapshot.context_for_matching()

    def __reduce__(self) -> tuple[type[RuntimeSourceBindingContextCache], tuple[()]]:
        """Transport reconstructs all derived caches from declaration defaults."""
        return type(self), ()

    def normalized_source_metadata(
        self,
        source_metadata_by_path: Mapping[str, SourceMetadataMapping],
    ) -> Mapping[str, SourceMetadataMapping]:
        """Return normalized source metadata for a projection-owned mapping."""
        cache_key = id(source_metadata_by_path)
        cached = self.source_metadata_by_mapping_identity.get(cache_key)
        if cached is None:
            cached = SourceBindingRuntimeMetadataNormalizer(
                source_metadata_by_path
            ).normalized()
            self.source_metadata_by_mapping_identity[cache_key] = cached
        return cached

    def runtime_universe_state(
        self,
        *,
        plan: Any,
        matching_files: tuple[str, ...],
        source_backend: object,
        source_projection: object | None,
    ) -> "SourceUniverseRuntimeState | None":
        """Return cached source-universe state for one request identity."""
        return self.runtime_universe_state_by_request_identity.get(
            self.runtime_universe_state_key(
                plan=plan,
                matching_files=matching_files,
                source_backend=source_backend,
                source_projection=source_projection,
            )
        )

    def store_runtime_universe_state(
        self,
        runtime_state: "SourceUniverseRuntimeState",
        *,
        plan: Any,
        matching_files: tuple[str, ...],
        source_backend: object,
        source_projection: object | None,
    ) -> "SourceUniverseRuntimeState":
        """Cache source-universe state for one request identity."""
        self.runtime_universe_state_by_request_identity[
            self.runtime_universe_state_key(
                plan=plan,
                matching_files=matching_files,
                source_backend=source_backend,
                source_projection=source_projection,
            )
        ] = runtime_state
        return runtime_state

    @staticmethod
    def runtime_universe_state_key(
        *,
        plan: Any,
        matching_files: tuple[str, ...],
        source_backend: object,
        source_projection: object | None,
    ) -> tuple[int, tuple[str, ...], object, int | None]:
        """Return the process-local identity for one source-universe request."""
        return (
            id(plan),
            tuple(matching_files),
            source_backend,
            None if source_projection is None else id(source_projection),
        )
