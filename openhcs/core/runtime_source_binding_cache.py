"""Processing-context-local source-binding runtime caches."""

from __future__ import annotations

from collections.abc import Mapping
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

if TYPE_CHECKING:
    from openhcs.core.source_binding_selection import (
        SourcePatternResolutionContext,
        SourceUniverseRuntimeState,
    )
    from openhcs.core.source_workspace_projection import (
        VirtualWorkspaceSourceProjection,
    )
    from openhcs.microscopes.microscope_interfaces import FilenameParser


@dataclass(frozen=True, slots=True)
class RuntimeSourceResolutionSnapshot:
    """A derived resolution view retaining its exact projection and parser owners."""

    projection: "VirtualWorkspaceSourceProjection"
    context: "SourcePatternResolutionContext"

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
            SourcePatternResolutionContext,
        )

        context = SourcePatternResolutionContext.from_projection(
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
        return cls(projection=projection, context=context)


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
            return cached.context
        snapshot = RuntimeSourceResolutionSnapshot.from_projection(
            parser=parser,
            projection=projection,
            metadata_rules=metadata_rules,
        )
        self.source_resolution_snapshots[key] = snapshot
        return snapshot.context

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
