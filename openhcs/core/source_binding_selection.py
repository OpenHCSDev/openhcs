"""Shared source-binding candidate selection for planning and runtime."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from enum import Enum
from functools import lru_cache
from pathlib import Path
from types import MappingProxyType
from typing import ClassVar, Mapping, Sequence, TYPE_CHECKING

from metaclass_registry import AutoRegisterMeta

from openhcs.constants.constants import Backend
from openhcs.core.path_pattern_matching import PathPatternTemplateMatcher
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    MetadataExtractionRule,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceSetRole,
    SourceProjectionRole,
)
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenance,
)
from openhcs.core.source_metadata import (
    SourceMetadataFields,
    SourceMetadataMapping,
    SourceMetadataRecord,
    SourceMetadataValue,
)
from openhcs.core.source_matching import (
    SourceImageSetIdentity,
    SourceImageSetIdentityCompatibility,
    SourceImageSetIdentityPolicy,
    merge_source_metadata,
    metadata_from_rules,
    semantic_source_metadata_value,
    source_component_metadata_items,
    source_component_metadata_value,
    source_component_metadata_values,
    source_filters_match,
    source_metadata_value,
    source_metadata_values_equal,
)
from openhcs.core.source_path_identity import (
    source_path_identity,
    source_path_identity_key,
    source_paths_equal,
)
from openhcs.core.source_projection import SourceProjection
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
)
from openhcs.core.aligned_image_payload import stack_image_payloads
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadataCompositionMode,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.steps.function_io import get_all_image_paths
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.compiled_step_plan import CompiledStepPlan

if TYPE_CHECKING:
    from openhcs.core.runtime_adapters import RuntimeAdapterRequest
    from openhcs.core.runtime_source_binding_cache import RuntimeSourceResolutionSnapshot
    from polystore.filemanager import FileManager
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.microscopes.microscope_interfaces import FilenameParser


SourceCandidatePath = str


@lru_cache(maxsize=65536)
def _cached_source_candidate_pattern_keys(pattern_path: str) -> tuple[str, ...]:
    """Return candidate source path spellings used for selector matching."""

    path = Path(pattern_path)
    return tuple(dict.fromkeys((pattern_path, path.as_posix(), path.name)))


@dataclass(frozen=True, slots=True, eq=False)
class DeclaredSourceMetadataRecord(SourceMetadataRecord):
    """Live declared metadata that still requires path-specific fallbacks."""

    @classmethod
    def from_mapping(
        cls, metadata: SourceMetadataMapping
    ) -> "DeclaredSourceMetadataRecord":
        return cls(tuple((str(key), value) for key, value in metadata.items()))

    def resolve(
        self,
        path: str,
        parser: "FilenameParser",
        metadata_rules: tuple[MetadataExtractionRule, ...],
    ) -> "SourceMetadataRecord | None":
        """Fill parser and extraction-rule fields absent from declarations."""
        metadata: dict[str, SourceMetadataValue] = {}
        merge_source_metadata(metadata, self, path=path)
        parsed_metadata = parser.parse_filename(path)
        if parsed_metadata is not None:
            merge_source_metadata(
                metadata,
                {
                    key: value
                    for key, value in parsed_metadata.wire_mapping().items()
                    if key not in metadata
                },
                path=path,
            )
        rule_metadata = metadata_from_rules(path, metadata_rules)
        if rule_metadata:
            merge_source_metadata(
                metadata,
                {
                    key: value
                    for key, value in rule_metadata.items()
                    if key not in metadata
                },
                path=path,
            )
        return self.from_mapping(metadata) if metadata else None


@dataclass(frozen=True, slots=True)
class SourceMetadataCandidates:
    """Candidate metadata records resolved for one source-binding pattern."""

    values: tuple[SourceMetadataRecord, ...]

    def __iter__(self):
        return iter(self.values)

    def __bool__(self) -> bool:
        return bool(self.values)

    def first_required(self, pattern: SourceCandidatePath) -> SourceMetadataRecord:
        if self.values:
            return self.values[0]
        raise ValueError(
            "Source binding metadata resolution found no parser-readable metadata "
            f"for candidate {pattern!s}."
        )


@dataclass(frozen=True, slots=True)
class SourceCandidatePathResolution:
    """Virtual and mapped-source path views for one source-binding candidate."""

    pattern_keys: tuple[str, ...]
    virtual_paths: tuple[str, ...]
    mapped_source_paths: tuple[str, ...]

    def metadata_paths(self) -> tuple[str, ...]:
        if self.virtual_paths:
            return tuple(
                dict.fromkeys(
                    (*self.virtual_paths, *self.mapped_source_paths, *self.pattern_keys)
                )
            )
        return tuple(dict.fromkeys((*self.pattern_keys, *self.mapped_source_paths)))

    def filter_paths(self) -> tuple[str, ...]:
        if self.mapped_source_paths:
            return tuple(dict.fromkeys(self.mapped_source_paths))
        if self.virtual_paths:
            return tuple(dict.fromkeys((*self.virtual_paths, *self.pattern_keys)))
        return self.pattern_keys


@dataclass(frozen=True, slots=True)
class SourcePatternResolutionContext:
    """Source paths and metadata available while filtering execution candidates."""

    parser: "FilenameParser"
    source_paths_by_virtual_path: Mapping[str, str]
    source_metadata_by_path: Mapping[str, SourceMetadataRecord] = field(
        default_factory=dict
    )
    metadata_rules: tuple[MetadataExtractionRule, ...] = ()
    source_projections_by_virtual_path: Mapping[str, SourceProjection] = field(
        default_factory=dict
    )
    resolution_snapshot: RuntimeSourceResolutionSnapshot | None = None

    @classmethod
    def from_sources(
        cls,
        *,
        parser: "FilenameParser",
        source_paths_by_virtual_path: Mapping[str, str],
        source_metadata_by_path: Mapping[str, SourceMetadataMapping] | None = None,
        metadata_rules: tuple[MetadataExtractionRule, ...] = (),
    ) -> "SourcePatternResolutionContext":
        if source_metadata_by_path is None:
            metadata_by_path: Mapping[str, SourceMetadataRecord] = {}
        else:
            metadata_by_path = {
                str(path): (
                    metadata
                    if isinstance(metadata, SourceMetadataRecord)
                    else DeclaredSourceMetadataRecord.from_mapping(metadata)
                )
                for path, metadata in source_metadata_by_path.items()
            }
        return cls(
            parser=parser,
            source_paths_by_virtual_path=source_paths_by_virtual_path,
            source_metadata_by_path=metadata_by_path,
            metadata_rules=metadata_rules,
        )

    @classmethod
    def from_projection(
        cls,
        *,
        parser: "FilenameParser",
        projection: VirtualWorkspaceSourceProjection,
        metadata_rules: tuple[MetadataExtractionRule, ...] = (),
    ) -> "SourcePatternResolutionContext":
        return replace(
            cls.from_sources(
                parser=parser,
                source_paths_by_virtual_path=MappingProxyType(
                    {
                        virtual_path: source_ref.backend_address
                        for virtual_path, source_ref in (
                            projection.source_refs_by_virtual_path.items()
                        )
                    }
                ),
                source_metadata_by_path=projection.source_metadata_by_path,
                metadata_rules=metadata_rules,
            ),
            source_projections_by_virtual_path=(
                projection.source_projections_by_virtual_path
            ),
        )

    @property
    def has_virtual_source_workspace(self) -> bool:
        return bool(self.source_paths_by_virtual_path)

    def candidate_paths(self, pattern: SourceCandidatePath) -> tuple[str, ...]:
        return self._candidate_path_resolution(pattern).metadata_paths()

    def candidate_filter_paths(self, pattern: SourceCandidatePath) -> tuple[str, ...]:
        resolution = self._candidate_path_resolution(pattern)
        source_filter_paths = tuple(
            dict.fromkeys(
                source_filter_path
                for metadata in self.metadata_for_paths(resolution.metadata_paths())
                for source_filter_path in SourceMetadataFields.source_filter_paths(
                    metadata
                )
            )
        )
        if source_filter_paths:
            return source_filter_paths
        return resolution.filter_paths()

    def _candidate_path_resolution(
        self,
        pattern: SourceCandidatePath,
    ) -> SourceCandidatePathResolution:
        if self.resolution_snapshot is not None:
            admitted = self.resolution_snapshot.path_resolutions.get(pattern)
            if admitted is not None:
                return admitted
        keys = _cached_source_candidate_pattern_keys(pattern)
        exact_virtual_path = next(
            (key for key in keys if key in self.source_paths_by_virtual_path),
            None,
        )
        if exact_virtual_path is not None:
            projection = self.source_projections_by_virtual_path.get(exact_virtual_path)
            virtual_matches = (
                tuple(
                    path
                    for path, declared in self.source_projections_by_virtual_path.items()
                    if declared is projection
                )
                if projection is not None else (exact_virtual_path,)
            )
        else:
            virtual_matches = tuple(
                dict.fromkeys(
                    virtual_path
                    for key in keys
                    for virtual_path in self._matching_virtual_paths(key)
                )
            )
        mapped = tuple(
            self.source_paths_by_virtual_path[key]
            for key in (*keys, *virtual_matches)
            if key in self.source_paths_by_virtual_path
        )
        return SourceCandidatePathResolution(
            pattern_keys=keys,
            virtual_paths=virtual_matches,
            mapped_source_paths=mapped,
        )

    def _matching_virtual_paths(self, pattern_key: str) -> tuple[str, ...]:
        if pattern_key in self.source_paths_by_virtual_path:
            return ()
        matcher = PathPatternTemplateMatcher.from_pattern(pattern_key)
        if matcher is None:
            return ()
        return tuple(
            virtual_path
            for virtual_path in self.source_paths_by_virtual_path
            if not source_path_identity(virtual_path).is_absolute()
            and matcher.matches(source_path_identity(virtual_path).name)
        )

    def candidate_metadata(
        self,
        pattern: SourceCandidatePath,
    ) -> SourceMetadataCandidates:
        return self.metadata_for_paths(self.candidate_paths(pattern))

    def source_path_for(self, path: str) -> str:
        """Return the physical source path represented by a runtime path."""
        resolved_paths = self._candidate_path_resolution(path).mapped_source_paths
        if resolved_paths:
            return str(resolved_paths[0])
        return str(path)

    def virtual_paths_for_source(self, source_path: str) -> tuple[str, ...]:
        """Return exact virtual-workspace paths declared for one source path."""

        return self.virtual_paths_for_sources((source_path,))[0]

    def virtual_paths_for_sources(
        self,
        source_paths: Sequence[str],
    ) -> tuple[tuple[str, ...], ...]:
        """Resolve exact physical addresses in one pass over the declarations."""
        positions_by_source: dict[str, list[str]] = {}
        for position, source in self.source_paths_by_virtual_path.items():
            positions_by_source.setdefault(source_path_identity_key(source), []).append(
                position
            )
        return tuple(
            tuple(positions_by_source.get(source_path_identity_key(source), ()))
            for source in source_paths
        )

    def declared_positions_for_candidates(
        self,
        candidates: Sequence[SourceCandidatePath],
    ) -> tuple[SourceCandidatePath, ...]:
        """Project exact physical spellings onto their declared workspace positions.

        Workspace positions are not physical-file identities: several positions
        may address different planes in one store. Lookup spellings backed by
        the same nominal projection are aliases of one position. Mapping-only
        declarations and distinct projections retain their separate positions.
        No basename, filesystem resolution or physical-ref equality participates.
        """
        projection_positions: dict[int, SourceCandidatePath] = {}
        for position, projection in self.source_projections_by_virtual_path.items():
            projection_positions.setdefault(id(projection), position)
        positions: list[SourceCandidatePath] = []
        for candidate, virtual_paths in zip(
            candidates, self.virtual_paths_for_sources(candidates), strict=True
        ):
            declared_positions = (
                (candidate,)
                if candidate in self.source_paths_by_virtual_path
                else virtual_paths or (candidate,)
            )
            for position in declared_positions:
                projection = self.source_projections_by_virtual_path.get(position)
                positions.append(
                    projection_positions[id(projection)]
                    if projection is not None else position
                )
        return tuple(dict.fromkeys(positions))

    def runtime_paths_for_candidate(
        self,
        candidate_path: str,
    ) -> tuple[str, ...]:
        """Project one source candidate through exact workspace provenance."""

        declared_virtual_paths = self._candidate_path_resolution(
            candidate_path
        ).virtual_paths
        if declared_virtual_paths:
            return declared_virtual_paths
        virtual_paths = self.virtual_paths_for_source(candidate_path)
        if virtual_paths:
            return virtual_paths
        return (candidate_path,)

    def candidate_matches_source_binding_projection(
        self,
        candidate_path: str,
        binding: NamedSourceBinding,
    ) -> bool:
        """Match a virtual candidate through its nominal source projection."""

        if not self.source_projections_by_virtual_path:
            return True
        resolution = self._candidate_path_resolution(candidate_path)
        virtual_paths = resolution.virtual_paths
        if not virtual_paths:
            virtual_paths = self.virtual_paths_for_source(candidate_path)
        if not virtual_paths:
            return True
        projections = tuple(
            self.source_projections_by_virtual_path.get(path) for path in virtual_paths
        )
        return any(
            projection is not None and projection.matches_binding(binding)
            for projection in projections
        )

    def metadata_for_paths(
        self,
        paths: tuple[str, ...],
    ) -> SourceMetadataCandidates:
        return SourceMetadataCandidates(
            tuple(
                metadata
                for path in paths
                for metadata in (self.metadata_for_path(path),)
                if metadata is not None
            )
        )

    def metadata_for_path(self, path: str) -> SourceMetadataRecord | None:
        record = self.source_metadata_by_path.get(path)
        if record is None:
            record = DeclaredSourceMetadataRecord(())
        return record.resolve(path, self.parser, self.metadata_rules)

    def merged_metadata_for_paths(
        self,
        paths: tuple[str, ...],
    ) -> SourceMetadataRecord | None:
        """Return one metadata record merged from all path identities."""
        metadata: dict[str, SourceMetadataValue] = {}
        for path in dict.fromkeys(paths):
            path_metadata = self.metadata_for_path(path)
            if path_metadata is not None:
                merge_source_metadata(metadata, path_metadata, path=path)
        if metadata:
            return DeclaredSourceMetadataRecord.from_mapping(metadata)
        return None

    def source_metadata_by_paths(
        self,
        paths: Sequence[str],
    ) -> Mapping[str, SourceMetadataMapping]:
        """Return resolved metadata keyed by the paths visible in a source universe."""
        metadata_by_path: dict[str, SourceMetadataMapping] = {}
        for path in dict.fromkeys(str(path) for path in paths):
            metadata = self.metadata_for_path(path)
            if metadata is not None:
                metadata_by_path[path] = metadata
        return MappingProxyType(metadata_by_path)

    def has_metadata_field(
        self,
        patterns: Sequence[SourceCandidatePath],
        field: str,
    ) -> bool:
        return any(
            source_metadata_value(metadata, field) is not None
            for pattern in patterns
            for metadata in self.candidate_metadata(pattern)
        )


class SourceBindingCandidateMatcher:
    """Match source-binding selectors against candidate source paths."""

    @staticmethod
    def selector_bindings(
        bindings: Sequence[NamedSourceBinding],
    ) -> tuple[NamedSourceBinding, ...]:
        return tuple(
            binding
            for binding in bindings
            if binding.required and binding.requires_selector_resolution
        )

    @classmethod
    def candidate_represents_complete_source_set(
        cls,
        candidate: SourceCandidatePath,
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> bool:
        """Return whether one anchor resolves every required source alias."""

        required_bindings = tuple(binding for binding in bindings if binding.required)
        return bool(required_bindings) and all(
            cls.matches(
                candidate,
                binding=binding,
                source_context=source_context,
            )
            for binding in required_bindings
        )

    @classmethod
    def execution_anchor_bindings(
        cls,
        bindings: Sequence[NamedSourceBinding],
        *,
        source_context: SourcePatternResolutionContext,
    ) -> tuple[NamedSourceBinding, ...]:
        """Return declarations resolvable at the execution-anchor boundary."""

        resolvable_bindings = (
            tuple(binding for binding in bindings if binding.required)
            if source_context.source_projections_by_virtual_path
            else cls.selector_bindings(bindings)
        )
        return tuple(
            binding
            for binding in resolvable_bindings
            if binding.source_set_role is SourceSetRole.MATCHED
        )

    @staticmethod
    def matches(
        candidate: SourceCandidatePath,
        *,
        binding: NamedSourceBinding,
        source_context: SourcePatternResolutionContext,
    ) -> bool:
        if not source_context.candidate_matches_source_binding_projection(
            candidate,
            binding,
        ):
            return False
        selector = binding.selector
        if not any(
            source_filters_match(path, selector.filters)
            for path in source_context.candidate_filter_paths(candidate)
        ):
            return False

        if not selector.components and not selector.metadata:
            return True

        return selector.metadata_candidates_match(source_context.candidate_metadata(candidate))

    @classmethod
    def compatible_candidates(
        cls,
        candidates: Sequence[SourceCandidatePath],
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> tuple[SourceCandidatePath, ...]:
        projection_candidates = tuple(
            candidate
            for candidate in candidates
            if not bindings
            or any(
                source_context.candidate_matches_source_binding_projection(
                    candidate,
                    binding,
                )
                for binding in bindings
            )
        )
        selector_bindings = cls.selector_bindings(bindings)
        if not selector_bindings:
            return projection_candidates
        return tuple(
            candidate
            for candidate in projection_candidates
            if any(
                cls.matches(
                    candidate,
                    binding=binding,
                    source_context=source_context,
                )
                for binding in selector_bindings
            )
        )


class SourceAnchorSelectionStatus(str, Enum):
    """Outcome of source-bound execution-anchor resolution."""

    SELECTED = "selected"
    DEFERRED_TO_RUNTIME = "deferred_to_runtime"


@dataclass(frozen=True, slots=True)
class SourceAnchorPatternSelection:
    """Resolved source-compatible anchors plus the authority that owns them."""

    patterns: tuple[SourceCandidatePath, ...]
    status: SourceAnchorSelectionStatus
    reason: str

    @classmethod
    def selected(
        cls,
        patterns: Sequence[SourceCandidatePath],
        *,
        reason: str = "source selectors resolved at anchor boundary",
    ) -> "SourceAnchorPatternSelection":
        return cls(
            patterns=tuple(patterns),
            status=SourceAnchorSelectionStatus.SELECTED,
            reason=reason,
        )

    @classmethod
    def deferred_to_runtime(
        cls,
        patterns: Sequence[SourceCandidatePath],
        *,
        reason: str,
    ) -> "SourceAnchorPatternSelection":
        return cls(
            patterns=tuple(patterns),
            status=SourceAnchorSelectionStatus.DEFERRED_TO_RUNTIME,
            reason=reason,
        )

    @property
    def owns_runtime_resolution(self) -> bool:
        return self.status is SourceAnchorSelectionStatus.DEFERRED_TO_RUNTIME


@dataclass(frozen=True, slots=True)
class SourceWorkspaceAnchorNarrowing:
    """Contract for partial anchors materialized from a virtual source workspace."""

    source_context: SourcePatternResolutionContext
    compatible_count: int
    alias_count: int

    def allows_runtime_completion(self) -> bool:
        return (
            self.source_context.has_virtual_source_workspace
            and 0 < self.compatible_count < self.alias_count
        )


class SourceBindingMatchResolutionStatus(str, Enum):
    """Outcome of matching one anchor pattern to source-binding aliases."""

    MATCHED = "matched"
    DEFERRED_TO_RUNTIME = "deferred_to_runtime"


@dataclass(frozen=True, slots=True)
class SourceBindingMatchResolution:
    """Alias match result for one source-bound anchor pattern."""

    status: SourceBindingMatchResolutionStatus
    binding: NamedSourceBinding | None
    reason: str

    @classmethod
    def matched(
        cls,
        binding: NamedSourceBinding,
    ) -> "SourceBindingMatchResolution":
        return cls(
            status=SourceBindingMatchResolutionStatus.MATCHED,
            binding=binding,
            reason="exactly one selector binding matched the anchor",
        )

    @classmethod
    def deferred_to_runtime(
        cls,
        *,
        reason: str,
    ) -> "SourceBindingMatchResolution":
        return cls(
            status=SourceBindingMatchResolutionStatus.DEFERRED_TO_RUNTIME,
            binding=None,
            reason=reason,
        )

    def require_binding(self) -> NamedSourceBinding:
        if self.binding is None:
            raise RuntimeError(
                f"Source binding resolution was deferred to runtime: {self.reason}."
            )
        return self.binding

    @property
    def owns_runtime_resolution(self) -> bool:
        return self.status is SourceBindingMatchResolutionStatus.DEFERRED_TO_RUNTIME


class SourceBoundAnchorPatternPolicy(ABC, metaclass=AutoRegisterMeta):
    """Nominal policy for choosing execution anchors from source-bound inputs."""

    __registry_key__ = "policy_key"
    __skip_if_no_key__ = True
    policy_key: ClassVar[str | None] = None

    def __init__(self, match_plan: SourceBindingMatchPlan | None = None) -> None:
        self._match_plan = match_plan

    @classmethod
    def for_plan(
        cls,
        plan: CompiledSourceBindingPlan,
    ) -> "SourceBoundAnchorPatternPolicy":
        if plan.match_plan is None:
            return DefaultSourceBoundAnchorPatternPolicy()
        policy_type = cls.__registry__.get(
            plan.match_plan.method.value,
            DefaultSourceBoundAnchorPatternPolicy,
        )
        return policy_type(plan.match_plan)

    @abstractmethod
    def select(
        self,
        pattern_list: Sequence[SourceCandidatePath],
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> list[SourceCandidatePath]:
        """Return source-compatible anchor patterns for one execution group."""

    def _source_compatible_anchor_selection(
        self,
        pattern_list: Sequence[SourceCandidatePath],
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> SourceAnchorPatternSelection:
        anchor_bindings = self._anchor_bindings(
            bindings,
            source_context=source_context,
        )
        if not anchor_bindings:
            return SourceAnchorPatternSelection.selected(
                pattern_list,
                reason="no selector bindings participate in execution anchoring",
            )

        compatible = [
            pattern
            for pattern in pattern_list
            if any(
                self._pattern_matches_source_binding(
                    pattern,
                    binding=binding,
                    source_context=source_context,
                )
                for binding in anchor_bindings
            )
        ]
        if compatible:
            return SourceAnchorPatternSelection.selected(compatible)
        if self._metadata_selector_fields_are_unavailable(
            pattern_list,
            bindings=anchor_bindings,
            source_context=source_context,
        ):
            return SourceAnchorPatternSelection.deferred_to_runtime(
                pattern_list,
                reason=(
                    "selector metadata fields are unavailable at the execution "
                    "anchor boundary"
                ),
            )
        if self._file_selector_paths_are_unavailable(
            bindings=anchor_bindings,
            source_context=source_context,
        ):
            return SourceAnchorPatternSelection.deferred_to_runtime(
                pattern_list,
                reason=(
                    "selector file paths are unavailable at the execution "
                    "anchor boundary"
                ),
            )
        return SourceAnchorPatternSelection.selected(
            (),
            reason="source selectors resolved no compatible anchor patterns",
        )

    @staticmethod
    def _metadata_selector_fields_are_unavailable(
        pattern_list: Sequence[SourceCandidatePath],
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> bool:
        metadata_fields = tuple(
            selector.field
            for binding in bindings
            for selector in binding.selector.metadata
        )
        return bool(metadata_fields) and not any(
            source_context.has_metadata_field(pattern_list, field)
            for field in metadata_fields
        )

    @staticmethod
    def _file_selector_paths_are_unavailable(
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> bool:
        return not source_context.has_virtual_source_workspace and any(
            binding.selector.filters for binding in bindings
        )

    @staticmethod
    def _selector_bindings(
        bindings: Sequence[NamedSourceBinding],
    ) -> tuple[NamedSourceBinding, ...]:
        return SourceBindingCandidateMatcher.selector_bindings(bindings)

    @staticmethod
    def _anchor_bindings(
        bindings: Sequence[NamedSourceBinding],
        *,
        source_context: SourcePatternResolutionContext,
    ) -> tuple[NamedSourceBinding, ...]:
        return SourceBindingCandidateMatcher.execution_anchor_bindings(
            bindings,
            source_context=source_context,
        )

    @staticmethod
    def _pattern_matches_source_binding(
        pattern: SourceCandidatePath,
        *,
        binding: NamedSourceBinding,
        source_context: SourcePatternResolutionContext,
    ) -> bool:
        return SourceBindingCandidateMatcher.matches(
            pattern,
            binding=binding,
            source_context=source_context,
        )


class DefaultSourceBoundAnchorPatternPolicy(SourceBoundAnchorPatternPolicy):
    """Keep every selector-compatible source anchor."""

    def select(
        self,
        pattern_list: Sequence[SourceCandidatePath],
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> list[SourceCandidatePath]:
        selection = self._source_compatible_anchor_selection(
            pattern_list,
            bindings=bindings,
            source_context=source_context,
        )
        return list(selection.patterns)


class MatchedImageSetAnchorPatternPolicy(SourceBoundAnchorPatternPolicy):
    """Collapse multi-alias source anchors to one representative per image set."""

    policy_key = None

    def select(
        self,
        pattern_list: Sequence[SourceCandidatePath],
        *,
        bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> list[SourceCandidatePath]:
        selection = self._source_compatible_anchor_selection(
            pattern_list,
            bindings=bindings,
            source_context=source_context,
        )
        compatible = list(selection.patterns)
        anchor_bindings = self._anchor_bindings(
            bindings,
            source_context=source_context,
        )
        if len(anchor_bindings) < 2:
            return compatible

        complete_source_set_anchors = tuple(
            pattern
            for pattern in compatible
            if SourceBindingCandidateMatcher.candidate_represents_complete_source_set(
                pattern,
                bindings=anchor_bindings,
                source_context=source_context,
            )
        )
        if complete_source_set_anchors:
            if len(complete_source_set_anchors) != len(compatible):
                raise ValueError(
                    "Matched source binding anchors mix complete source-set "
                    "templates with individual source-alias candidates."
                )
            return list(complete_source_set_anchors)

        return self._deduplicate_matched_image_sets(
            compatible,
            selector_bindings=anchor_bindings,
            source_context=source_context,
        )

    @abstractmethod
    def _deduplicate_matched_image_sets(
        self,
        compatible: Sequence[SourceCandidatePath],
        *,
        selector_bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> list[SourceCandidatePath]:
        """Return one execution anchor per matched image set."""


class OrderMatchedImageSetAnchorPatternPolicy(MatchedImageSetAnchorPatternPolicy):
    """Source aliases are paired by order within one logical image set."""

    policy_key = SourceBindingMatchMethod.ORDER.value

    def _deduplicate_matched_image_sets(
        self,
        compatible: Sequence[SourceCandidatePath],
        *,
        selector_bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> list[SourceCandidatePath]:
        alias_count = len(selector_bindings)
        if len(compatible) % alias_count:
            if SourceWorkspaceAnchorNarrowing(
                source_context=source_context,
                compatible_count=len(compatible),
                alias_count=alias_count,
            ).allows_runtime_completion():
                return list(compatible)
            raise ValueError(
                "ORDER source binding produced an incomplete image set: "
                f"{len(compatible)} source anchors for {alias_count} aliases."
            )
        return [
            pattern
            for index, pattern in enumerate(compatible)
            if index % alias_count == 0
        ]


class MetadataMatchedImageSetAnchorPatternPolicy(MatchedImageSetAnchorPatternPolicy):
    """Source aliases are paired by declared metadata dimensions."""

    policy_key = SourceBindingMatchMethod.METADATA.value

    def _deduplicate_matched_image_sets(
        self,
        compatible: Sequence[SourceCandidatePath],
        *,
        selector_bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> list[SourceCandidatePath]:
        if self._match_plan is None or not self._match_plan.dimensions:
            raise ValueError(
                "METADATA source binding requires explicit match dimensions "
                "to collapse source-bound execution anchors."
            )

        deduplicated: list[SourceCandidatePath] = []
        seen: set[tuple[str, ...]] = set()
        for pattern in compatible:
            metadata = source_context.candidate_metadata(pattern).first_required(
                pattern
            )
            binding = self._matching_binding(
                pattern,
                selector_bindings=selector_bindings,
                source_context=source_context,
            )
            if binding.owns_runtime_resolution:
                return list(compatible)
            key = self._metadata_image_set_key(
                metadata,
                binding=binding.require_binding(),
                allow_missing=source_context.has_virtual_source_workspace,
            )
            if key is None:
                return list(compatible)
            if key in seen:
                continue
            seen.add(key)
            deduplicated.append(pattern)
        return deduplicated

    def _matching_binding(
        self,
        pattern: SourceCandidatePath,
        *,
        selector_bindings: Sequence[NamedSourceBinding],
        source_context: SourcePatternResolutionContext,
    ) -> SourceBindingMatchResolution:
        matches = tuple(
            binding
            for binding in selector_bindings
            if self._pattern_matches_source_binding(
                pattern,
                binding=binding,
                source_context=source_context,
            )
        )
        if len(matches) > 1 and source_context.has_virtual_source_workspace:
            return SourceBindingMatchResolution.matched(matches[0])
        if len(matches) == 0 and source_context.has_virtual_source_workspace:
            return SourceBindingMatchResolution.deferred_to_runtime(
                reason=(
                    "virtual source workspace did not expose enough selector "
                    "metadata to bind this anchor to one alias"
                )
            )
        if len(matches) != 1:
            raise ValueError(
                "METADATA source binding expected exactly one alias match for "
                f"{pattern!s}, got {len(matches)}."
            )
        return SourceBindingMatchResolution.matched(matches[0])

    def _metadata_image_set_key(
        self,
        metadata: SourceMetadataMapping,
        *,
        binding: NamedSourceBinding,
        allow_missing: bool = False,
    ) -> tuple[str, ...] | None:
        if self._match_plan is None:
            raise ValueError("METADATA source binding policy has no match plan.")
        values: list[str] = []
        for dimension in self._match_plan.dimensions:
            field = dimension.field_for_alias(binding.alias)
            if field is None:
                raise ValueError(
                    "METADATA source binding dimension is missing alias "
                    f"{binding.alias!r}."
                )
            value = source_metadata_value(metadata, field)
            if value is None:
                if allow_missing:
                    return None
                raise ValueError(
                    "METADATA source binding could not read match field "
                    f"{field!r} for alias {binding.alias!r}."
                )
            values.append(value)
        return tuple(values)


class SourceIdentityResolutionContext(SourcePatternResolutionContext):
    """Resolve exact provenance identities through declared source paths and metadata."""

    __slots__ = ()

    def _candidate_matches_source_identity(
        self,
        candidate: SourceCandidatePath,
        source_identity: SourceImageIdentity,
    ) -> bool:
        """Return whether one candidate has the exact declared source identity."""

        if not source_identity.addressable:
            return False
        if source_identity.path is not None:
            declared_paths = self._identity_paths_for_candidate(candidate)
            if not any(
                source_paths_equal(declared_path, source_identity.path)
                for declared_path in declared_paths
            ):
                return False
        component_items = source_component_metadata_items(
            source_identity.component_metadata or {}
        )
        if not component_items:
            return source_identity.path is not None
        return any(
            all(
                (
                    candidate_value := source_component_metadata_value(
                        metadata, component
                    )
                )
                is not None
                and source_metadata_values_equal(candidate_value, expected_value)
                for component, expected_value in component_items
            )
            for metadata in self.candidate_metadata(candidate)
        )

    def _identity_paths_for_candidate(
        self,
        candidate: SourceCandidatePath,
    ) -> tuple[str, ...]:
        return (
            self.source_path_for(candidate),
            *self.runtime_paths_for_candidate(candidate),
        )

    def matching_candidates_for_source_identities(
        self,
        identities: Sequence[SourceImageIdentity],
        candidates: Sequence[SourceCandidatePath],
    ) -> tuple[tuple[SourceCandidatePath, ...], ...]:
        """Resolve a batch without rescanning unrelated paths for each identity."""

        if self.resolution_snapshot is not None:
            return self.resolution_snapshot.matching_candidates_for_source_identities(
                identities, candidates,
            )

        candidates = self.declared_positions_for_candidates(candidates)
        candidates_by_path: dict[str, list[SourceCandidatePath]] = {}
        for candidate in candidates:
            path_keys = dict.fromkeys(
                source_path_identity_key(path)
                for path in self._identity_paths_for_candidate(candidate)
            )
            for path_key in path_keys:
                candidates_by_path.setdefault(path_key, []).append(candidate)
        matches_by_identity: list[tuple[SourceCandidatePath, ...]] = []
        for identity in identities:
            identity_path = identity.path
            identity_candidates = (
                candidates
                if identity_path is None
                else candidates_by_path.get(source_path_identity_key(identity_path), ())
            )
            matches_by_identity.append(
                tuple(
                    candidate
                    for candidate in identity_candidates
                    if self._candidate_matches_source_identity(candidate, identity)
                )
            )
        return tuple(matches_by_identity)


@dataclass(frozen=True, slots=True, kw_only=True)
class SourceBindingMatchedImageSet(SourceIdentityResolutionContext):
    """Resolve all declared source aliases for one matched image-set anchor."""

    bindings: tuple[NamedSourceBinding, ...]
    match_plan: SourceBindingMatchPlan | None
    identity_policy: SourceImageSetIdentityPolicy

    @property
    def matched_bindings(self) -> tuple[NamedSourceBinding, ...]:
        """Return declarations that determine source-set cardinality."""

        return tuple(
            binding
            for binding in self.bindings
            if binding.source_set_role is SourceSetRole.MATCHED
        )

    @classmethod
    def from_plan(
        cls,
        *,
        bindings: Sequence[NamedSourceBinding],
        match_plan: SourceBindingMatchPlan | None,
        source_context: SourcePatternResolutionContext,
        identity_policy: SourceImageSetIdentityPolicy,
    ) -> "SourceBindingMatchedImageSet":
        return cls(
            parser=source_context.parser,
            source_paths_by_virtual_path=source_context.source_paths_by_virtual_path,
            source_metadata_by_path=source_context.source_metadata_by_path,
            metadata_rules=source_context.metadata_rules,
            source_projections_by_virtual_path=(
                source_context.source_projections_by_virtual_path
            ),
            resolution_snapshot=source_context.resolution_snapshot,
            bindings=tuple(bindings),
            match_plan=match_plan,
            identity_policy=identity_policy,
        )

    def expand(
        self,
        anchors: Sequence[SourceCandidatePath],
        *,
        source_universe: Sequence[SourceCandidatePath],
    ) -> tuple[SourceCandidatePath, ...]:
        """Return source files for every alias in each selected image-set anchor."""
        selector_bindings = SourceBindingCandidateMatcher.selector_bindings(
            self.matched_bindings
        )
        resolution_bindings = (
            self.matched_bindings
            if self.source_projections_by_virtual_path
            else selector_bindings
        )
        if len(resolution_bindings) == 1:
            return self._expand_single_alias(
                anchors,
                binding=resolution_bindings[0],
                source_universe=source_universe,
            )
        if (
            self.match_plan is None
            or self.match_plan.method is not SourceBindingMatchMethod.METADATA
            or not self.match_plan.dimensions
        ):
            selected = self._complete_alias_set(anchors, resolution_bindings)
            if selected is not None:
                return selected
            return tuple(
                dict.fromkeys(
                    candidate
                    for binding in resolution_bindings
                    for candidate in self._expand_single_alias(
                        anchors,
                        binding=binding,
                        source_universe=source_universe,
                    )
                )
            )

        selected_anchor_candidates = self._complete_alias_set(
            anchors, resolution_bindings
        )
        if selected_anchor_candidates is not None:
            return selected_anchor_candidates

        expanded: list[SourceCandidatePath] = []
        for anchor in anchors:
            anchor_binding = self._matching_binding(
                anchor,
                selector_bindings=resolution_bindings,
            )
            if anchor_binding is None:
                continue
            expanded.extend(
                self._expand_anchor(
                    anchor,
                    anchor_binding=anchor_binding,
                    selector_bindings=resolution_bindings,
                    source_universe=source_universe,
                )
            )
        if not expanded:
            return SourceBindingCandidateMatcher.compatible_candidates(
                anchors,
                bindings=resolution_bindings,
                source_context=self,
            )
        return tuple(dict.fromkeys(expanded))

    def members_for_binding(
        self,
        binding: NamedSourceBinding,
        *,
        anchor_provenance: SourceImageProvenance,
        source_universe: Sequence[SourceCandidatePath],
    ) -> tuple[SourceCandidatePath, ...]:
        """Resolve one binding's exact members in the current source image sets."""

        if binding not in self.bindings:
            raise ValueError(
                f"Source binding {binding.alias!r} is not declared by this image set."
            )
        anchor_identities = anchor_provenance.represented_source_identities
        if not anchor_identities:
            raise ValueError(
                "Exact source-binding membership requires addressable runtime "
                "provenance."
            )
        candidates = SourceBindingCandidateMatcher.compatible_candidates(
            source_universe,
            bindings=(binding,),
            source_context=self,
        )
        if not candidates:
            return ()
        declared_candidates = tuple(
            dict.fromkeys((*self.source_paths_by_virtual_path, *source_universe))
        )
        anchors: list[SourceCandidatePath] = []
        matches_by_identity = self.matching_candidates_for_source_identities(
            anchor_identities,
            declared_candidates,
        )
        for anchor_identity, matches in zip(anchor_identities, matches_by_identity):
            if len(matches) != 1:
                raise ValueError(
                    "Source binding requires one exact declared source-set position "
                    f"for runtime provenance {anchor_identity.identity!r}, got "
                    f"{matches!r}."
                )
            anchors.append(matches[0])
        return self._expand_single_alias(
            tuple(dict.fromkeys(anchors)),
            binding=binding,
            source_universe=source_universe,
            compatible_source_candidates=candidates,
        )

    def _expand_single_alias(
        self,
        anchors: Sequence[SourceCandidatePath],
        *,
        binding: NamedSourceBinding,
        source_universe: Sequence[SourceCandidatePath],
        compatible_source_candidates: Sequence[SourceCandidatePath] | None = None,
    ) -> tuple[SourceCandidatePath, ...]:
        compatible_anchors = SourceBindingCandidateMatcher.compatible_candidates(
            anchors,
            bindings=(binding,),
            source_context=self,
        )
        if compatible_anchors:
            return compatible_anchors
        if not source_universe:
            return ()

        anchor_identities = frozenset(
            self._source_image_set_identity(anchor) for anchor in anchors
        )
        if compatible_source_candidates is None:
            compatible_source_candidates = (
                SourceBindingCandidateMatcher.compatible_candidates(
                    source_universe,
                    bindings=(binding,),
                    source_context=self,
                )
            )
        return tuple(
            candidate
            for candidate in compatible_source_candidates
            if SourceImageSetIdentityCompatibility.any_match(
                frozenset((self._source_image_set_identity(candidate),)),
                anchor_identities,
            )
        )

    def _source_image_set_identity(
        self,
        candidate: SourceCandidatePath,
    ) -> SourceImageSetIdentity:
        metadata_candidates = self.candidate_metadata(candidate)
        metadata = (
            metadata_candidates.values[0]
            if metadata_candidates.values
            else DeclaredSourceMetadataRecord(())
        )
        return SourceImageSetIdentity.from_metadata(
            metadata,
            fallback_source_path=self.source_path_for(candidate),
            policy=self.identity_policy,
        )

    def _expand_anchor(
        self,
        anchor: SourceCandidatePath,
        *,
        anchor_binding: NamedSourceBinding,
        selector_bindings: tuple[NamedSourceBinding, ...],
        source_universe: Sequence[SourceCandidatePath],
    ) -> tuple[SourceCandidatePath, ...]:
        anchor_metadata = self.candidate_metadata(anchor).first_required(anchor)
        anchor_values = self._dimension_values(
            anchor_metadata,
            anchor_binding,
            allow_missing=self.has_virtual_source_workspace,
        )
        if anchor_values is None:
            return tuple(
                dict.fromkeys(
                    candidate
                    for binding in selector_bindings
                    for candidate in self._expand_single_alias(
                        (anchor,),
                        binding=binding,
                        source_universe=source_universe,
                    )
                )
            )
        if not anchor_values:
            raise ValueError(
                "Matched source image-set anchor lacks metadata declared by the "
                f"match plan: {anchor!s}."
            )

        selected: list[SourceCandidatePath] = []
        for binding in selector_bindings:
            matches = tuple(
                candidate
                for candidate in source_universe
                if self._candidate_matches_anchor_set(
                    candidate,
                    binding=binding,
                    anchor_values=anchor_values,
                )
            )
            if len(matches) != 1:
                raise ValueError(
                    "Matched source image set expected exactly one candidate for "
                    f"alias {binding.alias!r} anchored by {anchor!s}, got "
                    f"{len(matches)}."
                )
            selected.append(matches[0])
        return tuple(selected)

    def _complete_alias_set(
        self,
        candidates: Sequence[SourceCandidatePath],
        selector_bindings: tuple[NamedSourceBinding, ...],
    ) -> tuple[SourceCandidatePath, ...] | None:
        if not selector_bindings:
            return None
        selected: list[SourceCandidatePath] = []
        for binding in selector_bindings:
            matches = tuple(
                candidate
                for candidate in candidates
                if SourceBindingCandidateMatcher.matches(
                    candidate,
                    binding=binding,
                    source_context=self,
                )
            )
            if len(matches) != 1:
                return None
            selected.append(matches[0])
        return tuple(dict.fromkeys(selected))

    def _matching_binding(
        self,
        candidate: SourceCandidatePath,
        *,
        selector_bindings: tuple[NamedSourceBinding, ...],
    ) -> NamedSourceBinding | None:
        matches = tuple(
            binding
            for binding in selector_bindings
            if SourceBindingCandidateMatcher.matches(
                candidate,
                binding=binding,
                source_context=self,
            )
        )
        if not matches:
            return None
        if len(matches) != 1:
            raise ValueError(
                "Matched source image-set anchor must resolve to exactly one "
                f"source alias, got {len(matches)} for {candidate!s}."
            )
        return matches[0]

    def _candidate_matches_anchor_set(
        self,
        candidate: SourceCandidatePath,
        *,
        binding: NamedSourceBinding,
        anchor_values: Mapping[int, str],
    ) -> bool:
        if not SourceBindingCandidateMatcher.matches(
            candidate,
            binding=binding,
            source_context=self,
        ):
            return False
        metadata = self.candidate_metadata(candidate).first_required(candidate)
        candidate_values = self._dimension_values(
            metadata,
            binding,
            allow_missing=self.has_virtual_source_workspace,
        )
        if candidate_values is None:
            return False
        if not candidate_values:
            raise ValueError(
                f"Source alias {binding.alias!r} has no match-plan dimensions."
            )
        return all(
            anchor_values.get(dimension_index) == value
            for dimension_index, value in candidate_values.items()
        )

    def _dimension_values(
        self,
        metadata: SourceMetadataRecord,
        binding: NamedSourceBinding,
        *,
        allow_missing: bool = False,
    ) -> Mapping[int, str] | None:
        values: dict[int, str] = {}
        for dimension_index, dimension in enumerate(self.match_plan.dimensions):
            field = dimension.field_for_alias(binding.alias)
            if field is None:
                continue
            value = semantic_source_metadata_value(metadata, field)
            if value is None:
                if allow_missing:
                    return None
                raise ValueError(
                    "Source binding match plan could not read metadata field "
                    f"{field!r} for alias {binding.alias!r}."
                )
            values[dimension_index] = str(value)
        return MappingProxyType(values)


@dataclass(frozen=True, slots=True)
class SourceFileUniverse:
    """Concrete file universe plus the backend that names those files."""

    files: tuple[str, ...]
    backend: Backend

    def load_images(
        self,
        filemanager: "FileManager",
        *,
        zarr_config: Mapping[str, object] | None = None,
    ) -> list[RuntimeArrayData]:
        """Load this exact source cohort, retaining its execution-local memory copy."""
        if self.backend is Backend.MEMORY:
            return filemanager.load_batch(list(self.files), self.backend.value)
        missing = tuple(dict.fromkeys(
            path for path in self.files
            if not filemanager.exists(path, Backend.MEMORY.value)
        ))
        loaded_by_path = {}
        if missing:
            pixels = filemanager.load_batch(
                list(missing), self.backend.value,
                **({"zarr_config": zarr_config} if self.backend is Backend.ZARR else {}),
            )
            loaded_by_path.update(
                (path, ImagePayloadSourceMetadataContext(
                    SourceImageIdentity(path),
                    read_backend=self.backend.value,
                    filemanager=filemanager,
                ).payload(image))
                for path, image in zip(missing, pixels, strict=True)
            )
            for parent in dict.fromkeys(str(Path(path).parent) for path in missing):
                filemanager.ensure_directory(parent, Backend.MEMORY.value)
            filemanager.save_batch(
                list(loaded_by_path.values()), list(loaded_by_path), Backend.MEMORY.value,
            )
        retained = tuple(dict.fromkeys(
            path for path in self.files if path not in loaded_by_path
        ))
        if retained:
            loaded_by_path.update(zip(
                retained,
                filemanager.load_batch(list(retained), Backend.MEMORY.value),
                strict=True,
            ))
        return [loaded_by_path[path] for path in self.files]


@dataclass(frozen=True, slots=True)
class SourceUniverseRuntimeState:
    """Resolved source universes assembled from the registered request family."""

    load_universe: SourceFileUniverse | None = None
    source_metadata_by_path: Mapping[str, SourceMetadataMapping] = field(
        default_factory=lambda: MappingProxyType({})
    )

    def with_source_metadata(
        self,
        source_metadata_by_path: Mapping[str, SourceMetadataMapping],
    ) -> "SourceUniverseRuntimeState":
        if self.source_metadata_by_path is source_metadata_by_path:
            return self
        if not self.source_metadata_by_path:
            return replace(
                self,
                source_metadata_by_path=source_metadata_by_path,
            )
        if not source_metadata_by_path:
            return self
        merged = dict(self.source_metadata_by_path)
        merged.update(source_metadata_by_path)
        return replace(self, source_metadata_by_path=MappingProxyType(merged))

    def require_load_universe(self) -> SourceFileUniverse:
        if self.load_universe is None:
            raise RuntimeError("Source universe runtime state has no load universe.")
        return self.load_universe


@dataclass(frozen=True, slots=True)
class SourceUniverseRequest(metaclass=AutoRegisterMeta):
    """Plan-artifact request for source-binding runtime universe resolution."""

    __registry_key__ = "universe_request_kind"
    __skip_if_no_key__ = True

    universe_request_kind: ClassVar[str | None] = None
    context: "ProcessingContext"
    plan: "CompiledStepPlan"
    matching_files: tuple[str, ...]
    source_backend: Backend
    source_projection: VirtualWorkspaceSourceProjection | None

    @classmethod
    def from_context(
        cls,
        *,
        context: "ProcessingContext",
        plan: "CompiledStepPlan",
        matching_files: Sequence[str],
        source_projection: VirtualWorkspaceSourceProjection | None,
    ) -> "SourceUniverseRequest":
        if not isinstance(plan, CompiledStepPlan):
            raise TypeError(
                "SourceUniverseRequest requires CompiledStepPlan, got "
                f"{type(plan).__name__}."
            )
        plan.require_function_execution_ready()
        source_backend = Backend(
            context.microscope_handler.get_primary_backend(
                context.input_dir,
                context.filemanager,
            )
        )
        return cls(
            context=context,
            plan=plan,
            matching_files=tuple(matching_files),
            source_backend=source_backend,
            source_projection=source_projection,
        )

    @classmethod
    def source_artifact_payload(
        cls, request: RuntimeAdapterRequest, binding: NamedSourceBinding,
    ) -> object:
        """Resolve original source pixels in this origin's workspace universe."""

        ref = binding.input_spec().ref()
        source_payload = request.source_payload
        source_provenance = (
            None
            if source_payload is None
            else image_payload_metadata(source_payload).source_provenance
        )
        if source_provenance is not None and not source_provenance.has_values:
            raise ValueError(
                f"Source-bound artifact {ref!r} requires main-flow source provenance."
            )

        projection = request.context.runtime_source_workspace_projection_authority.projection_if_available(
            axis_id=request.axis_scope.axis_id,
        )
        if projection is None:
            raise ValueError(
                f"Source-bound artifact {ref!r} requires a virtual-workspace "
                "source projection."
            )
        source_context = (
            request.context.runtime_source_binding_context_cache.source_pattern_context(
                parser=request.context.microscope_handler.parser,
                projection=projection,
                metadata_rules=request.source_binding_plan.metadata_rules,
            )
        )
        matched_set = SourceBindingMatchedImageSet.from_plan(
            bindings=request.source_binding_plan.binding_declarations,
            match_plan=request.source_binding_plan.match_plan,
            source_context=source_context,
            identity_policy=request.context.source_image_set_identity_policy,
        )
        source_universe = tuple(
            dict.fromkeys(
                source_path
                for declared_binding in request.source_binding_plan.binding_declarations
                for source_path in projection.files_for_projection_role(
                    declared_binding.projection_role,
                    axis_id=request.axis_scope.axis_id,
                )
            )
        )
        members = matched_set.members_for_binding(
            binding,
            anchor_provenance=(
                source_provenance
                if source_provenance is not None
                else SourceImageProvenance()
            ),
            source_universe=source_universe,
        )
        if not members:
            raise ValueError(
                f"Source-bound artifact {ref!r} resolved no workspace members."
            )

        projected_payloads = projection.load_binding_payloads(
            members, binding=binding, filemanager=request.context.filemanager,
        )
        payload = (
            projected_payloads[0]
            if len(projected_payloads) == 1
            and image_payload_metadata(projected_payloads[0]).persists_whole_image()
            else stack_image_payloads(
                projected_payloads,
                metadata_mode=ImagePayloadMetadataCompositionMode.for_plane_axis(
                    RuntimePlaneAxis.RUNTIME_SLICE
                ),
            )
        )
        metadata = image_payload_metadata(payload)
        domain = request.source_binding_plan.source_spatial_domain.admit_source_cohort(
            metadata.source_spatial_domain,
            depth=len(members),
        )
        return metadata.replace_fields(source_spatial_domain=domain).attach_to(payload)

    @classmethod
    def for_binding(cls, binding: NamedSourceBinding) -> type[SourceUniverseRequest]:
        """Select the already registered owner of a binding's origin."""
        return cls.__registry__[binding.origin.value]

    def runtime_universe_state(self) -> SourceUniverseRuntimeState:
        """Return cached source-universe state for this request."""
        cache = self.context.runtime_source_binding_context_cache
        cached = cache.runtime_universe_state(
            plan=self.plan,
            matching_files=self.matching_files,
            source_backend=self.source_backend,
            source_projection=self.source_projection,
        )
        if cached is not None:
            return cached
        return cache.store_runtime_universe_state(
            SourceUniverseRequest.runtime_state(self),
            plan=self.plan,
            matching_files=self.matching_files,
            source_backend=self.source_backend,
            source_projection=self.source_projection,
        )

    @classmethod
    def registered_request_types(cls) -> tuple[type["SourceUniverseRequest"], ...]:
        """Return registered concrete runtime plan request classes."""
        request_types: list[type[SourceUniverseRequest]] = []
        for request_type in cls.__registry__.values():
            if issubclass(request_type, cls) and request_type not in request_types:
                request_types.append(request_type)
        return tuple(request_types)

    @classmethod
    def from_request(
        cls,
        request: "SourceUniverseRequest",
    ) -> "SourceUniverseRequest":
        """Build a registered source-universe role from its parent request."""
        return cls(
            context=request.context,
            plan=request.plan,
            matching_files=request.matching_files,
            source_backend=request.source_backend,
            source_projection=request.source_projection,
        )

    @classmethod
    def runtime_state(
        cls,
        request: "SourceUniverseRequest",
    ) -> SourceUniverseRuntimeState:
        """Resolve every registered source-universe request into runtime state."""
        state = SourceUniverseRuntimeState()
        for request_type in cls.registered_request_types():
            universe_request = request_type.from_request(request)
            universe = universe_request.source_universe()
            state = universe_request.contribute_runtime_state(state, universe)
        return state

    def source_universe(self) -> SourceFileUniverse:
        """Resolve current-axis files through their declared source backend."""
        return SourceFileUniverse(
            files=(
                self.require_source_projection().pipeline_start_files(
                    axis_id=self.plan.axis_id,
                )
                if self.uses_virtual_workspace_projection
                else self.axis_files()
            ),
            backend=self.source_backend,
        )

    def contribute_runtime_state(
        self,
        state: SourceUniverseRuntimeState,
        universe: SourceFileUniverse,
    ) -> SourceUniverseRuntimeState:
        """Contribute resolved metadata to runtime state."""
        return state.with_source_metadata(self.source_metadata_by_universe(universe))

    @property
    def requires_step_input_selector_resolution(self) -> bool:
        return self.plan.source_universe_plan.requires_step_input_selector_resolution

    @property
    def uses_virtual_workspace_projection(self) -> bool:
        return (
            self.source_backend is Backend.VIRTUAL_WORKSPACE
            and self.source_projection is not None
        )

    @property
    def uses_pipeline_start_binding_origin(self) -> bool:
        return self.plan.source_universe_plan.uses_pipeline_start_binding_origin

    @property
    def source_metadata_by_path(self) -> Mapping[str, SourceMetadataMapping]:
        projection = self.source_projection
        if projection is None:
            return MappingProxyType({})
        return projection.source_metadata_by_path

    def source_context(self) -> SourcePatternResolutionContext:
        metadata_rules = self.plan.source_binding_plan.metadata_rules
        if self.source_projection is not None:
            return self.context.runtime_source_binding_context_cache.source_pattern_context(
                parser=self.context.microscope_handler.parser,
                projection=self.source_projection,
                metadata_rules=metadata_rules,
            )
        return SourcePatternResolutionContext.from_sources(
            parser=self.context.microscope_handler.parser,
            source_paths_by_virtual_path={},
            metadata_rules=metadata_rules,
        )

    def source_metadata_by_universe(
        self,
        universe: SourceFileUniverse,
    ) -> Mapping[str, SourceMetadataMapping]:
        if self.source_projection is not None:
            return self.source_projection.source_metadata_by_path
        return self.source_context().source_metadata_by_paths(universe.files)

    def require_source_projection(self) -> VirtualWorkspaceSourceProjection:
        projection = self.source_projection
        if projection is None:
            raise RuntimeError(
                "Virtual workspace source universe requires projection metadata."
            )
        return projection

    def axis_files(self) -> tuple[str, ...]:
        return tuple(
            get_all_image_paths(
                input_dir=self.context.input_dir,
                axis_id=self.plan.axis_id,
                backend=self.source_backend.value,
                filemanager=self.context.filemanager,
                microscope_handler=self.context.microscope_handler,
            )
        )


@dataclass(frozen=True, slots=True)
class StepInputSourceUniverseRequest(SourceUniverseRequest):
    """Request for the source universe represented by the current step input."""

    universe_request_kind = "step_input"

    @classmethod
    def source_artifact_payload(
        cls, request: RuntimeAdapterRequest, binding: NamedSourceBinding,
    ) -> object:
        """Resolve primary planes from current pixels; companions from source."""
        if not binding.requires_current_pixels:
            return SourceUniverseRequest.source_artifact_payload(request, binding)
        if request.source_payload is None:
            raise ValueError(f"STEP_INPUT binding {binding.alias!r} requires current pixels.")
        return binding.project_step_input_payload(request.source_payload)

    def source_universe(self) -> SourceFileUniverse:
        """Expand source selectors; otherwise retain the selected pattern files."""
        if not self.requires_step_input_selector_resolution:
            return SourceFileUniverse(self.matching_files, self.source_backend)
        return SourceUniverseRequest.source_universe(self)

    def contribute_runtime_state(
        self,
        state: SourceUniverseRuntimeState,
        universe: SourceFileUniverse,
    ) -> SourceUniverseRuntimeState:
        state = replace(
            state,
            load_universe=state.load_universe or universe,
        )
        return SourceUniverseRequest.contribute_runtime_state(self, state, universe)


@dataclass(frozen=True, slots=True)
class PipelineStartSourceUniverseRequest(SourceUniverseRequest):
    """Request for the source universe represented by the pipeline start."""

    universe_request_kind = "pipeline_start"

    def contribute_runtime_state(
        self,
        state: SourceUniverseRuntimeState,
        universe: SourceFileUniverse,
    ) -> SourceUniverseRuntimeState:
        load_universe = self.load_universe()
        state = replace(
            state,
            load_universe=(
                state.load_universe if load_universe is None else load_universe
            ),
        )
        return SourceUniverseRequest.contribute_runtime_state(self, state, universe)

    def load_universe(self) -> SourceFileUniverse | None:
        projection = self.source_projection
        if projection is None:
            return None
        if not self.uses_pipeline_start_binding_origin:
            return None
        return SourceFileUniverse(
            files=projection.pipeline_start_files(axis_id=self.plan.axis_id),
            backend=self.source_backend,
        )
