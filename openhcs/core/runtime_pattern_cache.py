"""Execution-local cache for immutable pipeline-start pattern discovery."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Hashable, TYPE_CHECKING

from openhcs.constants.constants import AllComponents
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.function_patterns import FunctionGroupKey
from openhcs.core.source_binding_selection import SourceCandidatePath

if TYPE_CHECKING:
    from openhcs.microscopes.microscope_interfaces import FilenameParser

DiscoveredPatternCollection = (
    Sequence[SourceCandidatePath]
    | Mapping[FunctionGroupKey, Sequence[SourceCandidatePath]]
)


@dataclass(frozen=True, slots=True)
class RuntimePatternDiscoveryCacheKey:
    """Identity for pattern discovery over an immutable source-file universe."""

    axis_id: str
    source_files: tuple[str, ...]
    group_by: str | None
    variable_components: tuple[str, ...]

    @classmethod
    def from_source_files(
        cls,
        *,
        axis_id: str,
        source_files: Sequence[str],
        group_by: str | None,
        variable_components: Sequence[str],
    ) -> "RuntimePatternDiscoveryCacheKey":
        if not axis_id:
            raise ValueError("Runtime pattern cache axis_id cannot be empty.")
        if not source_files:
            raise ValueError("Runtime pattern cache source_files cannot be empty.")
        return cls(
            axis_id=str(axis_id),
            source_files=tuple(str(source_file) for source_file in source_files),
            group_by=None if group_by is None else str(group_by),
            variable_components=tuple(
                str(component) for component in variable_components
            ),
        )


@dataclass(frozen=True, slots=True)
class FrozenAxisPatternCollection:
    """Immutable pattern collection for one multiprocessing axis."""

    patterns: tuple[SourceCandidatePath, ...] = ()
    grouped_patterns: tuple[
        tuple[FunctionGroupKey, tuple[SourceCandidatePath, ...]], ...
    ] = ()

    @classmethod
    def from_collection(
        cls,
        collection: DiscoveredPatternCollection,
    ) -> "FrozenAxisPatternCollection":
        if isinstance(collection, Mapping):
            return cls(
                grouped_patterns=tuple(
                    (
                        group_key,
                        tuple(str(pattern) for pattern in pattern_list),
                    )
                    for group_key, pattern_list in collection.items()
                )
            )
        return cls(patterns=tuple(str(pattern) for pattern in collection))

    def thaw(self) -> DiscoveredPatternCollection:
        if self.grouped_patterns:
            return {
                group_key: list(patterns)
                for group_key, patterns in self.grouped_patterns
            }
        return list(self.patterns)


@dataclass(frozen=True, slots=True)
class FrozenPatternDiscoveryResult:
    """Immutable pattern-discovery result keyed by axis id."""

    patterns_by_axis: tuple[tuple[str, FrozenAxisPatternCollection], ...]

    @classmethod
    def from_patterns_by_axis(
        cls,
        patterns_by_axis: Mapping[str, DiscoveredPatternCollection],
    ) -> "FrozenPatternDiscoveryResult":
        return cls(
            tuple(
                (
                    str(axis_id),
                    FrozenAxisPatternCollection.from_collection(patterns),
                )
                for axis_id, patterns in patterns_by_axis.items()
            )
        )

    def thaw(self) -> dict[str, DiscoveredPatternCollection]:
        return {axis_id: patterns.thaw() for axis_id, patterns in self.patterns_by_axis}


@dataclass(slots=True)
class RuntimePatternDiscoveryCache:
    """Processing-context-local cache for pipeline-start source pattern discovery."""

    patterns: dict[
        RuntimePatternDiscoveryCacheKey,
        FrozenPatternDiscoveryResult,
    ] = field(default_factory=dict)

    filename_metadata: dict[
        tuple["FilenameParser", tuple[Hashable, ...], str],
        FilenameParseResult | None,
    ] = field(default_factory=dict)
    filenames_by_component: dict[
        tuple["FilenameParser", tuple[Hashable, ...], AllComponents, str], set[str],
    ] = field(default_factory=dict)

    def metadata_for_filename(
        self, parser: "FilenameParser", filename: str,
    ) -> FilenameParseResult | None:
        """Own each filename result under its actual parser semantics."""
        semantics = parser.semantic_identity()
        key = (parser, semantics, filename)
        if key not in self.filename_metadata:
            metadata = parser.parse_filename(filename)
            self.filename_metadata[key] = metadata
            if metadata is not None:
                for component, value in metadata.declared_values():
                    self.filenames_by_component.setdefault(
                        (parser, semantics, component, str(value)), set(),
                    ).add(filename)
        return self.filename_metadata[key]

    def files_for_component(
        self,
        parser: "FilenameParser",
        files: Sequence[str],
        component: AllComponents,
        value: object,
    ) -> list[str]:
        """Select component membership from the admitted filename inventory."""
        names = tuple(Path(path).name for path in files)
        members = self.filenames_by_component.get(
            (parser, parser.semantic_identity(), component, str(value)), (),
        )
        return [
            path for path, name in zip(files, names, strict=True) if name in members
        ]

    def get(
        self,
        key: RuntimePatternDiscoveryCacheKey,
    ) -> dict[str, DiscoveredPatternCollection] | None:
        cached = self.patterns.get(key)
        if cached is None:
            return None
        return cached.thaw()

    def store(
        self,
        key: RuntimePatternDiscoveryCacheKey,
        patterns_by_axis: Mapping[str, DiscoveredPatternCollection],
    ) -> None:
        self.patterns[key] = FrozenPatternDiscoveryResult.from_patterns_by_axis(
            patterns_by_axis
        )
