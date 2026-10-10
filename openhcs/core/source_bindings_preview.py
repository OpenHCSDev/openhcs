"""Previews of source-binding declarations against a concrete source inventory."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path

from openhcs.core.source_binding_workspace import (
    SourceSetAssembler,
    SourceBindingWorkspaceProjector,
    SourceCandidate,
    _SourceSet,
)
from openhcs.core.source_metadata import SourceMetadataValue
from openhcs.core.source_bindings import (
    EMPTY_SOURCE_BINDINGS,
    NamedSourceBinding,
    SourceBindingsConfig,
    StepSourceBindingsConfig,
)
from openhcs.core.vfs_protocol import FileManagerLike


def _active_source_bindings(
    source_bindings: SourceBindingsConfig,
    step_bindings: StepSourceBindingsConfig,
) -> SourceBindingsConfig:
    return step_bindings if step_bindings.enabled else source_bindings


@dataclass(frozen=True, slots=True)
class SourceInventory:
    """Resolved source candidates available for source-binding previews."""

    candidates: tuple[SourceCandidate, ...]
    source_root: Path = Path(".")

    def __post_init__(self) -> None:
        candidates = tuple(self.candidates)
        if any(not isinstance(item, SourceCandidate) for item in candidates):
            raise TypeError(
                "SourceInventory.candidates must contain SourceCandidate values."
            )
        object.__setattr__(self, "candidates", candidates)
        object.__setattr__(self, "source_root", Path(self.source_root))

    @classmethod
    def from_paths(
        cls,
        paths: tuple[str | Path, ...],
        *,
        source_root: str | Path,
        source_backend: str,
        source_bindings: SourceBindingsConfig,
        step_bindings: StepSourceBindingsConfig = EMPTY_SOURCE_BINDINGS,
    ) -> "SourceInventory":
        config = _active_source_bindings(source_bindings, step_bindings)
        return cls(
            candidates=SourceBindingWorkspaceProjector(config).source_candidates(
                Path(source_root),
                paths,
                source_backend=source_backend,
            ),
            source_root=Path(source_root),
        )

    @classmethod
    def from_filemanager(
        cls,
        *,
        filemanager: FileManagerLike,
        source_root: str | Path,
        backend: str,
        source_bindings: SourceBindingsConfig,
        step_bindings: StepSourceBindingsConfig = EMPTY_SOURCE_BINDINGS,
    ) -> "SourceInventory":
        paths = tuple(
            sorted(
                str(path)
                for path in filemanager.list_files(
                    source_root,
                    backend,
                    recursive=True,
                )
            )
        )
        return cls.from_paths(
            paths,
            source_root=source_root,
            source_backend=backend,
            source_bindings=source_bindings,
            step_bindings=step_bindings,
        )


@dataclass(frozen=True, slots=True)
class SourceBindingPreviewRow:
    """Preview summary for one binding applied to a concrete source inventory."""

    alias: str
    declaration_scope: str
    matched_source_count: int
    sample_paths: tuple[str, ...]

    @classmethod
    def from_binding(
        cls,
        binding: NamedSourceBinding,
        candidates: tuple[SourceCandidate, ...],
        *,
        declaration_scope: str,
        sample_limit: int,
    ) -> "SourceBindingPreviewRow":
        return cls(
            alias=binding.alias,
            declaration_scope=declaration_scope,
            matched_source_count=len(candidates),
            sample_paths=tuple(
                candidate.relative_path for candidate in candidates[:sample_limit]
            ),
        )


@dataclass(frozen=True, slots=True)
class SourceSetPreviewRow:
    """Preview summary for one matched source set."""

    index: int
    paths_by_alias: tuple[tuple[str, str], ...]
    metadata: tuple[tuple[str, SourceMetadataValue], ...]

    @classmethod
    def from_record(cls, record: _SourceSet) -> "SourceSetPreviewRow":
        return cls(
            index=record.index,
            paths_by_alias=tuple(
                (alias, candidate.relative_path)
                for alias, candidate in sorted(record.candidates_by_alias.items())
            ),
            metadata=tuple(sorted(record.metadata.items())),
        )


class SourceBindingDiagnosticSeverity(str, Enum):
    """Closed severity values for source-binding preview diagnostics."""

    ERROR = "error"
    WARNING = "warning"
    INFO = "info"


@dataclass(frozen=True, slots=True)
class SourceBindingDiagnostic:
    """Pure diagnostic for unresolved source-binding state."""

    severity: SourceBindingDiagnosticSeverity
    code: str
    alias: str | None
    message: str
    candidate_count: int | None = None


BindingMatches = tuple[
    tuple[NamedSourceBinding, tuple[SourceCandidate, ...]],
    ...,
]


@dataclass(frozen=True, slots=True)
class SourceBindingsPreview:
    """Concrete preview of source bindings against an inventory."""

    binding_rows: tuple[SourceBindingPreviewRow, ...]
    source_set_rows: tuple[SourceSetPreviewRow, ...]
    diagnostics: tuple[SourceBindingDiagnostic, ...] = ()

    @classmethod
    def from_config_and_step_bindings(
        cls,
        *,
        source_bindings: SourceBindingsConfig,
        step_bindings: StepSourceBindingsConfig,
        inventory: SourceInventory,
        sample_limit: int = 3,
    ) -> "SourceBindingsPreview":
        config = _active_source_bindings(source_bindings, step_bindings)
        projector = SourceBindingWorkspaceProjector(config)
        matches: BindingMatches = tuple(
            (
                binding,
                tuple(
                    candidate
                    for candidate in inventory.candidates
                    if projector.candidate_matches_binding(
                        candidate,
                        binding,
                        inventory.source_root,
                    )
                ),
            )
            for binding in config.binding_declarations
        )
        binding_rows = tuple(
            SourceBindingPreviewRow.from_binding(
                binding,
                candidates,
                declaration_scope="step" if step_bindings.enabled else "pipeline",
                sample_limit=sample_limit,
            )
            for binding, candidates in matches
        )
        diagnostics = tuple(
            SourceBindingDiagnostic(
                severity=SourceBindingDiagnosticSeverity.ERROR,
                code="source_binding.no_match",
                alias=binding.alias,
                message=f"Required source alias {binding.alias!r} matched no candidates.",
                candidate_count=0,
            )
            for binding, candidates in matches
            if binding.required and not candidates
        )
        source_set_rows, assembly_diagnostic = cls._assemble_source_set_rows(
            config,
            matches,
        )
        return cls(
            binding_rows=binding_rows,
            source_set_rows=source_set_rows,
            diagnostics=diagnostics + assembly_diagnostic,
        )

    @staticmethod
    def _assemble_source_set_rows(
        config: SourceBindingsConfig,
        matches: BindingMatches,
    ) -> tuple[
        tuple[SourceSetPreviewRow, ...],
        tuple[SourceBindingDiagnostic, ...],
    ]:
        matched_members = {
            binding.alias: candidates
            for binding, candidates in matches
            if binding in config.matched_source_bindings
        }
        if not matched_members or any(
            not candidates for candidates in matched_members.values()
        ):
            return (), ()
        try:
            source_sets = SourceSetAssembler.for_config(config).source_sets(
                config.match_plan,
                matched_members,
                (),
            )
        except ValueError as exc:
            return (), (
                SourceBindingDiagnostic(
                    severity=SourceBindingDiagnosticSeverity.ERROR,
                    code="source_binding.source_set_assembly",
                    alias=None,
                    message=str(exc),
                ),
            )
        return tuple(SourceSetPreviewRow.from_record(item) for item in source_sets), ()
