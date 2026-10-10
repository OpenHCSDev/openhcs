"""Input workspace preparation contracts owned by orchestration."""

from __future__ import annotations

import hashlib
import shutil
from dataclasses import dataclass
from pathlib import Path

from openhcs.core.config import PipelineConfig
from openhcs.core.source_binding_workspace import (
    SourceBindingWorkspaceMaterialization,
)
from openhcs.core.steps.function_step import FunctionStep


@dataclass(frozen=True, slots=True)
class PipelineImportDiagnostic:
    """Non-fatal diagnostic from importing an external pipeline dialect."""

    pipeline_path: Path
    exception_type: str
    message: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "pipeline_path", Path(self.pipeline_path))


@dataclass(frozen=True, slots=True)
class InputWorkspacePreparationRequest:
    """Request to prepare a selected input tree before microscope initialization."""

    selected_path: Path
    selected_pipeline_path: Path | None = None
    workspace_root: Path | None = None
    generated_source_path: Path | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "selected_path", Path(self.selected_path))
        if self.selected_pipeline_path is not None:
            object.__setattr__(
                self,
                "selected_pipeline_path",
                Path(self.selected_pipeline_path),
            )
        if self.workspace_root is not None:
            object.__setattr__(self, "workspace_root", Path(self.workspace_root))
        if self.generated_source_path is not None:
            object.__setattr__(
                self,
                "generated_source_path",
                Path(self.generated_source_path),
            )


@dataclass(frozen=True, slots=True)
class InputWorkspacePreparationResult:
    """Prepared input workspace plus optional external pipeline import product."""

    original_source_root: Path
    execution_plate_path: Path
    pipeline_path: Path | None = None
    pipeline_steps: list[FunctionStep] | None = None
    pipeline_config: PipelineConfig | None = None
    materialization: SourceBindingWorkspaceMaterialization | None = None
    pipeline_import_error: PipelineImportDiagnostic | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "original_source_root", Path(self.original_source_root)
        )
        object.__setattr__(
            self, "execution_plate_path", Path(self.execution_plate_path)
        )
        if self.pipeline_path is not None:
            object.__setattr__(self, "pipeline_path", Path(self.pipeline_path))
        if (self.pipeline_steps is None) is not (self.pipeline_config is None):
            raise ValueError(
                "InputWorkspacePreparationResult requires pipeline_steps and "
                "pipeline_config together."
            )
        if self.pipeline_steps is not None:
            pipeline_steps = list(self.pipeline_steps)
            for step in pipeline_steps:
                if not isinstance(step, FunctionStep):
                    raise TypeError(
                        "InputWorkspacePreparationResult.pipeline_steps must "
                        f"contain FunctionStep values, got {type(step).__name__}."
                    )
            object.__setattr__(self, "pipeline_steps", pipeline_steps)
        if self.pipeline_config is not None and not isinstance(
            self.pipeline_config,
            PipelineConfig,
        ):
            raise TypeError(
                "InputWorkspacePreparationResult.pipeline_config must be "
                f"PipelineConfig, got {type(self.pipeline_config).__name__}."
            )
        if self.materialization is not None and not isinstance(
            self.materialization,
            SourceBindingWorkspaceMaterialization,
        ):
            raise TypeError(
                "InputWorkspacePreparationResult.materialization must be "
                "SourceBindingWorkspaceMaterialization, got "
                f"{type(self.materialization).__name__}."
            )


def mirror_input_workspace(source_root: Path, workspace_root: Path) -> Path:
    """Build a fresh execution workspace over ``source_root`` without writing to it.

    Directories are recreated, data files are symlinked to the source, and the
    metadata files initialization rewrites are copied, so nothing that runs in
    the workspace can write through to the source. ``workspace_root`` must not
    exist yet and must not lie inside the source.
    """

    from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG

    source = Path(source_root).resolve()
    workspace = Path(workspace_root).resolve()
    if workspace == source or workspace.is_relative_to(source):
        raise ValueError(f"A workspace may not lie inside its source: {workspace}")
    copied = {path.name for path in METADATA_CONFIG.managed_paths(source)}
    workspace.mkdir(parents=True)
    for path in sorted(source.rglob("*")):
        target = workspace / path.relative_to(source)
        if path.is_dir():
            target.mkdir()
        elif path.name in copied:
            shutil.copyfile(path, target)
        else:
            target.symlink_to(path.resolve())
    return workspace


def derived_workspace_root(source_root: Path, parent: Path) -> Path:
    """A fresh, unused workspace directory for ``source_root`` under ``parent``."""

    source = Path(source_root).resolve()
    digest = hashlib.sha256(str(source).encode("utf-8")).hexdigest()[:12]
    stem = f"{source.name}-{digest}"
    candidate = Path(parent) / stem
    index = 1
    while candidate.exists():
        index += 1
        candidate = Path(parent) / f"{stem}-{index}"
    return candidate
