"""Typed step-dependency records for compiled pipeline execution."""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import ClassVar


@dataclass(frozen=True, slots=True)
class StepInputDependency(ABC):
    """Where one compiled step's main input comes from; each case is a subclass."""

    is_resolved: ClassVar[bool] = True
    """Whether compiled planning can use this dependency."""

    def predecessor_step_index(self) -> int | None:
        """The exact upstream compiled step, if one exists."""

        return None

    def uses_pipeline_start_anchors(self) -> bool:
        """Only a pipeline-start main input is filtered against raw source bindings."""

        return False

    def require_pipeline_start(self) -> None:
        """Prove that this terminal dependency reaches the pipeline source."""

        raise ValueError(
            "Terminal step-input dependency is not pipeline-start: "
            f"{type(self).__name__}."
        )


@dataclass(frozen=True, slots=True)
class UnresolvedStepInput(StepInputDependency):
    """Not yet resolved by compilation."""

    is_resolved = False


@dataclass(frozen=True, slots=True)
class NoMainFlowInput(StepInputDependency):
    """The step reads no main-flow image stack."""


@dataclass(frozen=True, slots=True)
class PipelineStartInput(StepInputDependency):
    """The step reads the pipeline's source planes."""

    def uses_pipeline_start_anchors(self) -> bool:
        return True

    def require_pipeline_start(self) -> None:
        return None


@dataclass(frozen=True, slots=True)
class StepOutputInput(StepInputDependency):
    """The step reads one upstream step's main-flow output."""

    source_step_index: int
    source_step_scope_id: str

    def __post_init__(self) -> None:
        if not self.source_step_scope_id:
            raise ValueError("StepOutputInput requires source_step_scope_id.")

    def predecessor_step_index(self) -> int:
        return self.source_step_index
