"""Nominal task declarations for the autonomous analysis corpus."""

from __future__ import annotations

from abc import ABC, abstractmethod
from pathlib import Path
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from benchmark.agent_validation.contracts import (
    AssertionResult,
    DiagnosticCheck,
    DslRequirement,
    EvidenceClass,
    FunctionAvailabilityExpectation,
    OutputKind,
    ScoringCase,
    TaskAuthoringSpec,
    UpstreamTaskSource,
    ViewKind,
)


class ValidationTaskDeclaration(ABC, metaclass=AutoRegisterMeta):
    """Single authority for one public prompt and its hidden scorer."""

    __registry__: ClassVar[dict[str, type["ValidationTaskDeclaration"]]] = {}
    __registry_key__ = "task_id"
    __skip_if_no_key__ = True

    task_id: ClassVar[str | None] = None
    prompt: ClassVar[str]
    evidence_class: ClassVar[EvidenceClass] = EvidenceClass.DETERMINISTIC_PARITY
    output_kind: ClassVar[OutputKind]
    function_availability: ClassVar[FunctionAvailabilityExpectation]
    source: ClassVar[UpstreamTaskSource]
    required_diagnostics: ClassVar[tuple[DiagnosticCheck, ...]]
    required_dsl: ClassVar[tuple[DslRequirement, ...]]
    dsl_instruction: ClassVar[str]

    @classmethod
    def declarations(cls) -> tuple[type["ValidationTaskDeclaration"], ...]:
        """Return registered tasks in stable semantic-id order."""

        return tuple(cls.__registry__[key] for key in sorted(cls.__registry__))

    @classmethod
    def get(cls, task_id: str) -> type["ValidationTaskDeclaration"]:
        """Resolve one exact task id from the declaration registry."""

        try:
            return cls.__registry__[task_id]
        except KeyError as exc:
            raise ValueError(
                f"task_id must be one of: {', '.join(sorted(cls.__registry__))}"
            ) from exc

    @classmethod
    def authoring_spec(cls, input_root: Path) -> TaskAuthoringSpec:
        """Project the declaration without held-out cases or assertions."""

        if cls.task_id is None:
            raise ValueError(f"{cls.__name__} must declare task_id.")
        return TaskAuthoringSpec(
            task_id=cls.task_id,
            prompt=cls.prompt,
            evidence_class=cls.evidence_class,
            output_kind=cls.output_kind,
            function_availability=cls.function_availability,
            source=cls.source,
            required_diagnostics=cls.required_diagnostics,
            required_dsl=cls.required_dsl,
            required_views=cls.required_views(),
            dsl_instruction=cls.dsl_instruction,
            input_root=input_root,
        )

    @classmethod
    def required_views(cls) -> tuple[ViewKind, ...]:
        """Derive evidence views from the declared output artifact family."""

        views = [ViewKind.RAW, ViewKind.NORMALIZED, ViewKind.OVERLAY]
        if cls.output_kind is OutputKind.LABEL_IMAGE:
            views.extend((ViewKind.MASK, ViewKind.ROI))
        if cls.output_kind in {OutputKind.SCALAR, OutputKind.TABLE}:
            views.append(ViewKind.MEASUREMENT)
        return tuple(views)

    @classmethod
    @abstractmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        """Return hidden inputs and upstream-equivalent expected results."""

    @classmethod
    @abstractmethod
    def assert_case(
        cls, case: ScoringCase, actual: object
    ) -> tuple[AssertionResult, ...]:
        """Apply the pinned upstream assertion semantics to one result."""
