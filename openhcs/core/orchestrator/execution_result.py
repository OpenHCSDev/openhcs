"""
Execution result types for pipeline orchestration.

This module defines typed execution results to replace dict-based results,
following OpenHCS standards for explicit contracts and type safety.
"""

from __future__ import annotations

import copyreg
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar, Mapping

from openhcs.constants.constants import Backend
from openhcs.core.array_conversions import StepConversions
from openhcs.core.context.processing_context import (
    ExecutingContext,
    ProcessingContext,
)
from openhcs.core.progress.types import (
    AxisErrorProgressPhase,
    CancelledProgressPhase,
    CancelledProgressStatus,
    ErrorProgressStatus,
    ProgressPhase,
    ProgressStatus,
)
from openhcs.core.runtime_stores import RuntimeArtifactQuery, StoredRuntimeValue
from openhcs.core.steps.abstract import StepExecutionObservation

if TYPE_CHECKING:
    from openhcs.core.compiled_execution import CompiledExecutionBundle


class RuntimeExecutionTransportSerialization:
    """Pickle reducers required for worker-to-parent execution results."""

    @staticmethod
    def mapping_proxy_from_dict(value: dict) -> MappingProxyType:
        """Rebuild an immutable mapping view from transport state."""
        return MappingProxyType(value)

    @staticmethod
    def reduce_mapping_proxy(
        value: MappingProxyType,
    ) -> tuple[object, tuple[dict]]:
        """Serialize immutable mapping views as immutable mapping views."""
        return RuntimeExecutionTransportSerialization.mapping_proxy_from_dict, (
            dict(value),
        )

    @classmethod
    def register(cls) -> None:
        """Install execution-result transport reducers in this interpreter."""
        copyreg.pickle(type(MappingProxyType({})), cls.reduce_mapping_proxy)


RuntimeExecutionTransportSerialization.register()


@dataclass(frozen=True)
class RuntimeContextObservation:
    """Runtime records produced for one compiled execution context."""

    context_key: str
    records: tuple[StoredRuntimeValue, ...]
    outputs: StepExecutionObservation = field(default_factory=StepExecutionObservation.empty)

    @classmethod
    def from_context(
        cls,
        *,
        context_key: str,
        context: ProcessingContext,
        records: tuple[StoredRuntimeValue, ...],
        runtime_observation_mode: type[RuntimeObservationMode],
        outputs: StepExecutionObservation,
    ) -> "RuntimeContextObservation":
        """Retain requested records beside the completed output projections."""
        return cls(
            context_key=context_key,
            records=runtime_observation_mode.retain_records(records, context),
            outputs=outputs,
        )


@dataclass(frozen=True)
class RuntimeExecutionObservation:
    """Runtime records returned from worker-owned execution contexts."""

    contexts: tuple[RuntimeContextObservation, ...] = field(default_factory=tuple)

    @classmethod
    def from_completed_outputs(
        cls, contexts: Mapping[str, ExecutingContext]
    ) -> "RuntimeExecutionObservation":
        """Project saved facts independently of retained runtime pixel records."""
        return cls(contexts=tuple(
            RuntimeContextObservation(
                context_key=context_key,
                records=(),
                outputs=context.completed_step_outputs,
            )
            for context_key, context in contexts.items()
            if not context.completed_step_outputs.is_empty
        ))

    def merge_into(self, execution_contexts: Mapping[str, ExecutingContext]) -> None:
        """Merge returned runtime records into parent-owned compiled contexts."""
        for context_observation in self.contexts:
            context = execution_contexts[context_observation.context_key]
            store = context.runtime_value_store
            store.merge_observed_values(context_observation.records)
            context.record_completed_step_outputs(context_observation.outputs)


class RuntimeObservationMode(ABC):
    """Which worker runtime records are returned to the parent; each mode keeps its own."""

    @staticmethod
    def from_parent_requirement(required: bool) -> "type[RuntimeObservationMode]":
        """Select the mode implied by compiled parent-side execution needs."""

        return MergeAllRuntimeRecords if required else OmitRuntimeRecords

    @staticmethod
    def for_compiled_bundle(
        bundle: "CompiledExecutionBundle",
    ) -> "type[RuntimeObservationMode]":
        """Consolidation carries rendered tables; only dataset-scoped inputs need records."""

        if bundle.requires_parent_runtime_observation:
            return MergeDatasetInputRecords
        return OmitRuntimeRecords

    @classmethod
    def including_parent_requirement(
        cls,
        required: bool,
    ) -> "type[RuntimeObservationMode]":
        """Return this mode strengthened by an additional retention requirement."""

        return MergeAllRuntimeRecords if required else cls

    @staticmethod
    @abstractmethod
    def retain_records(
        records: tuple[StoredRuntimeValue, ...],
        context: ProcessingContext,
    ) -> tuple[StoredRuntimeValue, ...]:
        """Keep records consumed by the selected parent-side execution route."""


class MergeAllRuntimeRecords(RuntimeObservationMode):
    """Return every worker record to the parent.

    Workers keep each record to the end, so consumed inputs are never released.
    """

    @staticmethod
    def retain_records(records, context):
        return records


class MergeDatasetInputRecords(RuntimeObservationMode):
    """Return only the records dataset-scoped steps read as inputs."""

    @staticmethod
    def retain_records(records, context):
        selected_addresses = set()
        for plan in context.step_plans.values():
            if not plan.execution_scope.requires_parent_runtime_observation:
                continue
            for invocation in plan.compiled_function_pattern.default_group.invocations:
                input_edges = {
                    edge.spec.ref(): edge
                    for edge in invocation.select_inputs(plan.artifact_inputs).values()
                    if edge.storage_plan is not None
                }
                for spec in invocation.contract.artifact_inputs:
                    edge = input_edges.get(spec.ref())
                    if edge is None:
                        continue
                    selected_addresses.update(
                        (record.key, record.location)
                        for record in RuntimeArtifactQuery.records_for_input_edge(
                            edge,
                            records,
                            axis_id=context.require_axis_id(),
                            backend=Backend.MEMORY.value,
                        )
                    )
        return tuple(
            record
            for record in records
            if (record.key, record.location) in selected_addresses
        )


class OmitRuntimeRecords(RuntimeObservationMode):
    """Return no worker records."""

    @staticmethod
    def retain_records(records, context):
        return ()


@dataclass(frozen=True)
class ExecutionResult(ABC):
    """Outcome of executing one axis value's compiled contexts."""

    stops_lane: ClassVar[bool] = False

    axis_id: str
    runtime_observation: RuntimeExecutionObservation = field(
        default_factory=RuntimeExecutionObservation
    )
    conversions: StepConversions = field(default_factory=StepConversions)
    """The array conversions made while this axis's steps executed."""

    def is_success(self) -> bool:
        return False

    def describe(self) -> str:
        """Return this outcome as one line of text."""
        return type(self).__name__

    def without_runtime_observation(self) -> "ExecutionResult":
        """Return this outcome without the worker runtime records it carries."""
        return replace(self, runtime_observation=RuntimeExecutionObservation())


@dataclass(frozen=True)
class ExecutionSucceeded(ExecutionResult):
    """Every compiled context of the axis ran to completion."""

    def is_success(self) -> bool:
        return True


@dataclass(frozen=True, kw_only=True)
class ExecutionStopped(ExecutionResult):
    """Execution of the axis ended before completion."""

    progress_phase: ClassVar[type[ProgressPhase]]
    progress_status: ClassVar[type[ProgressStatus]]

    error_message: str
    failed_combination: str | None = None

    def describe(self) -> str:
        return f"{type(self).__name__}: {self.error_message}"

    def at_combination(
        self,
        context_key: str,
        runtime_observation: RuntimeExecutionObservation,
        conversions: StepConversions,
    ) -> "ExecutionStopped":
        """Attribute this stop to one compiled context with the axis's records."""
        return replace(
            self,
            failed_combination=context_key,
            runtime_observation=runtime_observation,
            conversions=conversions,
        )


@dataclass(frozen=True, kw_only=True)
class ExecutionFailed(ExecutionStopped):
    """A step raised while executing the axis."""

    progress_phase = AxisErrorProgressPhase
    progress_status = ErrorProgressStatus


@dataclass(frozen=True, kw_only=True)
class ExecutionCancelled(ExecutionStopped):
    """Execution was cancelled cooperatively."""

    stops_lane = True
    progress_phase = CancelledProgressPhase
    progress_status = CancelledProgressStatus
