"""
Execution result types for pipeline orchestration.

This module defines typed execution results to replace dict-based results,
following OpenHCS standards for explicit contracts and type safety.
"""

import copyreg
from dataclasses import dataclass, field
from abc import ABC, abstractmethod
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar, Mapping, Optional

from metaclass_registry import AutoRegisterMeta

from openhcs.constants.constants import Backend
from openhcs.core.context.processing_context import ProcessingContext
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


class ExecutionStatus(ABC, metaclass=AutoRegisterMeta):
    """How pipeline execution ended for one axis; ``name`` is its spelling."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    succeeded: ClassVar[bool] = False


class AxisSucceeded(ExecutionStatus):
    name = "success"
    succeeded = True


class AxisFailed(ExecutionStatus):
    name = "error"


class AxisCancelled(ExecutionStatus):
    name = "cancelled"


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
        runtime_observation_mode: "type[RuntimeObservationMode]",
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
        cls, contexts: Mapping[str, ProcessingContext]
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

    def merge_into(self, execution_contexts: Mapping[str, ProcessingContext]) -> None:
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
class ExecutionResult:
    """
    Typed result of pipeline execution for a single axis.

    Replaces dict-based results to provide compile-time type safety
    and explicit contracts.

    Attributes:
        status: Execution status (success, error, etc.)
        axis_id: Identifier for the axis that was executed
        failed_combination: Optional key of the combination that failed (for sequential mode)
        error_message: Optional error message if status is ERROR
    """

    status: type[ExecutionStatus]
    axis_id: str
    failed_combination: Optional[str] = None
    error_message: Optional[str] = None
    runtime_observation: RuntimeExecutionObservation = field(
        default_factory=RuntimeExecutionObservation
    )

    def is_success(self) -> bool:
        """Check if execution was successful."""
        return self.status.succeeded

    def is_cancelled(self) -> bool:
        return self.status is AxisCancelled

    @classmethod
    def success(
        cls,
        axis_id: str,
        runtime_observation: RuntimeExecutionObservation | None = None,
    ) -> "ExecutionResult":
        """Create a successful execution result."""
        return cls(
            status=AxisSucceeded,
            axis_id=axis_id,
            runtime_observation=runtime_observation or RuntimeExecutionObservation(),
        )

    @classmethod
    def error(
        cls,
        axis_id: str,
        failed_combination: Optional[str] = None,
        error_message: Optional[str] = None,
        runtime_observation: RuntimeExecutionObservation | None = None,
    ) -> "ExecutionResult":
        """Create an error execution result."""
        return cls(
            status=AxisFailed,
            axis_id=axis_id,
            failed_combination=failed_combination,
            error_message=error_message,
            runtime_observation=(
                RuntimeExecutionObservation()
                if runtime_observation is None else runtime_observation
            ),
        )

    @classmethod
    def cancelled(
        cls,
        axis_id: str,
        *,
        error_message: str,
        runtime_observation: RuntimeExecutionObservation | None = None,
    ) -> "ExecutionResult":
        """Return completed outputs from a cooperative cancellation boundary."""
        return cls(
            status=AxisCancelled,
            axis_id=axis_id,
            error_message=error_message,
            runtime_observation=(
                RuntimeExecutionObservation()
                if runtime_observation is None else runtime_observation
            ),
        )
