"""OpenHCS extensions for zmqruntime server hooks."""

from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import Any

from zmqruntime.messages import (
    ExecutionStatus,
    MessageFields,
    ResponseType,
)

from openhcs.core.execution_state import ExecutionOutputSummary
from openhcs.core.orchestrator.bundle_execution import (
    BundleExecutionExtras,
)
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryParamField
from python_introspect import to_jsonable

logger = logging.getLogger(__name__)


@dataclass(frozen=True, slots=True)
class ZMQResultsSummaryEnricher:
    """Projects OpenHCS output-dataset metadata into execution summaries."""

    active_executions: dict[str, Any]

    def attach(
        self,
        *,
        execution_id: str,
        record: Any,
        execution_payload: dict | None = None,
    ) -> None:
        if record.status != ExecutionStatus.COMPLETE.value:
            return

        summary = record.results_summary
        if not isinstance(summary, dict):
            summary = {}
            record.results_summary = summary

        output_summary = record.get_extra(
            ExecutionOutputSummary.EXECUTION_RECORD_KEY
        )
        if output_summary is None:
            output_summary = ExecutionOutputSummary()
        elif not isinstance(output_summary, ExecutionOutputSummary):
            raise TypeError(
                "Execution output-dataset metadata must use "
                f"{ExecutionOutputSummary.__name__}."
            )
        observation_export_path = record.get_extra(
            ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value
        )
        observation_export_scope = record.get_extra(
            ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_SCOPE.value
        )
        compiled_execution_extras = record.get_extra(
            BundleExecutionExtras.EXECUTION_RECORD_KEY
        )
        if compiled_execution_extras is not None and not isinstance(
            compiled_execution_extras,
            BundleExecutionExtras,
        ):
            raise TypeError(
                "Compiled execution metadata must use "
                f"{BundleExecutionExtras.__name__}."
            )
        summary.update(output_summary.results_summary_fields())
        if observation_export_path:
            summary[ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value] = str(
                observation_export_path
            )
            if observation_export_scope is not None:
                summary[
                    ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_SCOPE.value
                ] = str(observation_export_scope)
        if compiled_execution_extras is not None:
            summary.update(compiled_execution_extras.load_phase.results_summary_fields())
        if (
            compiled_execution_extras is not None
            and compiled_execution_extras.viewer_states_by_port
        ):
            summary[BundleExecutionExtras.RESULTS_SUMMARY_KEY] = to_jsonable(
                compiled_execution_extras.viewer_states_by_port
            )
        if isinstance(execution_payload, dict):
            execution_payload[MessageFields.RESULTS_SUMMARY] = summary

        logger.info(
            "[%s] Attached results_summary extras: output_dataset_root=%s auto_add=%s observation=%s",
            execution_id,
            output_summary.output_dataset_root,
            output_summary.auto_add_output_dataset,
            summary.get(ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value),
        )

    def attach_to_status_response(
        self,
        *,
        execution_id: str | None,
        response: dict[str, Any],
    ) -> dict[str, Any]:
        if response.get(MessageFields.STATUS) != ResponseType.OK.value:
            return response
        if not execution_id:
            return response

        record = self.active_executions[execution_id]
        execution_payload = response.get(MessageFields.EXECUTION)
        self.attach(
            execution_id=execution_id,
            record=record,
            execution_payload=(
                execution_payload if isinstance(execution_payload, dict) else None
            ),
        )
        return response


@dataclass(frozen=True, slots=True)
class ZMQWorkerCleanup:
    """Cancel the exact execution resources owned by existing orchestrators."""

    active_executions: dict[str, Any]

    def cancel_execution(self, execution_id: str) -> int:
        """Cancel one execution and count its terminated worker processes."""

        record = self.active_executions.get(execution_id)
        if record is None:
            return 0
        orchestrator = record.get_extra("orchestrator")
        if orchestrator is None:
            return 0
        logger.info("[%s] Requesting graceful cancellation...", execution_id)
        return orchestrator.cancel_execution()

    def cancel_orchestrators(self) -> int:
        terminated = 0
        errors: list[Exception] = []
        for execution_id in tuple(self.active_executions):
            try:
                terminated += self.cancel_execution(execution_id)
            except Exception as error:
                errors.append(error)
                logger.warning(
                    "[%s] Graceful cancellation failed: %s",
                    execution_id,
                    error,
                )
        if errors:
            raise errors[0]
        return terminated
