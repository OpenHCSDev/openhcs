"""Outcome-only evidence from ordinary ZMQ execution."""

from pathlib import Path

import pytest

from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    ExecutionStatus,
    RuntimeContextObservation,
    RuntimeExecutionObservation,
)
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
    ZMQRuntimeExecutionOutcomeExport,
)


def test_outcome_export_round_trip_excludes_runtime_values(tmp_path: Path) -> None:
    runtime_value = b"worker-only-runtime-value"
    execution_results = {
        "A01": ExecutionResult.success(
            "A01",
            runtime_observation=RuntimeExecutionObservation(
                contexts=(RuntimeContextObservation("context", (runtime_value,)),)
            ),
        ),
        "B01": ExecutionResult.error(
            "B01", failed_combination="field-2", error_message="failed"
        ),
    }
    exported = ZMQRuntimeExecutionOutcomeExport.from_execution(
        execution_results=execution_results,
        output_roots=(tmp_path / "output",),
    )
    path = tmp_path / "outcomes.pkl.gz"
    exported.write(path)

    restored = ZMQRuntimeExecutionOutcomeExport.read(path)

    assert restored == exported
    assert restored.axis_count == 2
    assert restored.successful_axis_count == 1
    assert restored.outcomes_by_axis["B01"].status is ExecutionStatus.ERROR
    assert restored.outcomes_by_axis["B01"].failed_combination == "field-2"
    assert runtime_value not in path.read_bytes()
    with pytest.raises(RuntimeError, match="'B01': 'error'"):
        restored.require_successful_axes()
    with pytest.raises(
        TypeError, match="must contain ZMQRuntimeExecutionObservationExport"
    ):
        ZMQRuntimeExecutionObservationExport.read(path)


def test_successful_outcome_export_accepts_all_axes(tmp_path: Path) -> None:
    exported = ZMQRuntimeExecutionOutcomeExport.from_execution(
        execution_results={"A01": ExecutionResult.success("A01")},
        output_roots=(tmp_path,),
    )

    exported.require_successful_axes()
