"""Outcome-only evidence from ordinary ZMQ execution."""

from pathlib import Path

import pytest

from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    ExecutionStatus,
    RuntimeContextObservation,
    RuntimeExecutionObservation,
)
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
    ZMQRuntimeExecutionOutcomeExport,
)


def test_outcome_export_round_trip_excludes_runtime_values(tmp_path: Path) -> None:
    runtime_value = b"worker-only-runtime-value"
    declared_output = tmp_path / "output" / "measurements.db"
    declared_output.parent.mkdir()
    declared_output.write_bytes(b"sqlite evidence")
    owned_exports = RuntimeExportObservation.from_output_paths((declared_output,))
    execution_results = {
        "A01": ExecutionResult.success(
            "A01",
            runtime_observation=RuntimeExecutionObservation(
                contexts=(
                    RuntimeContextObservation(
                        "context",
                        (runtime_value,),
                        outputs=StepExecutionObservation({}, (declared_output,)),
                    ),
                )
            ),
        ),
        "B01": ExecutionResult.error(
            "B01", failed_combination="field-2", error_message="failed"
        ),
    }
    exported = ZMQRuntimeExecutionOutcomeExport.from_execution(
        compiled_axis_ids=("A01", "B01"),
        execution_results=execution_results,
        output_roots=(tmp_path / "output",),
        execution_id="execution-1",
        exports=owned_exports,
    )
    path = tmp_path / "outcomes.pkl.gz"
    exported.write(path)

    restored = ZMQRuntimeExecutionOutcomeExport.read(path)
    retained_bytes = path.read_bytes()
    with pytest.raises(FileExistsError):
        exported.write(path)

    assert restored == exported
    assert path.read_bytes() == retained_bytes
    assert restored.execution_id == "execution-1"
    assert restored.axis_count == 2
    assert restored.successful_axis_count == 1
    assert restored.outcomes_by_axis["B01"].status is ExecutionStatus.ERROR
    assert restored.outcomes_by_axis["B01"].failed_combination == "field-2"
    assert restored.exports is not None
    assert restored.exports.output_files == (declared_output,)
    assert runtime_value not in path.read_bytes()
    with pytest.raises(RuntimeError, match="'B01': 'error'"):
        restored.require_successful_axes()
    with pytest.raises(
        TypeError, match="must contain ZMQRuntimeExecutionObservationExport"
    ):
        ZMQRuntimeExecutionObservationExport.read(path)


def test_successful_outcome_export_accepts_all_axes(tmp_path: Path) -> None:
    exported = ZMQRuntimeExecutionOutcomeExport.from_execution(
        compiled_axis_ids=("A01",),
        execution_results={"A01": ExecutionResult.success("A01")},
        output_roots=(tmp_path,),
    )

    exported.require_successful_axes()


def test_outcome_export_rejects_missing_and_uncompiled_axes(tmp_path: Path) -> None:
    missing = ZMQRuntimeExecutionOutcomeExport.from_execution(
        compiled_axis_ids=("A01", "B01"),
        execution_results={"A01": ExecutionResult.success("A01")},
        output_roots=(tmp_path,),
    )
    with pytest.raises(RuntimeError, match="compiled axes have no execution outcome"):
        missing.require_successful_axes()

    unexpected = ZMQRuntimeExecutionOutcomeExport.from_execution(
        compiled_axis_ids=("A01",),
        execution_results={
            "A01": ExecutionResult.success("A01"),
            "B01": ExecutionResult.success("B01"),
        },
        output_roots=(tmp_path,),
    )
    with pytest.raises(RuntimeError, match="execution outcomes have no compiled axis"):
        unexpected.require_successful_axes()


def test_value_export_rejects_an_uncompiled_execution_axis() -> None:
    exported = ZMQRuntimeExecutionObservationExport.from_execution(
        compiled_contexts={},
        execution_results={"A01": ExecutionResult.success("A01")},
        output_roots=(),
        runtime_observations=(),
    )
    with pytest.raises(RuntimeError, match="execution outcomes have no compiled axis"):
        exported.require_valid_observation()


def test_runtime_observation_export_never_overwrites_existing_file(
    tmp_path: Path,
) -> None:
    observation_path = tmp_path / "observation.pkl.gz"
    ZMQRuntimeExecutionObservationExport.from_execution(
        compiled_contexts={},
        execution_results={},
        output_roots=(),
        execution_id="first-job",
        runtime_observations=(),
    ).write(observation_path)
    retained_bytes = observation_path.read_bytes()
    with pytest.raises(FileExistsError):
        ZMQRuntimeExecutionObservationExport.from_execution(
            compiled_contexts={},
            execution_results={},
            output_roots=(),
            execution_id="other-job",
            runtime_observations=(),
        ).write(observation_path)
    assert observation_path.read_bytes() == retained_bytes
    assert (
        ZMQRuntimeExecutionObservationExport.read(observation_path).execution_id
        == "first-job"
    )
