"""The agent's observation option uses ordinary pipeline execution end to end."""

from __future__ import annotations

import asyncio
import os
import time
from pathlib import Path
from types import SimpleNamespace

import pytest
from objectstate.object_state import ObjectStateRegistry
from zmqruntime import DataControlPortPairAuthority
from zmqruntime.messages import ExecutionStatus

from benchmark.cellprofiler_benchmark_cli import create_benchmark_argument_parser
from benchmark.contracts.measured_run_receipt import MeasuredPipelineRunReceipt
from benchmark.contracts.run_artifacts import MeasuredPipelineRunArtifact
from benchmark.control import (
    inspect_measured_pipeline_run,
    report_measured_pipeline_run,
)
from benchmark.openhcs_measured_run import (
    _ZMQProgressTimingObserver,
    execute_measured_openhcs_pipeline,
    execute_measured_openhcs_pipeline_on_client,
)
from benchmark.timing import BenchmarkPhase, PhaseTimingTrace
from benchmark.well_throughput_scaling import (
    ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    WellThroughputMode,
    run_case_well_throughput,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.authoring.session.session import CallerThread
from openhcs.core.config import GlobalPipelineConfig, PathPlanningConfig, PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.mcp import server
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG, OpenHCSZMQConfig
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
)
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
    ZMQRuntimeExecutionOutcomeExport,
)
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQRuntimeObservationExportScope,
)


def _synthetic_plate_and_pipeline(tmp_path: Path, *, wells: tuple[str, ...] = ("A01",)):
    plate = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(plate),
        grid_size=(1, 1),
        tile_size=(32, 32),
        wavelengths=1,
        z_stack_levels=1,
        num_cells=2,
        wells=list(wells),
        format="ImageXpress",
        random_seed=7,
    ).generate_dataset()
    pipeline = PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=[
            FunctionStep(name="Blur", func=(gaussian_blur, {"sigma": 1.0}))
        ],
    )
    return plate, pipeline


@pytest.fixture
def mcp_session(tmp_path: Path):
    """An MCP server over a fresh session that runs on the calling thread."""

    ObjectStateRegistry.clear()
    context = OpenHCSAgentContext(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        ),
        session_transport_config=OpenHCSZMQConfig(
            default_port=18000 + os.getpid() % 20000, persistent=False
        ),
    )
    built = server.build_server(context)
    context.bind_main_thread(CallerThread())
    try:
        yield built, context.session
    finally:
        context.session.close()
        ObjectStateRegistry.clear()


def _call(built, name: str, arguments: dict) -> dict:
    _content, structured = asyncio.run(built.call_tool(name, arguments))
    return structured


def _start_run(built, plate: Path, pipeline, export_path: Path) -> tuple[str, int]:
    """Add the dataset, give it the pipeline, initialize and compile it, start a run."""

    (scope_id,) = _call(built, "openhcs_add_datasets", {"roots": [str(plate)]})[
        "target_scope_ids"
    ]
    _call(
        built,
        "openhcs_set_dataset_pipeline",
        {"scope_id": scope_id, "pipeline_source": PipelineDocumentCodec.render(pipeline)},
    )
    _wait_for_row(built, _call(
        built, "openhcs_initialize_datasets", {"scope_ids": [scope_id]}
    ), lambda row: row["initialized"] and not row["init_pending"])
    _wait_for_row(built, _call(
        built, "openhcs_compile_datasets", {"scope_ids": [scope_id]}
    ), lambda row: row["compiled"] and not row["compile_pending"])
    started = _call(
        built,
        "openhcs_run_datasets",
        {
            "scope_ids": [scope_id],
            "runtime_observation_export_path": str(export_path),
        },
    )
    assert started["status"] == "accepted", started["errors"]
    return scope_id, started["event_sequence"]


def _wait_for_row(built, started: dict, finished) -> dict:
    assert started["status"] == "accepted", started["errors"]
    sequence = started["event_sequence"]
    deadline = time.monotonic() + 300
    while True:
        (row,) = _call(built, "openhcs_session_datasets", {})["rows"]
        if finished(row):
            return row
        assert time.monotonic() < deadline, row
        sequence = _call(
            built,
            "openhcs_session_events",
            {"after_sequence": sequence, "timeout_seconds": 5.0},
        )["last_sequence"]


def _run_finished(row: dict) -> bool:
    return row["terminal_status"] is not None and not row["execution_active"]


def test_headless_observation_export_uses_ordinary_execution(
    tmp_path: Path, mcp_session
) -> None:
    built, session = mcp_session
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    export_path = tmp_path / "runtime_observation.pkl"

    scope_id, sequence = _start_run(built, plate, pipeline, export_path)
    row = _wait_for_row(
        built, {"status": "accepted", "event_sequence": sequence}, _run_finished
    )

    assert row["terminal_status"] == "complete", row
    execution_id = row["finished_execution_id"]
    completed = session.finished_executions[execution_id]
    assert completed.scope_id == scope_id
    assert completed.record.execution_id == execution_id
    assert completed.record.results_summary is not None
    assert completed.record.end_time is not None
    assert completed.endpoint is not None
    observation = ZMQRuntimeExecutionObservationExport.read(export_path)
    observation.require_valid_observation()
    assert observation.output_roots
    assert observation.server_environment is not None
    assert observation.server_environment.python_version
    assert observation.server_environment.python_executable
    assert any(
        distribution.name.casefold() == "numpy"
        for distribution in observation.server_environment.installed_distributions
    )
    finalization = _call(
        built,
        "openhcs_finalize_measured_pipeline_run",
        {
            "execution_id": execution_id,
            "run_id": "headless-ordinary",
            "pipeline_name": "Blur",
        },
    )
    assert finalization.get("execution_id") == execution_id, finalization
    receipt = MeasuredPipelineRunReceipt.read(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path)
    )
    assert receipt.execution_id == execution_id
    assert receipt.plate_id == str(plate)
    assert receipt.server_environment == observation.server_environment
    assert BenchmarkPhase.SERVER_PIPELINE_JOB in {
        timing.phase for timing in receipt.phase_timings
    }
    assert all(timing.seconds >= 0 for timing in receipt.phase_timings)
    inspection = inspect_measured_pipeline_run(tmp_path)
    assert all(evidence.valid for evidence in inspection.source_evidence)
    assert inspection.observation_integrity_verified
    assert inspection.results_summary_integrity_verified
    assert inspection.retained_evidence_valid


def test_measured_wrapper_retains_sources_and_receipt_for_ordinary_pipeline(
    tmp_path: Path,
) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    evidence_dir = tmp_path / "evidence"
    submission = OpenHCSExecutionSubmission(
        plate_id=plate,
        pipeline_document=pipeline,
        global_config=GlobalPipelineConfig(),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=evidence_dir / "observation.pkl"
        )
    )

    execution, source = execute_measured_openhcs_pipeline(
        submission=submission,
        phase_timing=PhaseTimingTrace(
            run_id="ordinary-live",
            pipeline_name="Blur",
            tool="OpenHCS",
        ),
        timing_observer=_ZMQProgressTimingObserver(),
        execution_port=19000 + os.getpid() % 20000,
    )

    receipt = MeasuredPipelineRunReceipt.read(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(evidence_dir)
    )
    inspection = inspect_measured_pipeline_run(evidence_dir)
    assert execution.observation.records_by_axis
    assert any(
        path.suffix.lower() in {".tif", ".tiff"}
        for root in execution.output_roots
        for path in root.rglob("*")
        if path.is_file()
    )
    assert receipt == execution.receipt
    assert receipt.compile_artifact_id is not None
    assert (
        MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(evidence_dir).read_text(
            encoding="utf-8"
        )
        == source
    )
    assert all(item.valid for item in inspection.source_evidence)
    assert inspection.observation_integrity_verified
    assert inspection.results_summary_integrity_verified
    assert inspection.retained_evidence_valid
    assert inspection.warnings == ()
    assert "EXECUTE_OPENHCS" in report_measured_pipeline_run(inspection).markdown


def test_measured_wrapper_uses_declared_main_flow_output_policy(
    tmp_path: Path,
) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    evidence_dir = tmp_path / "evidence"
    output_dir = tmp_path / "outputs"
    submission = OpenHCSExecutionSubmission(
        plate_id=plate,
        pipeline_document=pipeline,
        global_config=GlobalPipelineConfig(
            path_planning_config=PathPlanningConfig(
                well_filter=0,
                global_output_folder=output_dir,
            ),
            materialize_runtime_artifacts=False,
        ),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=evidence_dir / "observation.pkl",
        )
    )

    execution, _ = execute_measured_openhcs_pipeline(
        submission=submission,
        phase_timing=PhaseTimingTrace(
            run_id="runtime-only",
            pipeline_name="Blur",
            tool="OpenHCS",
        ),
        timing_observer=_ZMQProgressTimingObserver(),
        execution_port=21000 + os.getpid() % 20000,
    )

    assert execution.receipt.observed_axis_count == 1
    assert execution.output_roots
    assert all(root.is_relative_to(output_dir) for root in execution.output_roots)
    assert not any(
        path.suffix.lower() in {".tif", ".tiff"}
        for root in execution.output_roots
        for path in root.rglob("*")
        if path.is_file()
    )


def test_ordinary_execution_can_export_outcomes_without_value_observation(
    tmp_path: Path,
) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    export_path = tmp_path / "outcomes.pkl.gz"
    submission = OpenHCSExecutionSubmission(
        plate_id=plate,
        pipeline_document=pipeline,
        global_config=GlobalPipelineConfig(materialize_runtime_artifacts=False),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=export_path,
            runtime_observation_export_scope=ZMQRuntimeObservationExportScope.OUTCOMES,
        )
    )

    completed, _ = execute_measured_openhcs_pipeline(
        submission=submission,
        phase_timing=PhaseTimingTrace(
            run_id="outcomes-live", pipeline_name="Blur", tool="OpenHCS"
        ),
        timing_observer=_ZMQProgressTimingObserver(),
        execution_port=23000 + os.getpid() % 20000,
        require_owned_server=True,
    )

    exported = ZMQRuntimeExecutionOutcomeExport.read(export_path)
    exported.require_successful_axes()
    assert completed.results_summary["well_count"] == exported.axis_count == 1
    assert completed.results_summary["runtime_observation_export_scope"] == "outcomes"
    assert exported.successful_axis_count == 1
    assert exported.output_roots
    assert exported.server_environment is not None
    assert exported.server_environment.python_executable
    assert completed.observation is None
    assert (
        completed.receipt.observation_export_scope
        is ZMQRuntimeObservationExportScope.OUTCOMES
    )
    assert {
        BenchmarkPhase.COMPILE_OPENHCS,
        BenchmarkPhase.EXECUTE_OPENHCS,
        BenchmarkPhase.SERVER_COMPILATION_JOB,
        BenchmarkPhase.SERVER_PIPELINE_JOB,
    } <= {record.phase for record in completed.receipt.phase_timings}
    assert (
        MeasuredPipelineRunReceipt.read(
            MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path)
        )
        == completed.receipt
    )
    inspection = inspect_measured_pipeline_run(tmp_path)
    assert inspection.observation_integrity_verified
    assert inspection.results_summary_integrity_verified
    assert inspection.retained_evidence_valid


def test_measured_repetitions_share_one_owned_ordinary_server(tmp_path: Path) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    observer = _ZMQProgressTimingObserver()
    port = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
        transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode,
    ).data_port
    receipts = []

    with ZMQExecutionClient(
        port=port, persistent=False, progress_callback=observer
    ) as client:
        for repetition in range(2):
            evidence_dir = tmp_path / f"evidence-{repetition}"
            submission = OpenHCSExecutionSubmission(
                plate_id=plate,
                pipeline_document=pipeline,
                global_config=GlobalPipelineConfig(
                    path_planning_config=PathPlanningConfig(
                        well_filter=0,
                        global_output_folder=tmp_path / f"outputs-{repetition}",
                    ),
                    materialize_runtime_artifacts=False,
                ),
            ).with_auxiliary_params(
                ZMQAuxiliaryExecutionParams(
                    runtime_observation_export_path=(
                        evidence_dir / "observation.pkl.gz"
                    ),
                    runtime_observation_export_scope=(
                        ZMQRuntimeObservationExportScope.OUTCOMES
                    ),
                )
            )
            completed, _ = execute_measured_openhcs_pipeline_on_client(
                client=client,
                submission=submission,
                phase_timing=PhaseTimingTrace(
                    run_id=f"repetition-{repetition}",
                    pipeline_name="Blur",
                    tool="OpenHCS",
                ),
                timing_observer=observer,
                expected_axis_count=1,
                require_owned_server=True,
            )
            receipts.append(completed.receipt)

    assert receipts[0].execution_id != receipts[1].execution_id
    assert receipts[0].endpoint_provenance.endpoint_pid == (
        receipts[1].endpoint_provenance.endpoint_pid
    )
    assert receipts[0].endpoint_provenance.endpoint_pid is not None
    assert all(receipt.observed_axis_count == 1 for receipt in receipts)
    assert all(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(
            tmp_path / f"evidence-{repetition}"
        ).is_file()
        for repetition in range(2)
    )


def test_well_throughput_wrapper_runs_a_synthetic_ordinary_plate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import benchmark.well_throughput_scaling as throughput

    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    source_identity = tmp_path / "original_source"
    source_identity.mkdir()
    monkeypatch.setattr(
        throughput,
        "prepare_cellprofiler_input_workspace",
        lambda _request: SimpleNamespace(
            pipeline_import_error=None,
            pipeline_steps=pipeline.pipeline_steps,
            pipeline_config=pipeline.pipeline_config,
            materialization=SimpleNamespace(metadata_path=tmp_path / "metadata.json"),
            execution_plate_path=plate,
        ),
    )
    monkeypatch.setattr(
        throughput,
        "_replicate_source_binding_workspace_wells",
        lambda _path, _well_ids, *, source_well_filter: ("A01",),
    )
    output_root = tmp_path / "throughput"

    result = run_case_well_throughput(
        case_name="synthetic-blur",
        dataset_path=source_identity,
        cppipe_path=tmp_path / "synthetic.cppipe",
        output_root=output_root,
        mode=WellThroughputMode("1w_1t", 1, 1, use_threading=True),
        execution_port=25000 + os.getpid() % 20000,
    )

    assert result.is_successful(), result.error_message
    assert result.execution_route is ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE
    assert result.successful_wells == 1
    assert result.compile_seconds > 0
    assert result.execute_seconds > 0
    (receipt_path,) = output_root.glob(
        "ordinary_run_evidence/*/measured_pipeline_receipt.json"
    )
    receipt = MeasuredPipelineRunReceipt.read(receipt_path)
    assert receipt.plate_id == str(source_identity)
    assert receipt.execution_plate_id == str(plate)
    assert receipt.expected_axis_count == receipt.observed_axis_count == 1
    assert receipt.observation_export_scope is ZMQRuntimeObservationExportScope.OUTCOMES


def test_paper_two_worker_geometry_uses_one_ordinary_measured_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import benchmark.well_throughput_scaling as throughput

    wells = tuple(f"A{index:02d}" for index in range(1, 9))
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path, wells=wells)
    source_identity = tmp_path / "original_source"
    source_identity.mkdir()
    monkeypatch.setattr(
        throughput,
        "prepare_cellprofiler_input_workspace",
        lambda _request: SimpleNamespace(
            pipeline_import_error=None,
            pipeline_steps=pipeline.pipeline_steps,
            pipeline_config=pipeline.pipeline_config,
            materialization=SimpleNamespace(metadata_path=tmp_path / "metadata.json"),
            execution_plate_path=plate,
        ),
    )
    monkeypatch.setattr(throughput, "_synthetic_well_ids", lambda _count: wells)
    monkeypatch.setattr(
        throughput,
        "_replicate_source_binding_workspace_wells",
        lambda _path, _well_ids, *, source_well_filter: wells,
    )
    output_root = tmp_path / "throughput"

    result = run_case_well_throughput(
        case_name="synthetic-blur-eight-well",
        dataset_path=source_identity,
        cppipe_path=tmp_path / "synthetic.cppipe",
        output_root=output_root,
        mode=WellThroughputMode("8w_2c", 8, 2),
        execution_port=26000 + os.getpid() % 20000,
    )

    assert result.is_successful(), result.error_message
    assert result.execution_route is ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE
    assert result.successful_wells == 8
    (receipt_path,) = output_root.glob(
        "ordinary_run_evidence/*/measured_pipeline_receipt.json"
    )
    receipt = MeasuredPipelineRunReceipt.read(receipt_path)
    assert receipt.expected_axis_count == receipt.observed_axis_count == 8
    assert receipt.phase_timings


def test_measured_cli_uses_ordinary_source_session_and_shared_finalizer(
    tmp_path: Path,
) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    source_identity = tmp_path / "source_identity"
    source_identity.mkdir()
    source_file = tmp_path / "pipeline.py"
    source_file.write_text(PipelineDocumentCodec.render(pipeline), encoding="utf-8")
    output_dir = tmp_path / "cli_evidence"
    args = create_benchmark_argument_parser().parse_args(
        [
            "run-measured",
            "--plate",
            str(source_identity),
            "--execution-plate",
            str(plate),
            "--pipeline-source-file",
            str(source_file),
            "--output-dir",
            str(output_dir),
            "--run-id",
            "ordinary-cli",
            "--observation-scope",
            "outcomes",
            "--port",
            str(22000 + os.getpid() % 20000),
            "--no-persistent",
            "--submit-timeout-ms",
            "120000",
            "--wait-timeout-ms",
            "120000",
        ]
    )

    assert args.cli_command.run(args) == 0
    receipt = MeasuredPipelineRunReceipt.read(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir)
    )
    assert receipt.plate_id == str(source_identity)
    assert receipt.execution_plate_id == str(plate)
    assert receipt.run_id == "ordinary-cli"
    assert receipt.pipeline_name == "pipeline"
    assert receipt.observation_export_scope is ZMQRuntimeObservationExportScope.OUTCOMES
    # The CLI measures on its own client, so client phases precede the server's.
    assert BenchmarkPhase.SERVER_PIPELINE_JOB in {
        timing.phase for timing in receipt.phase_timings
    }
    assert all(
        evidence.valid
        for evidence in inspect_measured_pipeline_run(output_dir).source_evidence
    )


def test_stopped_run_is_cancelled_and_refuses_finalization(
    tmp_path: Path, mcp_session
) -> None:
    built, session = mcp_session
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)

    _scope_id, sequence = _start_run(
        built, plate, pipeline, tmp_path / "cancelled_observation.pkl"
    )
    stopped = _call(built, "openhcs_stop_execution", {"force": False})
    assert stopped["status"] in ("accepted", "completed"), stopped
    row = _wait_for_row(
        built, {"status": "accepted", "event_sequence": sequence}, _run_finished
    )

    assert row["terminal_status"] == ExecutionStatus.CANCELLED.value, row
    finalization = _call(
        built,
        "openhcs_finalize_measured_pipeline_run",
        {
            "execution_id": row["execution_id"] or "missing",
            "run_id": "cancelled",
            "pipeline_name": "Blur",
        },
    )
    assert finalization["errors"], finalization
    assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path).exists()
