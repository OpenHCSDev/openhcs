"""The agent's observation option uses ordinary pipeline execution end to end."""

from __future__ import annotations

import asyncio
import os
from pathlib import Path

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
)
from benchmark.timing import BenchmarkPhase, PhaseTimingTrace
from openhcs.agent.dto.execution import (
    PipelineSourceOrchestratorSessionRequest,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.config_service import ConfigService
from openhcs.agent.services.execution_session_service import (
    ExecutionSessionService,
)
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.mcp import server
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
)
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
)


def _synthetic_plate_and_pipeline(tmp_path: Path):
    plate = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(plate),
        grid_size=(1, 1),
        tile_size=(32, 32),
        wavelengths=1,
        z_stack_levels=1,
        num_cells=2,
        wells=["A01"],
        format="ImageXpress",
        random_seed=7,
    ).generate_dataset()
    pipeline = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=[
            FunctionStep(name="Blur", func=(gaussian_blur, {"sigma": 1.0}))
        ],
    )
    return plate, pipeline


def test_headless_observation_export_uses_ordinary_execution(tmp_path: Path) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    source_identity = tmp_path / "source_identity"
    source_identity.mkdir()
    path_policy = AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,), writable_roots=(tmp_path,)
    )
    service = ExecutionSessionService(
        path_policy=path_policy,
        pipeline_service=PipelineAuthoringService(),
        config_service=ConfigService(),
    )
    session = service.create_session_from_pipeline_source_request(
        PipelineSourceOrchestratorSessionRequest.from_fields(
            plate_path=str(source_identity),
            execution_plate_path=str(plate),
            pipeline_source=PipelineDocumentAuthority.render(pipeline),
            port=18000 + os.getpid() % 20000,
            persistent=False,
        )
    )
    export_path = tmp_path / "runtime_observation.pkl"

    status = service.submit_execution(
        session.session_id,
        runtime_observation_export_path=str(export_path),
        wait=True,
        submit_timeout_ms=120_000,
        wait_timeout_ms=120_000,
    )

    assert status.status == "complete", status
    completed = service.require_completed_pipeline_execution(status.job_id)
    assert completed.submission.plate_id == str(source_identity)
    assert completed.submission.execution_plate_id == str(plate)
    assert completed.record.execution_id == status.server_execution_id
    assert completed.record.results_summary is not None
    assert completed.record.end_time is not None
    assert completed.endpoint is not None
    observation = ZMQRuntimeExecutionObservationExport.read(export_path)
    observation.require_valid_observation()
    assert observation.output_roots
    built = server.build_server(
        OpenHCSAgentContext(path_policy=path_policy, execution_service=service)
    )
    finalization = asyncio.run(
        built.call_tool(
            "openhcs_finalize_measured_pipeline_run",
            {
                "job_id": status.job_id,
                "run_id": "headless-ordinary",
                "pipeline_name": "Blur",
            },
        )
    )
    assert finalization[1]["execution_id"] == status.server_execution_id, finalization
    receipt = MeasuredPipelineRunReceipt.read(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path)
    )
    assert receipt.execution_id == status.server_execution_id
    assert receipt.plate_id == str(source_identity)
    assert receipt.execution_plate_id == str(plate)
    assert receipt.compile_artifact_id is None
    assert receipt.phase_timings[0].phase is BenchmarkPhase.SERVER_PIPELINE_JOB
    assert receipt.phase_timings[0].seconds >= 0
    assert all(
        evidence.valid
        for evidence in inspect_measured_pipeline_run(tmp_path).source_evidence
    )


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
    assert receipt == execution.receipt
    assert receipt.compile_artifact_id is not None
    assert (
        MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(evidence_dir).read_text(
            encoding="utf-8"
        )
        == source
    )
    assert all(item.valid for item in inspection.source_evidence)
    assert inspection.warnings == ()
    assert "EXECUTE_OPENHCS" in report_measured_pipeline_run(inspection).markdown


def test_measured_cli_uses_ordinary_source_session_and_shared_finalizer(
    tmp_path: Path,
) -> None:
    plate, pipeline = _synthetic_plate_and_pipeline(tmp_path)
    source_identity = tmp_path / "source_identity"
    source_identity.mkdir()
    source_file = tmp_path / "pipeline.py"
    source_file.write_text(PipelineDocumentAuthority.render(pipeline), encoding="utf-8")
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
    assert receipt.phase_timings[0].phase is BenchmarkPhase.SERVER_PIPELINE_JOB
    assert all(
        evidence.valid
        for evidence in inspect_measured_pipeline_run(output_dir).source_evidence
    )
