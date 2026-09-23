from __future__ import annotations

import argparse
import asyncio
import hashlib
import importlib.util
import json
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest
from zmqruntime.messages import ExecutionRecord

import benchmark.cellprofiler_comparison as comparison_module
from benchmark.cellprofiler_benchmark_cli import (
    BenchmarkCliCommand,
    create_benchmark_argument_parser,
)
from benchmark.cellprofiler_comparison import (
    CellProfilerComparisonCase,
    CellProfilerComparisonObservation,
    ComparisonMetricPolicy,
    ToolExecutionSummary,
    append_observations_jsonl,
    run_comparison_suite,
)
from benchmark.contracts.control import (
    BenchmarkCaseDiscoveryRequest,
    BenchmarkRunInspectionRequest,
    MeasuredPipelineRunFinalizationRequest,
    MeasuredPipelineRunInspectionRequest,
)
from benchmark.contracts.measured_run_receipt import (
    MEASURED_PIPELINE_RUN_RECEIPT_SCHEMA_VERSION,
    MeasuredEndpointProvenance,
    MeasuredPipelineRunReceipt,
)
from benchmark.contracts.run_artifacts import (
    ComparisonRunArtifact,
    MeasuredPipelineRunArtifact,
    StructuredArtifactFormat,
)
from benchmark.contracts.run_receipt import (
    COMPARISON_SUITE_RUN_RECEIPT_SCHEMA_VERSION,
    ComparisonSuiteRunDeclaration,
    ComparisonSuiteRunReceipt,
    ComparisonSuiteRunStatus,
)
from benchmark.control import discover_benchmark_cases
from benchmark.control_service import BenchmarkControlService
from benchmark.timing import BenchmarkPhase, PhaseTimingRecord
from openhcs.agent.capabilities import agent_capabilities, get_capability_registry
from openhcs.agent.dto.execution import ExecutionJobRef, ExecutionJobStatus
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.execution_session_service import CompletedPipelineExecution
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.mcp import server
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.runtime.environment_provenance import (
    InstalledDistributionVersion,
    RuntimeEnvironmentSnapshot,
)
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams


def test_benchmark_command_catalog_is_derived_from_registered_commands() -> None:
    commands = BenchmarkCliCommand.registered_commands()
    parser = create_benchmark_argument_parser()
    subparser_action = next(
        action
        for action in parser._actions
        if isinstance(action, argparse._SubParsersAction)
    )

    assert tuple(subparser_action.choices) == tuple(
        command.command_name for command in commands
    )


def test_measured_cli_rejects_existing_evidence_before_execution(
    tmp_path: Path,
) -> None:
    plate = tmp_path / "plate"
    plate.mkdir()
    source_file = tmp_path / "pipeline.py"
    source_file.write_text("pipeline_steps = []\n", encoding="utf-8")
    output_dir = tmp_path / "evidence"
    output_dir.mkdir()
    sentinel = output_dir / "keep.txt"
    sentinel.write_text("keep", encoding="utf-8")
    args = create_benchmark_argument_parser().parse_args(
        [
            "run-measured",
            "--plate",
            str(plate),
            "--pipeline-source-file",
            str(source_file),
            "--output-dir",
            str(output_dir),
            "--run-id",
            "test",
            "--wait-timeout-ms",
            "1000",
        ]
    )

    with pytest.raises(FileExistsError, match="must be empty"):
        args.cli_command.run(args)
    assert sentinel.read_text(encoding="utf-8") == "keep"


@pytest.mark.parametrize("wait_outcome", ("interrupt", "timeout"))
def test_measured_cli_cancels_accepted_ordinary_job_when_wait_stops(
    monkeypatch,
    tmp_path: Path,
    capsys,
    wait_outcome: str,
) -> None:
    plate = tmp_path / "plate"
    plate.mkdir()
    source_file = tmp_path / "pipeline.py"
    source_file.write_text("pipeline_steps = []\n", encoding="utf-8")
    output_dir = tmp_path / "evidence"
    submitted = ExecutionJobRef(
        schema_version="test",
        session_id="session-1",
        job_id="job-1",
        kind="execute",
        uri="test",
        server_execution_id="execution-1",
        status="accepted",
    )
    calls: list[tuple[str, object]] = []

    class FakeExecutionService:
        def create_session_from_pipeline_source_request(self, request):
            return SimpleNamespace(session_id="session-1")

        def submit_execution(self, session_id, **kwargs):
            calls.append(("submit", kwargs["wait"]))
            return submitted

        def wait_job(self, job_id, *, timeout_ms):
            calls.append(("wait", (job_id, timeout_ms)))
            if wait_outcome == "interrupt":
                raise KeyboardInterrupt
            return ExecutionJobStatus(
                schema_version="test",
                session_id="session-1",
                job_id="job-1",
                kind="execute",
                uri="test",
                server_execution_id="execution-1",
                status="running",
                response={"wait_timed_out": True},
            )

        def cancel_job(self, job_id):
            calls.append(("cancel", job_id))
            return {"applied": True}

    monkeypatch.setattr(
        "openhcs.mcp.context.OpenHCSAgentContext",
        lambda *, path_policy: SimpleNamespace(
            execution_service=FakeExecutionService()
        ),
    )
    args = create_benchmark_argument_parser().parse_args(
        [
            "run-measured",
            "--plate",
            str(plate),
            "--pipeline-source-file",
            str(source_file),
            "--output-dir",
            str(output_dir),
            "--run-id",
            "test",
            "--wait-timeout-ms",
            "1000",
        ]
    )

    if wait_outcome == "interrupt":
        assert args.cli_command.run(args) == 130
    else:
        with pytest.raises(RuntimeError, match="did not complete"):
            args.cli_command.run(args)
    assert calls == [
        ("submit", False),
        ("wait", ("job-1", 1000)),
        ("cancel", "job-1"),
    ]
    assert "job-1" in capsys.readouterr().err
    assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir).exists()


def _measured_run_receipt(output_dir: Path) -> MeasuredPipelineRunReceipt:
    output_dir.mkdir()
    pipeline_source = b"pipeline_steps = []\n"
    config_source = b"config = GlobalPipelineConfig()\n"
    MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(output_dir).write_bytes(
        pipeline_source
    )
    MeasuredPipelineRunArtifact.GLOBAL_CONFIG_SOURCE.path_in(output_dir).write_bytes(
        config_source
    )
    observation_path = output_dir / "observation.pkl"
    observation_path.write_bytes(b"opaque runtime observation")
    summary_path = output_dir / "zmq_results_summary.json"
    summary_path.write_text("{}", encoding="utf-8")
    receipt = MeasuredPipelineRunReceipt(
        schema_version=MEASURED_PIPELINE_RUN_RECEIPT_SCHEMA_VERSION,
        run_id="run-1",
        pipeline_name="ordinary",
        plate_id=str(output_dir / "plate"),
        execution_plate_id=None,
        selected_pipeline_path=None,
        execution_id="execution-1",
        pipeline_source_sha256=hashlib.sha256(pipeline_source).hexdigest(),
        global_config_source_sha256=hashlib.sha256(config_source).hexdigest(),
        observation_export_sha256=hashlib.sha256(
            observation_path.read_bytes()
        ).hexdigest(),
        results_summary_sha256=hashlib.sha256(summary_path.read_bytes()).hexdigest(),
        observation_export_path=observation_path,
        results_summary_path=summary_path,
        output_roots=(output_dir / "outputs",),
        phase_timings=(
            PhaseTimingRecord(
                run_id="run-1",
                pipeline_name="ordinary",
                tool="OpenHCS",
                phase=BenchmarkPhase.EXECUTE_OPENHCS,
                seconds=0.25,
            ),
        ),
        endpoint_provenance=MeasuredEndpointProvenance(
            client_python_executable=sys.executable,
            client_openhcs_file="/test/openhcs/__init__.py",
            client_openhcs_version="0.8.6",
            endpoint_application_identifier="openhcs",
            endpoint_openhcs_version="0.8.6",
            endpoint_pid=123,
            endpoint_create_time_epoch_seconds=1.0,
            endpoint_log_file_path=None,
            endpoint_port=23456,
        ),
        completed_at_epoch_seconds=2.0,
    )
    receipt.write(MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir))
    return receipt


def test_case_discovery_shares_exact_selection_across_cli_and_mcp(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    dataset = tmp_path / "images"
    dataset.mkdir()
    pipeline = tmp_path / "pipeline.cppipe"
    pipeline.write_text("CellProfiler Pipeline: http://www.cellprofiler.org\n")
    manifest = tmp_path / "cases.json"
    manifest.write_text(
        json.dumps(
            {
                "cases": [
                    {
                        "name": "present",
                        "dataset_path": str(dataset),
                        "cppipe_path": str(pipeline),
                    },
                    {
                        "name": "missing",
                        "dataset_path": str(tmp_path / "absent"),
                        "cppipe_path": str(tmp_path / "absent.cppipe"),
                    },
                ]
            }
        ),
        encoding="utf-8",
    )
    request = BenchmarkCaseDiscoveryRequest(
        manifest_path=str(manifest), case_names=("present",)
    )
    path_policy = AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,), writable_roots=()
    )
    service = BenchmarkControlService(path_policy)

    selected = service.discover_cases(request)
    all_cases = discover_benchmark_cases(manifest)
    assert tuple(case.name for case in selected.cases) == ("present",)
    assert selected.cases[0].dataset_present is True
    assert selected.cases[0].cppipe_present is True
    assert selected.warnings == ()
    assert len(all_cases.cases) == 2
    assert len(all_cases.warnings) == 1

    args = create_benchmark_argument_parser().parse_args(
        ("list-cases", "--manifest", str(manifest), "--case", "present")
    )
    assert args.cli_command.run(args) == 0
    cli_payload = json.loads(capsys.readouterr().out)
    assert [case["name"] for case in cli_payload["cases"]] == ["present"]

    context = OpenHCSAgentContext(path_policy=path_policy)
    built = server.build_server(context)
    names = {tool.name for tool in asyncio.run(built.list_tools())}
    assert "openhcs_list_benchmark_cases" in names
    mcp_result = asyncio.run(
        built.call_tool(
            "openhcs_list_benchmark_cases",
            {"manifest_path": str(manifest), "case_names": ["present"]},
        )
    )
    assert [case["name"] for case in mcp_result[1]["cases"]] == ["present"]


def test_case_discovery_rejects_duplicate_names_without_acquiring(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = tmp_path / "duplicate.json"
    manifest.write_text(
        json.dumps(
            {
                "cases": [
                    {"name": "same", "dataset_path": "a", "cppipe_path": "a.cppipe"},
                    {"name": "same", "dataset_path": "b", "cppipe_path": "b.cppipe"},
                ]
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setenv("OPENHCS_BENCHMARK_AUTO_ACQUIRE", "1")

    def reject_acquisition(*_args):
        raise AssertionError("Discovery must not acquire manifest roots")

    monkeypatch.setattr(
        "benchmark.contracts.comparison_manifest.materialize_manifest_path_roots",
        reject_acquisition,
    )

    with pytest.raises(ValueError, match="must be unique"):
        discover_benchmark_cases(manifest)


def test_case_discovery_keeps_declared_sources_inside_agent_read_roots(
    tmp_path: Path,
) -> None:
    allowed = tmp_path / "allowed"
    allowed.mkdir()
    manifest = allowed / "cases.json"
    manifest.write_text(
        json.dumps(
            {
                "cases": [
                    {
                        "name": "outside",
                        "dataset_path": str(tmp_path / "outside"),
                        "cppipe_path": str(tmp_path / "outside.cppipe"),
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(allowed,), writable_roots=())
    )

    with pytest.raises(ValueError, match="outside allowed roots"):
        service.discover_cases(
            BenchmarkCaseDiscoveryRequest(manifest_path=str(manifest))
        )


def test_measured_inspection_cli_and_report_share_one_receipt(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output_dir = tmp_path / "measured"
    receipt = _measured_run_receipt(output_dir)
    request = MeasuredPipelineRunInspectionRequest(output_dir=str(output_dir))
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )

    inspection = service.inspect_measured_run(request)
    report = service.report_measured_run(request)

    assert inspection.receipt == receipt
    assert inspection.unreceipted_artifacts == ()
    assert all(item.valid for item in inspection.source_evidence)
    assert inspection.observation_present is True
    assert inspection.results_summary_present is True
    assert inspection.observation_integrity_verified is True
    assert inspection.results_summary_integrity_verified is True
    assert inspection.evidence_valid is True
    assert inspection.warnings == ()
    assert "Retained evidence: verified" in report.markdown
    assert "EXECUTE_OPENHCS: 0.250000 s" in report.markdown

    parser = create_benchmark_argument_parser()
    args = parser.parse_args(("inspect-measured", "--output-dir", str(output_dir)))
    assert args.cli_command.run(args) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["receipt"]["execution_id"] == receipt.execution_id
    assert payload["evidence_valid"] is True
    assert payload["receipt"]["phase_timings"][0]["phase"] == (
        BenchmarkPhase.EXECUTE_OPENHCS.value
    )
    args = parser.parse_args(
        ("inspect-measured", "--output-dir", str(output_dir), "--report")
    )
    assert args.cli_command.run(args) == 0
    assert "EXECUTE_OPENHCS: 0.250000 s" in capsys.readouterr().out


def test_measured_inspection_exposes_artifacts_without_a_valid_receipt(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output_dir = tmp_path / "measured"
    output_dir.mkdir()
    MeasuredPipelineRunArtifact.RESULTS_SUMMARY.path_in(output_dir).write_text(
        "{}\n", encoding="utf-8"
    )
    MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(output_dir).write_text(
        "pipeline_steps = []\n", encoding="utf-8"
    )
    outside = tmp_path / "outside.py"
    outside.write_text("unrelated\n", encoding="utf-8")
    MeasuredPipelineRunArtifact.GLOBAL_CONFIG_SOURCE.path_in(output_dir).symlink_to(
        outside
    )
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(output_dir,), writable_roots=())
    )
    request = MeasuredPipelineRunInspectionRequest(output_dir=str(output_dir))

    inspection = service.inspect_measured_run(request)
    assert inspection.receipt is None
    assert inspection.evidence_valid is False
    assert inspection.unreceipted_artifacts == (
        MeasuredPipelineRunArtifact.RESULTS_SUMMARY,
        MeasuredPipelineRunArtifact.PIPELINE_SOURCE,
    )
    assert any(
        "without a valid success receipt" in item for item in inspection.warnings
    )
    assert (
        "without a valid success receipt"
        in service.report_measured_run(request).markdown
    )

    args = create_benchmark_argument_parser().parse_args(
        ("inspect-measured", "--output-dir", str(output_dir))
    )
    assert args.cli_command.run(args) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["unreceipted_artifacts"] == [
        "zmq_results_summary.json",
        "submitted_pipeline.py",
    ]


def test_measured_inspection_rejects_tampered_and_escaped_evidence(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "measured"
    receipt = _measured_run_receipt(output_dir)
    MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(output_dir).write_text(
        "changed\n", encoding="utf-8"
    )
    escaped = tmp_path / "outside.pkl"
    escaped.write_bytes(b"outside")
    receipt_path = MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir)
    receipt_path.unlink()  # Construct a tampered fixture, not a production rewrite.
    replace(receipt, observation_export_path=escaped).write(receipt_path)
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(output_dir,), writable_roots=())
    )

    inspection = service.inspect_measured_run(
        MeasuredPipelineRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.observation_present is False
    assert inspection.source_evidence[0].valid is False
    assert inspection.evidence_valid is False
    assert any("digest differs" in warning for warning in inspection.warnings)
    assert any("escapes the run" in warning for warning in inspection.warnings)


def test_measured_inspection_detects_tampered_runtime_and_summary(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "measured"
    _measured_run_receipt(output_dir)
    (output_dir / "observation.pkl").write_bytes(b"changed runtime observation")
    MeasuredPipelineRunArtifact.RESULTS_SUMMARY.path_in(output_dir).write_text(
        '{"changed": true}', encoding="utf-8"
    )

    inspection = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(output_dir,), writable_roots=())
    ).inspect_measured_run(
        MeasuredPipelineRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.observation_present is True
    assert inspection.results_summary_present is True
    assert inspection.observation_integrity_verified is False
    assert inspection.results_summary_integrity_verified is False
    assert inspection.evidence_valid is False
    assert "Declared runtime observation digest differs." in inspection.warnings
    assert "Declared execution summary digest differs." in inspection.warnings


def test_measured_inspection_reads_archived_receipt_without_claiming_integrity(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "measured"
    _measured_run_receipt(output_dir)
    path = MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir)
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["schema_version"] = "openhcs.benchmark.measured-pipeline.v1"
    payload.pop("observation_export_sha256")
    payload.pop("results_summary_sha256")
    path.write_text(json.dumps(payload), encoding="utf-8")

    inspection = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(output_dir,), writable_roots=())
    ).inspect_measured_run(
        MeasuredPipelineRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.receipt is not None
    assert inspection.observation_integrity_verified is False
    assert inspection.results_summary_integrity_verified is False
    assert inspection.evidence_valid is False
    assert any("integrity is unverified" in item for item in inspection.warnings)


def test_measured_receipt_reads_older_optional_compile_identity(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "measured"
    _measured_run_receipt(output_dir)
    path = MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir)
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload.pop("compile_artifact_id")
    payload.pop("server_environment")
    path.write_text(json.dumps(payload), encoding="utf-8")

    assert MeasuredPipelineRunReceipt.read(path).compile_artifact_id is None
    assert MeasuredPipelineRunReceipt.read(path).server_environment is None


def test_measured_receipt_round_trips_server_environment(tmp_path: Path) -> None:
    output_dir = tmp_path / "measured"
    receipt = _measured_run_receipt(output_dir)
    environment = RuntimeEnvironmentSnapshot(
        python_executable="/server/bin/python",
        python_version="3.12.3",
        python_implementation="CPython",
        sys_platform="linux",
        machine="x86_64",
        installed_distributions=(InstalledDistributionVersion("numpy", "2.0.0"),),
    )
    path = MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir)

    path.unlink()  # Serialize the variant as a fresh receipt.
    replace(receipt, server_environment=environment).write(path)

    assert MeasuredPipelineRunReceipt.read(path).server_environment == environment


def test_measured_finalization_refuses_missing_server_timing_without_receipt(
    tmp_path: Path,
) -> None:
    observation_path = tmp_path / "observation.pkl"
    observation_path.touch()
    submission = OpenHCSExecutionSubmission(
        plate_id=tmp_path,
        pipeline_document=PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=[]
        ),
        global_config=GlobalPipelineConfig(),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(runtime_observation_export_path=observation_path)
    )

    class CompletedJobService:
        def require_completed_pipeline_execution(self, job_id: str):
            assert job_id == "job-1"
            return CompletedPipelineExecution(
                submission=submission,
                record=ExecutionRecord(
                    execution_id="execution-1",
                    plate_id=str(tmp_path),
                    client_address=None,
                    status="complete",
                    results_summary={},
                ),
                endpoint=None,
            )

    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        ),
        CompletedJobService(),
    )

    with pytest.raises(ValueError, match="no server execution time bounds"):
        service.finalize_measured_run(
            MeasuredPipelineRunFinalizationRequest(
                job_id="job-1", run_id="run-1", pipeline_name="empty"
            )
        )

    assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path).exists()


def test_empty_comparison_run_writes_completed_owned_receipt(tmp_path: Path) -> None:
    output_dir = tmp_path / "run"
    rerun_command = (
        "openhcs-benchmark",
        "run",
        "--manifest",
        "/data/manifest.json",
        "--output-dir",
        str(output_dir),
    )

    observations = run_comparison_suite(
        (),
        output_root=output_dir,
        suite_id="empty-suite",
        coverage_manifest_path=None,
        metric_policy=ComparisonMetricPolicy(collect_memory=False),
        rerun_command=rerun_command,
        rerun_working_directory=tmp_path,
    )

    metadata = json.loads(
        ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir).read_text(
            encoding="utf-8"
        )
    )
    assert observations == ()
    assert metadata["suite_id"] == "empty-suite"
    assert metadata["status"] == "completed"
    assert metadata["schema_version"] == COMPARISON_SUITE_RUN_RECEIPT_SCHEMA_VERSION
    assert metadata["collect_memory_metric"] is False
    assert metadata["case_names"] == []
    assert metadata["completed_observation_count"] == 0
    assert metadata["rerun_command"] == list(rerun_command)
    assert metadata["rerun_working_directory"] == str(tmp_path)
    assert metadata["created_at_epoch_seconds"] <= metadata["finished_at_epoch_seconds"]
    receipt = ComparisonSuiteRunReceipt.read(
        ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir)
    )
    assert receipt.status is ComparisonSuiteRunStatus.COMPLETED
    assert receipt.expected_observation_count == 0
    assert receipt.rerun_command == rerun_command


def test_comparison_run_rejects_occupied_destination_before_loading_manifest(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    sentinel = output_dir / "preserve.txt"
    sentinel.write_text("preserve", encoding="utf-8")

    with pytest.raises(FileExistsError, match="must be empty"):
        run_comparison_suite((), output_root=output_dir, suite_id="blocked")
    args = create_benchmark_argument_parser().parse_args(
        (
            "run",
            "--manifest",
            str(tmp_path / "missing-manifest.json"),
            "--output-dir",
            str(output_dir),
        )
    )
    with pytest.raises(FileExistsError, match="must be empty"):
        args.cli_command.run(args)

    assert sentinel.read_text(encoding="utf-8") == "preserve"
    assert tuple(output_dir.iterdir()) == (sentinel,)


def test_comparison_first_receipt_claim_is_exclusive(tmp_path: Path) -> None:
    receipt = _run_receipt(
        suite_id="first",
        status=ComparisonSuiteRunStatus.RUNNING,
        case_names=(),
        repeats=1,
        completed_observation_count=0,
    )
    path = ComparisonRunArtifact.SUITE_METADATA.path_in(tmp_path)
    receipt.write_new(path)

    with pytest.raises(FileExistsError):
        replace(receipt, suite_id="second").write_new(path)
    assert ComparisonSuiteRunReceipt.read(path).suite_id == "first"


def test_comparison_run_records_failed_status_before_propagating(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    output_dir = tmp_path / "failed-run"
    case = CellProfilerComparisonCase(
        name="failing-case",
        dataset_path=tmp_path / "dataset",
        cppipe_path=tmp_path / "pipeline.cppipe",
    )

    def fail_case(*_args, **_kwargs):
        raise RuntimeError("expected failure")

    monkeypatch.setattr(comparison_module, "_run_comparison_case", fail_case)

    with pytest.raises(RuntimeError, match="expected failure"):
        run_comparison_suite(
            (case,),
            output_root=output_dir,
            suite_id="failed-suite",
        )

    metadata = json.loads(
        ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir).read_text(
            encoding="utf-8"
        )
    )
    assert metadata["status"] == "failed"
    assert metadata["completed_observation_count"] == 0
    receipt = ComparisonSuiteRunReceipt.read(
        ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir)
    )
    assert receipt.expected_observation_count == 1


def test_benchmark_control_inspects_progress_rerun_and_discovered_artifacts(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    _run_receipt(
        suite_id="suite-7",
        status=ComparisonSuiteRunStatus.RUNNING,
        case_names=("one", "two"),
        repeats=2,
        completed_observation_count=2,
        manifest_path=Path("/data/manifest.json"),
        rerun_command=(
            "openhcs-benchmark",
            "run",
            "--manifest",
            "/data/manifest.json",
        ),
        rerun_working_directory=Path("/repo/openhcs"),
    ).write(ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir))
    ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(output_dir).write_text(
        '{"case_name": "one"}\n{"case_name": "two"}\n',
        encoding="utf-8",
    )
    nested = output_dir / "figures"
    nested.mkdir()
    (nested / "plot_data.csv").write_text("x,y\n1,2\n", encoding="utf-8")
    (output_dir / "runtime.log").write_text("not structured", encoding="utf-8")

    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,),
            writable_roots=(),
        )
    )
    inspection = service.inspect_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.suite_id == "suite-7"
    assert inspection.recorded_status is ComparisonSuiteRunStatus.RUNNING
    assert inspection.completed_observation_count == 2
    assert inspection.expected_observation_count == 4
    assert inspection.progress_fraction == 0.5
    assert inspection.rerun_command[0] == "openhcs-benchmark"
    assert inspection.rerun_working_directory == "/repo/openhcs"
    assert {artifact.relative_path for artifact in inspection.structured_artifacts} == {
        "figures/plot_data.csv",
        "observations.jsonl",
        "suite_metadata.json",
    }
    assert inspection.warnings == ()
    artifacts = {
        artifact.relative_path: artifact for artifact in inspection.structured_artifacts
    }
    assert artifacts["figures/plot_data.csv"].format is StructuredArtifactFormat.CSV
    assert artifacts["suite_metadata.json"].declared_identity is (
        ComparisonRunArtifact.SUITE_METADATA
    )


def test_benchmark_artifact_paging_is_shared_by_cli_and_service(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    for name in ("a.csv", "b.json", "c.jsonl"):
        (output_dir / name).write_text("{}\n", encoding="utf-8")
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )
    first = service.inspect_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir), artifact_limit=2)
    )
    second = service.inspect_run(
        BenchmarkRunInspectionRequest(
            output_dir=str(output_dir), artifact_offset=2, artifact_limit=2
        )
    )
    assert [item.relative_path for item in first.structured_artifacts] == [
        "a.csv",
        "b.json",
    ]
    assert first.next_artifact_offset == 2
    assert [item.relative_path for item in second.structured_artifacts] == ["c.jsonl"]
    assert second.next_artifact_offset is None

    args = create_benchmark_argument_parser().parse_args(
        (
            "inspect-run",
            "--output-dir",
            str(output_dir),
            "--artifact-offset",
            "2",
            "--artifact-limit",
            "2",
        )
    )
    assert args.cli_command.run(args) == 0
    payload = json.loads(capsys.readouterr().out)
    assert [item["relative_path"] for item in payload["structured_artifacts"]] == [
        "c.jsonl"
    ]
    assert payload["next_artifact_offset"] is None


def test_comparison_report_uses_typed_observations_for_cli_and_mcp(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    _run_receipt(
        suite_id="suite-report",
        status=ComparisonSuiteRunStatus.COMPLETED,
        case_names=("one",),
        repeats=2,
        completed_observation_count=2,
    ).write(ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir))
    native = ToolExecutionSummary(
        tool="CellProfiler",
        success=True,
        output_path=str(output_dir),
        execution_seconds=2.0,
        total_metric_seconds=2.0,
        peak_memory_mb=None,
        cached=False,
        error_message=None,
        phase_seconds={},
    )
    candidate = replace(native, tool="OpenHCS", execution_seconds=1.0)
    observations = tuple(
        CellProfilerComparisonObservation(
            suite_id="suite-report",
            case_name="one",
            repetition=repetition,
            dataset_id="one",
            assay_category=None,
            module_category=None,
            cppipe_path="one.cppipe",
            equivalent=True,
            difference_count=0,
            numeric_abs_tolerance=1e-6,
            numeric_rel_tolerance=1e-6,
            native_cellprofiler=native,
            openhcs=candidate,
        )
        for repetition in (1, 2)
    )
    append_observations_jsonl(
        ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(output_dir),
        observations,
    )
    request = BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )
    report = service.report_run(request)
    assert "| one | 2 | 2 | 2 | 2.000 | 1.000 |" in report.markdown
    assert "not, by themselves, a matched-concurrency performance claim" in (
        report.markdown
    )
    assert report.warnings == ()

    args = create_benchmark_argument_parser().parse_args(
        ("inspect-run", "--output-dir", str(output_dir), "--report")
    )
    assert args.cli_command.run(args) == 0
    assert capsys.readouterr().out == report.markdown

    if importlib.util.find_spec("mcp") is not None:
        built = server.build_server(
            OpenHCSAgentContext(
                path_policy=AgentPathPolicy.with_roots(
                    readable_roots=(tmp_path,), writable_roots=()
                )
            )
        )
        result = asyncio.run(
            built.call_tool(
                "openhcs_report_benchmark_run",
                {"output_dir": str(output_dir)},
            )
        )
        assert result[1]["markdown"] == report.markdown

    append_observations_jsonl(
        ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(output_dir),
        (replace(observations[0], suite_id="foreign"),),
    )
    foreign_report = service.report_run(request)
    assert "| one | 2 | 2 | 2 | 2.000 | 1.000 |" in foreign_report.markdown
    assert any("another suite identity" in item for item in foreign_report.warnings)


def test_comparison_report_warns_on_invalid_observation(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    _run_receipt(
        suite_id="suite-report",
        status=ComparisonSuiteRunStatus.COMPLETED,
        case_names=("one",),
        repeats=1,
        completed_observation_count=1,
    ).write(ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir))
    ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(output_dir).write_text(
        '{"suite_id": "other", "case_name": "one", "repetition": 1}\n',
        encoding="utf-8",
    )
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )
    report = service.report_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    )
    assert "No validated comparison observations are available." in report.markdown
    assert any("invalid" in warning for warning in report.warnings)


def test_comparison_report_bounds_invalid_observation_warnings(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    _run_receipt(
        suite_id="suite-report",
        status=ComparisonSuiteRunStatus.COMPLETED,
        case_names=("one",),
        repeats=1,
        completed_observation_count=0,
    ).write(ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir))
    ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(output_dir).write_text(
        "{}\n" * 100,
        encoding="utf-8",
    )

    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )
    report = service.report_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    )

    assert len(report.warnings) == 32
    assert report.warnings[-1] == "Additional evidence warnings omitted."
    assert len(report.markdown) < 5_000


def test_comparison_inspection_refuses_oversized_receipt(tmp_path: Path) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir).write_text(
        " " * 1_000_001,
        encoding="utf-8",
    )

    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )
    inspection = service.inspect_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.suite_id is None
    assert inspection.warnings == (
        "suite_metadata.json exceeds the inspection size limit.",
    )


@pytest.mark.parametrize(
    ("offset", "limit"),
    ((-1, 1), (False, 1), (0, 0), (0, 513), (0, True)),
)
def test_benchmark_artifact_page_request_rejects_invalid_bounds(
    offset: int, limit: int
) -> None:
    with pytest.raises(ValueError, match="artifact_(offset|limit)"):
        BenchmarkRunInspectionRequest(
            output_dir="run", artifact_offset=offset, artifact_limit=limit
        )


def test_benchmark_control_rejects_paths_outside_agent_policy(
    tmp_path: Path,
) -> None:
    allowed = tmp_path / "allowed"
    allowed.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(
            readable_roots=(allowed,),
            writable_roots=(),
        )
    )

    with pytest.raises(ValueError, match="outside allowed roots"):
        service.inspect_run(BenchmarkRunInspectionRequest(output_dir=str(outside)))


def test_benchmark_inspection_does_not_follow_escaped_artifact_symlinks(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "run"
    output_dir.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    metadata = outside / "suite_metadata.json"
    _run_receipt(
        suite_id="outside-suite",
        status=ComparisonSuiteRunStatus.COMPLETED,
        case_names=("one",),
        repeats=1,
        completed_observation_count=1,
    ).write(metadata)
    (outside / "observations.jsonl").write_text(
        '{"case_name": "one"}\n', encoding="utf-8"
    )
    (outside / "plot_data.csv").write_text("x,y\n1,2\n", encoding="utf-8")
    (output_dir / "suite_metadata.json").symlink_to(metadata)
    (output_dir / "observations.jsonl").symlink_to(outside / "observations.jsonl")
    (output_dir / "plot_data.csv").symlink_to(outside / "plot_data.csv")

    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(readable_roots=(output_dir,), writable_roots=())
    )
    inspection = service.inspect_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.suite_id is None
    assert inspection.completed_observation_count == 0
    assert inspection.structured_artifacts == ()
    assert any(
        "suite_metadata.json is absent or escapes" in item
        for item in inspection.warnings
    )
    assert any("observations.jsonl escapes" in item for item in inspection.warnings)
    assert any("Structured artifact escapes" in item for item in inspection.warnings)


def test_benchmark_control_marks_historical_receipt_gaps_without_guessing(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "historical"
    output_dir.mkdir()
    ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir).write_text(
        json.dumps({"suite_id": "historical-suite"}),
        encoding="utf-8",
    )
    service = BenchmarkControlService(
        AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,),
            writable_roots=(),
        )
    )

    inspection = service.inspect_run(
        BenchmarkRunInspectionRequest(output_dir=str(output_dir))
    )

    assert inspection.recorded_status is None
    assert inspection.rerun_command == ()
    assert len(inspection.warnings) == 1
    assert "not a current typed run receipt" in inspection.warnings[0]


def test_benchmark_capability_uses_generated_mcp_request_binding(
    tmp_path: Path,
) -> None:
    if importlib.util.find_spec("mcp") is None:
        return

    output_dir = tmp_path / "run"
    output_dir.mkdir()
    _run_receipt(
        suite_id="mcp-suite",
        status=ComparisonSuiteRunStatus.COMPLETED,
        case_names=(),
        repeats=1,
        completed_observation_count=0,
        rerun_command=("openhcs-benchmark", "run", "--manifest", "manifest.json"),
        rerun_working_directory=tmp_path,
    ).write(ComparisonRunArtifact.SUITE_METADATA.path_in(output_dir))
    context = OpenHCSAgentContext(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,),
            writable_roots=(),
        )
    )
    built = server.build_server(context)
    tools = asyncio.run(built.list_tools())

    assert "openhcs_inspect_benchmark_run" in {tool.name for tool in tools}
    result = asyncio.run(
        built.call_tool(
            "openhcs_inspect_benchmark_run",
            {"output_dir": str(output_dir), "artifact_limit": 1},
        )
    )
    assert isinstance(result, tuple)
    payload = result[1]
    assert payload["output_dir"] == str(output_dir)
    assert payload["recorded_status"] == ComparisonSuiteRunStatus.COMPLETED.value
    assert payload["next_artifact_offset"] is None
    metadata_artifact = next(
        artifact
        for artifact in payload["structured_artifacts"]
        if artifact["relative_path"] == ComparisonRunArtifact.SUITE_METADATA.value
    )
    assert metadata_artifact["format"] == StructuredArtifactFormat.JSON.value
    assert metadata_artifact["declared_identity"] == (
        ComparisonRunArtifact.SUITE_METADATA.value
    )


def test_measured_inspection_and_report_are_expert_mcp_tools(tmp_path: Path) -> None:
    if importlib.util.find_spec("mcp") is None:
        return

    output_dir = tmp_path / "measured"
    _measured_run_receipt(output_dir)
    context = OpenHCSAgentContext(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=()
        )
    )
    built = server.build_server(context)
    names = {tool.name for tool in asyncio.run(built.list_tools())}
    assert {
        "openhcs_inspect_measured_pipeline_run",
        "openhcs_report_measured_pipeline_run",
        "openhcs_finalize_measured_pipeline_run",
    } <= names
    finalizer = next(
        tool
        for tool in asyncio.run(built.list_tools())
        if tool.name == "openhcs_finalize_measured_pipeline_run"
    )
    assert {"job_id", "run_id", "pipeline_name"} <= set(
        finalizer.inputSchema["properties"]
    )

    inspected = asyncio.run(
        built.call_tool(
            "openhcs_inspect_measured_pipeline_run",
            {"output_dir": str(output_dir)},
        )
    )
    reported = asyncio.run(
        built.call_tool(
            "openhcs_report_measured_pipeline_run",
            {"output_dir": str(output_dir)},
        )
    )

    assert inspected[1]["receipt"]["execution_id"] == "execution-1"
    assert inspected[1]["unreceipted_artifacts"] == []
    assert inspected[1]["source_evidence"][0]["valid"] is True
    assert inspected[1]["evidence_valid"] is True
    assert "EXECUTE_OPENHCS" in reported[1]["markdown"]

    MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir).unlink()
    interrupted = asyncio.run(
        built.call_tool(
            "openhcs_inspect_measured_pipeline_run",
            {"output_dir": str(output_dir)},
        )
    )
    assert interrupted[1]["receipt"] is None
    assert interrupted[1]["evidence_valid"] is False
    assert set(interrupted[1]["unreceipted_artifacts"]) == {
        artifact.value
        for artifact in MeasuredPipelineRunArtifact
        if artifact.finalizer_output
        and artifact is not MeasuredPipelineRunArtifact.RECEIPT
    }


def test_benchmark_extension_projects_its_declared_capability() -> None:
    capabilities = get_capability_registry().capabilities

    assert "openhcs_inspect_benchmark_run" in {
        capability.name for capability in capabilities
    }
    assert agent_capabilities.inspect_benchmark_run.name == (
        "openhcs_inspect_benchmark_run"
    )


def test_direct_benchmark_capability_lookup_loads_extension_first() -> None:
    repository_root = Path(__file__).resolve().parents[2]
    probe = subprocess.run(
        (
            sys.executable,
            "-c",
            (
                "from openhcs.agent.capabilities import "
                "get_agent_capability_declaration; "
                "declaration = get_agent_capability_declaration("
                "'openhcs_inspect_benchmark_run'); "
                "assert declaration.name == 'openhcs_inspect_benchmark_run'"
            ),
        ),
        cwd=repository_root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert probe.returncode == 0, probe.stderr or probe.stdout


def test_product_imports_without_benchmark_package() -> None:
    repository_root = Path(__file__).resolve().parents[2]
    probe_source = """
import sys


class BlockBenchmark:
    def find_spec(self, fullname, path=None, target=None):
        if fullname == "benchmark" or fullname.startswith("benchmark."):
            raise ModuleNotFoundError(fullname, name=fullname)


sys.meta_path.insert(0, BlockBenchmark())
import openhcs.agent.capabilities
import openhcs.mcp.context
import openhcs.mcp.server
from openhcs.agent.capabilities import get_capability_registry

assert "openhcs_inspect_benchmark_run" not in {
    capability.name for capability in get_capability_registry().capabilities
}
assert not any(
    name == "benchmark" or name.startswith("benchmark.") for name in sys.modules
)
"""
    probe = subprocess.run(
        (
            sys.executable,
            "-c",
            probe_source,
        ),
        cwd=repository_root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert probe.returncode == 0, probe.stderr or probe.stdout


def test_capability_discovery_does_not_import_benchmark_execution_modules() -> None:
    repository_root = Path(__file__).resolve().parents[2]
    probe = subprocess.run(
        (
            sys.executable,
            "-c",
            (
                "import sys; import openhcs.agent.capabilities; "
                "blocked = sorted(name for name in sys.modules "
                "if name in {'benchmark.cellprofiler_benchmark_cli', "
                "'benchmark.cellprofiler_comparison', 'benchmark.runner'}); "
                "raise SystemExit(str(blocked) if blocked else 0)"
            ),
        ),
        cwd=repository_root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert probe.returncode == 0, probe.stderr or probe.stdout


def _run_receipt(
    *,
    suite_id: str,
    status: ComparisonSuiteRunStatus,
    case_names: tuple[str, ...],
    repeats: int,
    completed_observation_count: int,
    manifest_path: Path | None = None,
    rerun_command: tuple[str, ...] = (),
    rerun_working_directory: Path | None = None,
) -> ComparisonSuiteRunReceipt:
    updated_at = 2.0
    declaration = ComparisonSuiteRunDeclaration(
        suite_id=suite_id,
        speedup_target=1.0,
        created_at_epoch_seconds=1.0,
        native_reference_root=None,
        require_native_reference=False,
        discard_openhcs_outputs=False,
        continue_on_error=False,
        collect_memory_metric=True,
        openhcs_execution_port=None,
        manifest_path=manifest_path,
        case_names=case_names,
        repeats=repeats,
        rerun_command=rerun_command,
        rerun_working_directory=rerun_working_directory,
    )
    return ComparisonSuiteRunReceipt.from_declaration(
        declaration,
        status=status,
        completed_observation_count=completed_observation_count,
        updated_at_epoch_seconds=updated_at,
    )
