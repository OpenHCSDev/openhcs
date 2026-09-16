from __future__ import annotations

import argparse
import asyncio
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

import benchmark.cellprofiler_comparison as comparison_module
from benchmark.cellprofiler_benchmark_cli import (
    BenchmarkCliCommand,
    create_benchmark_argument_parser,
)
from benchmark.cellprofiler_comparison import (
    CellProfilerComparisonCase,
    ComparisonMetricPolicy,
    run_comparison_suite,
)
from benchmark.contracts.control import BenchmarkRunInspectionRequest
from benchmark.contracts.run_artifacts import (
    ComparisonRunArtifact,
    StructuredArtifactFormat,
)
from benchmark.contracts.run_receipt import (
    COMPARISON_SUITE_RUN_RECEIPT_SCHEMA_VERSION,
    ComparisonSuiteRunDeclaration,
    ComparisonSuiteRunReceipt,
    ComparisonSuiteRunStatus,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.benchmark_control_service import BenchmarkControlService
from openhcs.mcp import server
from openhcs.mcp.context import OpenHCSAgentContext


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
            {"output_dir": str(output_dir)},
        )
    )
    assert isinstance(result, tuple)
    payload = result[1]
    assert payload["output_dir"] == str(output_dir)
    assert payload["recorded_status"] == ComparisonSuiteRunStatus.COMPLETED.value
    metadata_artifact = next(
        artifact
        for artifact in payload["structured_artifacts"]
        if artifact["relative_path"] == ComparisonRunArtifact.SUITE_METADATA.value
    )
    assert metadata_artifact["format"] == StructuredArtifactFormat.JSON.value
    assert metadata_artifact["declared_identity"] == (
        ComparisonRunArtifact.SUITE_METADATA.value
    )


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
