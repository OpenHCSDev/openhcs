"""Focused gates for the portable installed MCP/Napari demo."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest
from zmqruntime.config import TransportMode

from python_introspect import to_jsonable

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.session import DatasetListState, DatasetRowState
from openhcs.agent.dto.plate import PlateFileQueryRecordSummary
from openhcs.agent.dto.viewer import (
    ViewerWindowDescriptor,
    ViewerWindowValidationSummaryResult,
)
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.mcp import installed_demo
from openhcs.mcp.dev_client import McpDevCommandExecution
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.processing.presets.pipelines import (
    loose_operaphenix_neurite_outgrowth as neurite_preset,
)
from openhcs.domains.microscopy.axes import Microscopy


def _records(tmp_path: Path) -> tuple[PlateFileQueryRecordSummary, ...]:
    records = []
    for channel in (1, 2):
        source_path = tmp_path / f"A01_s001_w{channel}_z001_t001.tif"
        source_path.touch()
        records.append(
            PlateFileQueryRecordSummary(
                kind=PlateFileKind.IMAGE,
                key=source_path.name,
                source_path=str(source_path),
                metadata={
                    Microscopy.Well.name: "A01",
                    Microscopy.Site.name: "1",
                    Microscopy.Channel.name: str(channel),
                    Microscopy.ZIndex.name: "1",
                    Microscopy.Timepoint.name: "1",
                },
            )
        )
    return tuple(records)


def _validation(*, settled: bool) -> ViewerWindowValidationSummaryResult:
    return ViewerWindowValidationSummaryResult(
        schema_version=SCHEMA_VERSION,
        observed=True,
        valid=settled,
        pending_update_count=0 if settled else 8,
        mounted_layer_count=9 if settled else 0,
        nonzero_payload_count=9 if settled else 0,
        viewer=ViewerWindowDescriptor(viewer_type=ViewerType.NAPARI, title="napari"),
    )


def _execution(capability, payload, *, returncode: int = 0) -> McpDevCommandExecution:
    """Frame one declared result exactly as the dev client serializes it."""
    response = McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp"),
        results=(
            McpDevToolResult(tool=capability.name, mcp_error=False, payloads=(payload,)),
        ),
    )
    return McpDevCommandExecution(
        argv=(capability.cli_command or capability.name,),
        payload=to_jsonable(response),
        rendered_output="",
        returncode=returncode,
        server_stderr_tail=None,
    )


def test_portable_source_projects_authoritative_neurite_preset(
    monkeypatch,
    tmp_path: Path,
) -> None:
    records = _records(tmp_path)
    original_builder = neurite_preset.build_loose_operaphenix_neurite_pipeline
    observed: dict[str, object] = {}

    def tracked_builder(inputs):
        pipeline_config, pipeline_steps = original_builder(inputs)
        observed.update(
            inputs=inputs,
            pipeline_config=pipeline_config,
            pipeline_steps=tuple(pipeline_steps),
        )
        return pipeline_config, pipeline_steps

    monkeypatch.setattr(
        neurite_preset,
        "build_loose_operaphenix_neurite_pipeline",
        tracked_builder,
    )
    source, endpoint = installed_demo.build_portable_neurite_source(
        plate_path=tmp_path,
        output_root=tmp_path / "analysis",
        viewer_port=43123,
        source_records=records,
        viewer=True,
    )

    document = PipelineDocumentCodec.from_source(source)
    expected_steps = observed["pipeline_steps"]

    assert document.pipeline_config == observed["pipeline_config"]
    assert isinstance(expected_steps, tuple)
    assert tuple(step.name for step in document.pipeline_steps) == tuple(
        step.name for step in expected_steps
    )
    assert endpoint.port == 43123
    assert endpoint.mode is TransportMode.TCP
    assert all(
        step.napari_streaming_config.enabled
        and step.napari_streaming_config.persistent
        and step.napari_streaming_config.port == 43123
        and step.napari_streaming_config.transport_mode is TransportMode.TCP
        for step in document.pipeline_steps
    )


def test_installed_demo_import_defers_optional_neurite_preset(tmp_path: Path) -> None:
    blocked_module = (
        "openhcs.processing.presets.pipelines.loose_operaphenix_neurite_outgrowth"
    )
    source = f"""
import builtins
from importlib.metadata import distribution

real_import = builtins.__import__

def guarded_import(name, *args, **kwargs):
    if name == {blocked_module!r}:
        raise AssertionError(f"optional preset imported eagerly: {{name}}")
    return real_import(name, *args, **kwargs)

builtins.__import__ = guarded_import
entry_point = next(
    item
    for item in distribution("openhcs").entry_points
    if item.group == "console_scripts" and item.name == "openhcs-mcp-demo"
)
assert callable(entry_point.load())
"""

    result = subprocess.run(
        [sys.executable, "-c", source],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr


def test_feature_enhancement_declaration_defers_native_image_runtimes(
    tmp_path: Path,
) -> None:
    source = """
import sys
from openhcs.processing.backends.cellprofiler.feature_enhancement import (
    enhance_or_suppress_features,
)
assert callable(enhance_or_suppress_features)
execution_modules = {
    "scipy.linalg",
    "scipy.ndimage",
    "scipy.special",
    "skimage",
}
unexpected = sorted(execution_modules.intersection(sys.modules))
assert not unexpected, f"execution runtimes imported by declaration: {unexpected}"
"""

    result = subprocess.run(
        [sys.executable, "-c", source],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr


def test_analysis_submodule_import_does_not_load_unrelated_backends(
    tmp_path: Path,
) -> None:
    source = """
import sys
from openhcs.processing.backends.analysis import region_properties
assert region_properties.LabelRegionPropertiesBackendStrategy.for_memory_type()
prefix = "openhcs.processing.backends.analysis."
unexpected = sorted(
    name
    for name in sys.modules
    if name.startswith(prefix) and name != f"{prefix}region_properties"
)
assert not unexpected, f"unrelated analysis backends imported: {unexpected}"
"""

    result = subprocess.run(
        [sys.executable, "-c", source],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr


def test_portable_source_normalization_defers_catalog_and_execution_runtimes(
    tmp_path: Path,
) -> None:
    pipeline_source, _endpoint = installed_demo.build_portable_neurite_source(
        plate_path=tmp_path,
        output_root=tmp_path / "analysis",
        viewer_port=43124,
        source_records=_records(tmp_path),
        viewer=False,
    )
    source_path = tmp_path / "portable_pipeline.py"
    source_path.write_text(pipeline_source, encoding="utf-8")
    probe = """
import sys
from pathlib import Path
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.processing.backends.lib_registry.registry_service import RegistryService

def forbidden_catalog_discovery(cls):
    raise AssertionError("pipeline normalization requested full catalog discovery")

RegistryService.get_all_functions_with_metadata = classmethod(
    forbidden_catalog_discovery
)
baseline_modules = frozenset(sys.modules)
PipelineDocumentCodec.from_source(Path(sys.argv[1]).read_text(encoding="utf-8"))
execution_prefixes = (
    "centrosome.cpmorphology",
    "centrosome.zernike",
    "scipy.interpolate",
    "scipy.linalg",
    "scipy.ndimage",
    "scipy.special",
    "skimage",
)
unexpected = sorted(
    name
    for name in sys.modules
    if name not in baseline_modules and name.startswith(execution_prefixes)
)
assert not unexpected, f"execution runtimes imported by pipeline source: {unexpected}"
"""

    result = subprocess.run(
        [sys.executable, "-c", probe, str(source_path)],
        cwd=Path(__file__).resolve().parents[2],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr


def test_headless_portable_source_disables_every_viewer_config(
    tmp_path: Path,
) -> None:
    source, _endpoint = installed_demo.build_portable_neurite_source(
        plate_path=tmp_path,
        output_root=tmp_path / "analysis",
        viewer_port=43124,
        source_records=_records(tmp_path),
        viewer=False,
    )

    document = PipelineDocumentCodec.from_source(source)

    assert all(
        not step.napari_streaming_config.enabled
        and not step.napari_streaming_config.persistent
        for step in document.pipeline_steps
    )


def test_installed_demo_phase_reporting_preserves_json_stdout(capsys) -> None:
    installed_demo._report_phase("starting MCP session")

    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == "Installed demo phase: starting MCP session\n"


def test_command_payload_decodes_the_declared_result() -> None:
    capability = agent_capabilities.validate_viewer_window_state
    validation = _validation(settled=True)

    payload = installed_demo._command_payload(
        _execution(capability, validation),
        capability=capability,
        payload_type=ViewerWindowValidationSummaryResult,
    )

    assert payload == validation


def test_command_payload_rejects_a_missing_declared_result() -> None:
    capability = agent_capabilities.validate_viewer_window_state

    with pytest.raises(installed_demo.InstalledDemoFailure, match="returned no"):
        installed_demo._command_payload(
            _execution(agent_capabilities.query_plate_files, _validation(settled=True)),
            capability=capability,
            payload_type=ViewerWindowValidationSummaryResult,
        )


def _dataset_row(root: Path, terminal_status: str | None) -> DatasetRowState:
    return DatasetRowState(
        scope_id=str(root), name=root.name, root=str(root), pipeline_path=None,
        selected=True, initialized=True, compiled=True, init_pending=False,
        compile_pending=False, execution_active=False, status_prefix="",
        orchestrator_state=None, execution_id=None, terminal_status=terminal_status,
        runtime_state=None, runtime_percent=None, queue_position=None,
    )


@pytest.mark.parametrize("terminal_status", ("complete", "failed"))
def test_execute_pipeline_runs_the_session_journey_and_reads_its_row(
    monkeypatch,
    tmp_path: Path,
    terminal_status: str,
) -> None:
    plate = tmp_path / "plate"
    calls = []
    rows = (
        _dataset_row(tmp_path / "other", "failed"),
        _dataset_row(plate, terminal_status),
    )

    def fake_run_mcp(client, argv, *, capability, payload_type, timeout_seconds):
        calls.append((client, tuple(argv), capability, payload_type, timeout_seconds))
        return DatasetListState(
            rows=rows, selected_scope_ids=(str(plate),), execution_state="idle",
        )

    monkeypatch.setattr(installed_demo, "_run_mcp", fake_run_mcp)
    client = object()

    def execute():
        return installed_demo._execute_pipeline(
            client,
            plate_path=plate,
            source_path=tmp_path / "pipeline.py",
            runtime_port=43125,
        )

    if terminal_status == "complete":
        assert execute() == rows[1]
    else:
        with pytest.raises(installed_demo.InstalledDemoFailure, match="failed"):
            execute()
    ((called_client, argv, capability, payload_type, timeout_seconds),) = calls
    assert called_client is client
    assert argv[:2] == ("execute-source", str(plate))
    assert argv[argv.index("--port") + 1] == "43125"
    assert "--wait" in argv and "--no-wait" not in argv
    assert capability is agent_capabilities.session_datasets
    assert payload_type is DatasetListState
    assert timeout_seconds is None


def test_validate_viewer_polls_until_debounced_layers_settle(monkeypatch) -> None:
    responses = iter((_validation(settled=False), _validation(settled=True)))
    calls: list[dict[str, object]] = []

    def fake_run_mcp(client, argv, *, capability, payload_type, timeout_seconds):
        calls.append({"argv": tuple(argv), "timeout_seconds": timeout_seconds})
        return next(responses)

    now = 0.0

    def monotonic() -> float:
        nonlocal now
        now += 1.1
        return now

    monkeypatch.setattr(installed_demo, "_run_mcp", fake_run_mcp)
    monkeypatch.setattr(installed_demo.time, "monotonic", monotonic)
    monkeypatch.setattr(installed_demo.time, "sleep", lambda _seconds: None)

    payload = installed_demo._validate_viewer(object(), viewer_port=43126)

    assert payload.valid is True
    assert len(calls) == 2
    assert calls[1]["timeout_seconds"] == 30.0


def test_validate_viewer_retries_failed_control_commands_until_viewer_starts(
    monkeypatch,
) -> None:
    responses = iter((None, _validation(settled=True)))
    calls: list[dict[str, object]] = []

    def fake_run_mcp(client, argv, *, capability, payload_type, timeout_seconds):
        calls.append({"argv": tuple(argv), "timeout_seconds": timeout_seconds})
        payload = next(responses)
        if payload is None:
            raise installed_demo.InstalledDemoFailure(
                "MCP command failed: viewer_window_state_failed"
            )
        return payload

    now = 0.0

    def monotonic() -> float:
        nonlocal now
        now += 6.0
        return now

    monkeypatch.setattr(installed_demo, "_run_mcp", fake_run_mcp)
    monkeypatch.setattr(installed_demo.time, "monotonic", monotonic)
    monkeypatch.setattr(installed_demo.time, "sleep", lambda _seconds: None)

    payload = installed_demo._validate_viewer(object(), viewer_port=43128)

    assert payload.valid is True
    assert len(calls) == 2


def test_validate_viewer_fails_after_settle_deadline(monkeypatch) -> None:
    now = 0.0

    def monotonic() -> float:
        nonlocal now
        now += 30.0
        return now

    def fake_run_mcp(client, argv, *, capability, payload_type, timeout_seconds):
        return _validation(settled=False)

    monkeypatch.setattr(installed_demo, "_run_mcp", fake_run_mcp)
    monkeypatch.setattr(installed_demo.time, "monotonic", monotonic)
    monkeypatch.setattr(installed_demo.time, "sleep", lambda _seconds: None)

    with pytest.raises(
        installed_demo.InstalledDemoFailure,
        match="viewer validation did not pass",
    ):
        installed_demo._validate_viewer(object(), viewer_port=43127)
