"""Process-only memory receipts and measured (not causal) retention slopes."""

import json
import os
import subprocess
import sys
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Annotated

import pytest

from python_introspect import dataclass_from_mapping

import openhcs
from scripts.mcp_memory_diagnostic import (
    DiagnosticSourceIdentity,
    MemoryDiagnosticReport,
    MemoryDiagnosticMcpClient,
    ProcessMemoryReceipt,
    RetentionMetric,
    read_request_sequence,
)
from scripts.mcp_memory_diagnostic_launch import DiagnosticServerSpec
from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority


def test_process_receipt_uses_current_process_and_reports_gc_boundary():
    before = ProcessMemoryReceipt.capture(collect=False)
    after = ProcessMemoryReceipt.capture(collect=True)
    assert before.pid == after.pid == os.getpid()
    assert before.collected_objects == 0
    assert after.collected_objects >= 0
    assert after.pss_kib > 0
    assert after.rss_kib >= after.pss_kib
    assert after.private_dirty_kib >= 0
    assert after.swap_kib >= 0
    assert after.threads >= 1
    assert after.monotonic_seconds >= before.monotonic_seconds
    assert before.host_mem_available_kib > 0
    assert before.host_swap_used_kib >= 0
    assert before.host_full_psi_avg10 >= 0
    assert before.host_full_psi_avg60 >= 0
    assert before.host_full_psi_avg300 >= 0


def test_slope_distinguishes_warmup_from_repeated_request_growth():
    baseline = ProcessMemoryReceipt.capture(collect=False)
    repeated = [replace(baseline, rss_kib=value) for value in (20, 23, 26)]
    assert ProcessMemoryReceipt.retention_slopes(repeated)["rss_kib"] == 3
    assert ProcessMemoryReceipt.retention_slopes([baseline] * 3)["rss_kib"] == 0
    with pytest.raises(ValueError, match="at least two"):
        ProcessMemoryReceipt.retention_slopes([baseline])


def test_memory_payload_decodes_once_and_rejects_shape_and_type_errors():
    receipt = ProcessMemoryReceipt.capture(collect=False)
    wire = json.loads(json.dumps(asdict(receipt)))
    restored = ProcessMemoryReceipt.from_payload(wire)
    assert restored == receipt
    assert isinstance(restored.native_library_paths, tuple)
    with pytest.raises(ValueError, match="undeclared"):
        ProcessMemoryReceipt.from_payload({**wire, "extra_metric": 0})
    wire["rss_kib"] = True
    with pytest.raises(TypeError, match="rss_kib"):
        ProcessMemoryReceipt.from_payload(wire)


def test_new_metric_requires_only_its_receipt_field_declaration():
    @dataclass(frozen=True)
    class ExtendedReceipt(ProcessMemoryReceipt):
        private_clean_kib: Annotated[
            int, RetentionMetric(lambda sample: sample.private_clean_kib)
        ]

    baseline = ProcessMemoryReceipt.capture(collect=False)
    first = ExtendedReceipt.from_payload(asdict(baseline))
    repeated = [replace(first, private_clean_kib=value) for value in (10, 15, 20)]
    slopes = ExtendedReceipt.retention_slopes(repeated)
    assert slopes["private_clean_kib"] == 5
    assert "private_clean_kib" not in ProcessMemoryReceipt.retention_slopes(
        [baseline] * 3
    )
    assert ExtendedReceipt.retention_changes(repeated[0], repeated[-1])["private_clean_kib"] == 10
    assert "host_mem_available_kib" not in slopes


def test_natural_retention_and_gc_sensitivity_are_separate():
    baseline = ProcessMemoryReceipt.capture(collect=False)
    natural = [replace(baseline, rss_kib=value) for value in (100, 130, 160)]
    collected = replace(natural[-1], rss_kib=120)
    report = MemoryDiagnosticReport(3, (), round_interval_seconds=75, gc_at_end=True)
    report.post_warmup_slopes_kib_per_round = ProcessMemoryReceipt.retention_slopes(natural)
    report.post_gc_change_kib = ProcessMemoryReceipt.retention_changes(natural[-1], collected)
    assert report.post_warmup_slopes_kib_per_round["rss_kib"] == 30
    assert report.post_gc_change_kib["rss_kib"] == -40
    assert MemoryDiagnosticReport(100, ()).rounds == 100
    with pytest.raises(ValueError, match="at least two"):
        MemoryDiagnosticReport(1, ())
    for interval in (-1, float("inf"), float("nan")):
        with pytest.raises(ValueError, match="finite and nonnegative"):
            MemoryDiagnosticReport(2, (), round_interval_seconds=interval)
    for timeout in (0, -1, float("inf"), float("nan")):
        with pytest.raises(ValueError, match="finite and positive"):
            MemoryDiagnosticMcpClient(None, timeout)


def test_large_process_low_host_memory_sample_is_observation_not_veto():
    import asyncio
    from openhcs.mcp.dev_client_core import McpDevToolResult

    sample = replace(ProcessMemoryReceipt.capture(collect=False),
                     rss_kib=4 * 1024**2, host_mem_available_kib=512 * 1024)

    class RecordedClient(MemoryDiagnosticMcpClient):
        async def call(self, name, arguments):
            assert arguments == {"collect": False}
            return McpDevToolResult.from_payload(name, {
                "content": [{"type": "text", "text": json.dumps(asdict(sample))}],
                "isError": False,
            })

    assert asyncio.run(RecordedClient(None, 30).sample(collect=False)) == sample


def test_request_sequence_decodes_existing_owner_and_rejects_mutations(tmp_path):
    from openhcs.agent.capabilities import agent_capabilities
    from openhcs.mcp.dev_client_core import McpDevToolCall

    path = tmp_path / "sequence.json"
    path.write_text(
        json.dumps([{"name": agent_capabilities.health_check.name, "arguments": {}}])
    )
    assert read_request_sequence(path) == (
        McpDevToolCall(agent_capabilities.health_check.name, {}),
    )
    path.write_text(
        json.dumps([{"name": agent_capabilities.create_config.name, "arguments": {}}])
    )
    with pytest.raises(ValueError, match="read-only"):
        read_request_sequence(path)
    path.write_text("[]")
    with pytest.raises(ValueError, match="1..16"):
        read_request_sequence(path)


def test_mutating_declaration_without_side_effects_is_rejected(tmp_path, monkeypatch):
    from openhcs.agent import capabilities

    capability = replace(
        capabilities.get_agent_capability(
            capabilities.agent_capabilities.health_check.name
        ),
        mutating=True,
        side_effects=(),
    )
    assert not capability.read_only
    monkeypatch.setattr(capabilities, "get_agent_capability", lambda name: capability)
    path = tmp_path / "sequence.json"
    path.write_text(json.dumps([{"name": capability.name, "arguments": {}}]))
    with pytest.raises(ValueError, match="read-only"):
        read_request_sequence(path)


def test_integrated_artifact_plan_is_not_admitted_as_read_only(tmp_path):
    from openhcs.agent.capabilities import agent_capabilities, get_agent_capability

    capability = get_agent_capability(
        agent_capabilities.inspect_pipeline_source_artifact_plan.name
    )
    assert capability.mutating
    assert not capability.read_only
    path = tmp_path / "sequence.json"
    path.write_text(json.dumps([{"name": capability.name, "arguments": {}}]))
    with pytest.raises(ValueError, match="read-only"):
        read_request_sequence(path)


@pytest.mark.parametrize("ambient_path", [None, "competing"])
def test_diagnostic_child_retains_selected_source_from_competing_cwd(
    tmp_path, monkeypatch, ambient_path
):
    # Actual source entrypoint and launch owner, but provenance-only mode: no
    # MCP server, GUI, scientific framework, or execution runtime is started.
    competing = tmp_path / "competing"
    (competing / "openhcs").mkdir(parents=True)
    (competing / "openhcs" / "__init__.py").write_text(
        "raise RuntimeError('foreign OpenHCS')\n"
    )
    (competing / "scripts").mkdir()
    (competing / "scripts" / "mcp_memory_diagnostic.py").write_text(
        "raise RuntimeError('foreign diagnostic')\n"
    )
    monkeypatch.delenv("PYTHONPATH", raising=False)
    if ambient_path is not None:
        monkeypatch.setenv("PYTHONPATH", str(competing))
    spec = DiagnosticServerSpec(
        python_executable=sys.executable, data_directory=str(tmp_path)
    )
    child_environment = spec.environment()
    assert "PYTHONPATH" not in child_environment
    # Even a hostile ambient path must not override the selected source root.
    if ambient_path is not None:
        child_environment["PYTHONPATH"] = str(competing)
    completed = subprocess.run(
        [spec.python_executable, *spec.process_args(), "--source-identity"],
        cwd=competing,
        env=child_environment,
        capture_output=True,
        text=True,
        check=True,
        timeout=10,
    )
    identity = dataclass_from_mapping(
        DiagnosticSourceIdentity, json.loads(completed.stdout)
    )
    authority = OpenHCSRuntimeImportAuthority.current()
    identity.require_authority(authority)
    assert (
        Path(identity.diagnostic_source_path)
        == authority.import_root / "scripts/mcp_memory_diagnostic.py"
    )
    assert Path(identity.openhcs_source_path) == Path(openhcs.__file__).resolve()


@pytest.mark.parametrize(
    "path_field", ["diagnostic_source_path", "openhcs_source_path"]
)
def test_source_receipt_rejects_either_foreign_source(path_field, tmp_path):
    identity = replace(
        DiagnosticSourceIdentity.capture(), **{path_field: str(tmp_path / "foreign.py")}
    )
    with pytest.raises(RuntimeError, match="different.*source"):
        identity.require_authority(OpenHCSRuntimeImportAuthority.current())
