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
from openhcs.mcp.memory_diagnostic import (
    DiagnosticSourceIdentity,
    ProcessMemoryReceipt,
    RetentionMetric,
    read_request_sequence,
)
from openhcs.mcp.memory_diagnostic_launch import DiagnosticServerSpec
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
    package = competing / "openhcs" / "mcp"
    package.mkdir(parents=True)
    (package.parent / "__init__.py").write_text(
        "raise RuntimeError('foreign OpenHCS')\n"
    )
    (package / "__init__.py").write_text("")
    (package / "memory_diagnostic.py").write_text(
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
        == authority.import_root / "openhcs/mcp/memory_diagnostic.py"
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
