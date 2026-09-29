"""Process-only memory receipts and measured (not causal) retention slopes."""

import json
import os
from dataclasses import asdict, dataclass, replace
from typing import Annotated

import pytest

from benchmark.mcp_memory_diagnostic import (
    ProcessMemoryReceipt,
    RetentionMetric,
    read_request_sequence,
)


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
