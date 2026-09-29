"""Process-only memory receipts and measured (not causal) retention slopes."""

import os

import pytest

from benchmark.mcp_memory_diagnostic import ProcessMemoryReceipt, retained_slope_kib


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
    repeated = [{"rss": 20}, {"rss": 23}, {"rss": 26}]
    assert retained_slope_kib(repeated, "rss") == 3
    assert retained_slope_kib([{"rss": 30}] * 3, "rss") == 0
    with pytest.raises(ValueError, match="at least two"):
        retained_slope_kib([{"rss": 30}], "rss")
