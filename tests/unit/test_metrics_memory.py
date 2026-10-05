from __future__ import annotations

import time
import threading
import subprocess
import sys

import psutil
import pytest

from benchmark.metrics import memory as memory_module
from benchmark.metrics.memory import MemoryMetric


def test_memory_metric_teardown_wakes_sampler_and_retains_peak(monkeypatch) -> None:
    metric = MemoryMetric(interval_seconds=60)
    waiting = threading.Event()
    wait = metric._stop_event.wait

    def observe_wait(timeout=None):
        waiting.set()
        return wait(timeout)

    monkeypatch.setattr(metric._stop_event, "wait", observe_wait)
    monkeypatch.setattr(
        metric, "_sample_process_tree_rss", lambda: (2 * 1024 * 1024, ())
    )
    with metric:
        assert waiting.wait(timeout=1)

    assert not metric._thread.is_alive()
    assert metric.get_result() == 2.0


@pytest.mark.skipif(sys.platform != "linux", reason="Linux descendant discovery")
def test_memory_sampler_retains_real_child_rss_and_limit_callback_without_host_scan(
    monkeypatch,
) -> None:
    child = subprocess.Popen(
        [sys.executable, "-u", "-c",
         "import sys; pixels = bytearray(32 * 1024 * 1024); print('ready'); sys.stdin.readline()"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
    )
    try:
        assert child.stdout.readline().strip() == "ready"
        callbacks = []
        metric = MemoryMetric(
            max_memory_mb=1,
            on_limit_exceeded=lambda _peak, children: callbacks.append(children),
        )
        parent_rss = metric._process.memory_info().rss
        child_rss = psutil.Process(child.pid).memory_info().rss

        def reject_host_scan(*args, **kwargs):
            pytest.fail("Memory sampling scanned every host process")

        monkeypatch.setattr(psutil.Process, "children", reject_host_scan)
        rss, children = metric._sample_process_tree_rss()
        assert child.pid in {process.pid for process in children}
        assert rss >= parent_rss + child_rss - 1024 * 1024
        metric._peak_rss = rss
        metric._enforce_limit(rss, children)
        assert callbacks == [children]
    finally:
        child.communicate("stop\n", timeout=5)


def test_memory_metric_reenforces_limit_while_rss_remains_high(monkeypatch) -> None:
    callbacks: list[float] = []
    metric = MemoryMetric(
        interval_seconds=0.01,
        max_memory_mb=1.0,
        on_limit_exceeded=lambda peak_mb, _children: callbacks.append(peak_mb),
        limit_callback_interval_seconds=0.01,
    )
    monkeypatch.setattr(
        metric,
        "_sample_process_tree_rss",
        lambda: (2 * 1024 * 1024, ()),
    )

    with metric:
        deadline = time.monotonic() + 0.5
        while len(callbacks) < 2 and time.monotonic() < deadline:
            time.sleep(0.01)

    assert metric.limit_exceeded
    assert len(callbacks) >= 2


def test_memory_metric_can_interrupt_main_once_on_limit(monkeypatch) -> None:
    interrupts: list[None] = []
    metric = MemoryMetric(
        interval_seconds=0.01,
        max_memory_mb=1.0,
        interrupt_main_on_limit=True,
    )
    monkeypatch.setattr(
        metric,
        "_sample_process_tree_rss",
        lambda: (2 * 1024 * 1024, ()),
    )
    monkeypatch.setattr(
        memory_module._thread,
        "interrupt_main",
        lambda: interrupts.append(None),
    )

    with metric:
        deadline = time.monotonic() + 0.5
        while not interrupts and time.monotonic() < deadline:
            time.sleep(0.01)

    assert metric.limit_exceeded
    assert interrupts == [None]


def test_memory_metric_suppresses_own_interrupt_during_cleanup(monkeypatch) -> None:
    metric = MemoryMetric(max_memory_mb=1.0, interrupt_main_on_limit=True)
    metric._thread = type(
        "InterruptingThread",
        (),
        {"join": lambda self, timeout=None: (_ for _ in ()).throw(KeyboardInterrupt())},
    )()
    metric._limit_exceeded = True

    metric.__exit__(None, None, None)
