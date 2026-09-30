"""Execution readiness owns main-thread registry warming and one catalogue future."""

import threading
from concurrent.futures import CancelledError

import pytest
from zmqruntime.execution import ExecutionServer

from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import FunctionCatalogPreparationOutcome
from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation
from openhcs.runtime.zmq_execution_server import ZMQExecutionServer


class PreparedCatalog:
    def __init__(self, events):
        self.events = events

    def prepare(self, **kwargs):
        pytest.fail("Prepared server must not spawn a second catalogue warmup")

    def catalog(self, **kwargs):
        self.events.append("catalog")


def test_direct_server_start_warms_main_thread_before_bind_and_reuses_future(
    monkeypatch,
):
    events = []

    def warm(*, status_callback):
        assert threading.current_thread() is threading.main_thread()
        events.append("warm")

    monkeypatch.setattr(
        FunctionCatalogPreparation, "prepare_persistent_catalog", staticmethod(warm)
    )
    monkeypatch.setattr(ExecutionServer, "start", lambda self: events.append("bind"))
    server = ZMQExecutionServer()
    server._function_catalog = PreparedCatalog(events)
    server._function_catalog_preparation = FunctionCatalogPreparation(
        server._function_catalog
    )
    server.start()
    preparation = server._function_catalog_preparation
    future = preparation.ensure_started()
    assert future.done() and future.exception() is None
    assert preparation._thread is None
    assert events == ["warm", "catalog", "bind"]
    state = preparation.start(ExecutionConnectionSpec(port=22319))
    assert state.outcome is FunctionCatalogPreparationOutcome.READY
    assert preparation.ensure_started() is future
    server.prepare_runtime_capabilities()
    assert events == ["warm", "catalog", "bind"]


def test_startup_warm_failure_cannot_bind_or_report_catalogue_ready(monkeypatch):
    def fail(*, status_callback):
        raise RuntimeError("declared kernel failed")

    monkeypatch.setattr(
        FunctionCatalogPreparation, "prepare_persistent_catalog", staticmethod(fail)
    )
    monkeypatch.setattr(
        ExecutionServer, "start", lambda self: pytest.fail("cannot bind")
    )
    server = ZMQExecutionServer()
    with pytest.raises(RuntimeError, match="declared kernel failed"):
        server.start()
    preparation = server._function_catalog_preparation
    assert preparation._thread is None
    state = preparation.start(ExecutionConnectionSpec(port=22319))
    assert state.outcome is FunctionCatalogPreparationOutcome.FAILED
    assert state.errors[0].message == "declared kernel failed"


def test_cancelled_startup_cannot_warm_or_bind(monkeypatch):
    monkeypatch.setattr(
        FunctionCatalogPreparation,
        "prepare_persistent_catalog",
        staticmethod(lambda *, status_callback: pytest.fail("cannot warm")),
    )
    monkeypatch.setattr(
        ExecutionServer, "start", lambda self: pytest.fail("cannot bind")
    )
    server = ZMQExecutionServer()
    preparation = server._function_catalog_preparation
    preparation.cancel_and_join()
    with pytest.raises(CancelledError):
        server.start()
    assert preparation._future.cancelled()
    assert preparation._thread is None


def test_cancellation_during_warm_preserves_same_cancelled_future(monkeypatch):
    preparation = FunctionCatalogPreparation(PreparedCatalog([]))
    monkeypatch.setattr(
        FunctionCatalogPreparation,
        "prepare_persistent_catalog",
        staticmethod(lambda *, status_callback: preparation._cancellation.cancel()),
    )
    with pytest.raises(CancelledError):
        preparation.prepare_before_serving()
    future = preparation.ensure_started()
    assert future is preparation._future and future.cancelled()
    assert preparation._thread is None


def test_startup_observer_receives_live_kernel_progress_before_binding(monkeypatch):
    preparation = FunctionCatalogPreparation(PreparedCatalog([]))
    observed = []

    def observe(status):
        observed.append((status.message, preparation._future.done()))

    def warm(*, status_callback):
        status_callback("Prepared kernel cache worker 123")
        assert observed[-1] == ("Prepared kernel cache worker 123", False)
        status_callback("Prepared callable example.process")
        assert observed[-1] == ("Prepared callable example.process", False)

    monkeypatch.setattr(
        FunctionCatalogPreparation, "prepare_persistent_catalog", staticmethod(warm)
    )
    preparation.prepare_before_serving(observe)
    assert observed[-1] == ("Function catalog ready", True)
