"""Bounded source controls; no native, socket, viewer or kernel preparation."""

from concurrent.futures import CancelledError
from dataclasses import replace
from threading import Event
from types import SimpleNamespace

import pytest

# Activate the source owner's declared externals before dependency imports.
import openhcs  # noqa: F401
from zmqruntime import OperationCancellation
from zmqruntime.messages import ProcessIdentity

from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import (
    FunctionCatalogPreparationHandle,
    FunctionCatalogPreparationOutcome as Outcome,
)
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.unified_registry import (
    FunctionMetadata,
    ProcessingContract,
)
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import CustomFunctionRuntimeRegistry
from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation


def declaration(image, gain: float = 1.0):
    """A nonexecuted public-contract probe."""
    raise AssertionError("source controls must never execute a processing function")


@pytest.fixture
def catalog(monkeypatch, tmp_path):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "data"))
    manager = CustomFunctionManager()
    metadata = FunctionMetadata(
        name="declaration", func=declaration,
        contract=ProcessingContract.FLEXIBLE,
        registry=SimpleNamespace(library_name="probe"),
        module=__name__, doc=declaration.__doc__,
    )
    monkeypatch.setattr(RegistryService, "_metadata_cache", {"probe:declaration": metadata})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", manager.source_revision())

    def projected_metadata(self, **kwargs):
        # Model the original registry/source owners publishing their revision.
        CustomFunctionRuntimeRegistry._source_revision = manager.source_revision()
        return RegistryService._metadata_cache

    monkeypatch.setattr(FunctionCatalogService, "_all_metadata", projected_metadata)
    kernel_calls = []
    monkeypatch.setattr(
        RegistryService, "prepare_persistent_catalog",
        lambda **kwargs: kernel_calls.append("kernel"),
    )
    return FunctionCatalogService(), manager, kernel_calls


def handle():
    # Nominal identity only: these controls never connect to this port.
    return FunctionCatalogPreparationHandle(
        ExecutionConnectionSpec(port=22319), ProcessIdentity.current()
    )


def test_both_public_views_are_warm(catalog, monkeypatch):
    service, _, _ = catalog
    calls = []
    original = service._entry

    def entry(*args, **kwargs):
        calls.append(args[2:4])
        return original(*args, **kwargs)

    monkeypatch.setattr(service, "_entry", entry)
    assert not service.projections_current()
    service.prepare_projections()
    assert service.projections_current()
    assert len(calls) == 2
    for compact in (False, True, False, True):
        page = service.catalog(compact_signatures=compact)
        assert service.search(query="declaration", compact_signatures=compact).items == page.items
        service.require_revision(page.revision)
    assert len(calls) == 2
    assert service.get("probe:declaration").entry.name == "declaration"
    assert service.reference("probe:declaration") is not None


@pytest.mark.parametrize("mutation", ("add", "update", "delete", "body_only"))
def test_stale_success_refreshes_without_kernel_rewarm(catalog, mutation):
    service, manager, kernels = catalog
    preparation = FunctionCatalogPreparation(service)
    first = preparation.ensure_started()
    first.result(timeout=2)
    assert preparation.observe(handle()).outcome is Outcome.READY
    old = RegistryService._metadata_cache
    if mutation == "body_only":
        manager.storage_dir.joinpath("source_probe.py").write_text("# source revision changed\n")
    elif mutation == "delete":
        RegistryService._metadata_cache = {}
    elif mutation == "update":
        RegistryService._metadata_cache = {
            "probe:declaration": replace(old["probe:declaration"], doc="Updated declaration")
        }
    else:
        RegistryService._metadata_cache = {
            **old, "probe:second": replace(old["probe:declaration"], name="second")
        }
    state = preparation.observe(handle())
    assert state.outcome is Outcome.NOT_STARTED
    assert "require preparation" in state.progress.message
    refreshed = preparation.ensure_started()
    assert refreshed is not first
    refreshed.result(timeout=2)
    assert preparation.ensure_started() is refreshed
    assert preparation.observe(handle()).outcome is Outcome.READY
    assert kernels == ["kernel"]
    preparation.cancel_and_join()


def test_current_refresh_coalesces_and_reports_pending(catalog, monkeypatch):
    service, _, _ = catalog
    preparation = FunctionCatalogPreparation(service)
    preparation.ensure_started().result(timeout=2)
    RegistryService._metadata_cache = dict(RegistryService._metadata_cache)
    RegistryService._metadata_cache["probe:second"] = replace(
        RegistryService._metadata_cache["probe:declaration"], name="second"
    )
    started, release = Event(), Event()
    original = service._entry

    def delayed_entry(*args, **kwargs):
        started.set()
        assert release.wait(timeout=2)
        return original(*args, **kwargs)

    monkeypatch.setattr(service, "_entry", delayed_entry)
    future = preparation.ensure_started()
    try:
        assert started.wait(timeout=2)
        assert preparation.ensure_started() is future
        assert preparation.observe(handle()).outcome is Outcome.PENDING
    finally:
        release.set()
    future.result(timeout=2)
    preparation.cancel_and_join()


def test_failure_is_terminal_not_replayed(catalog, monkeypatch):
    service, _, kernels = catalog

    def fail(*args, **kwargs):
        raise ValueError("projection failure witness")

    monkeypatch.setattr(service, "_entry", fail)
    preparation = FunctionCatalogPreparation(service)
    future = preparation.ensure_started()
    with pytest.raises(ValueError, match="failure witness"):
        future.result(timeout=2)
    assert preparation.observe(handle()).outcome is Outcome.FAILED
    assert preparation.ensure_started() is future
    assert kernels == ["kernel"]
    preparation.cancel_and_join()


def test_projection_cancellation_does_not_publish_partial_view(catalog, monkeypatch):
    service, _, _ = catalog
    cancellation = OperationCancellation()
    original = service._entry

    def cancelling_entry(*args, **kwargs):
        cancellation.cancel()
        return original(*args, **kwargs)

    monkeypatch.setattr(service, "_entry", cancelling_entry)
    with pytest.raises(CancelledError):
        service.prepare_projections(cancellation=cancellation)
    assert not service.projections_current()


def test_cancelled_owner_remains_terminal(catalog):
    service, _, kernels = catalog
    preparation = FunctionCatalogPreparation(service)
    preparation.cancel_and_join()
    future = preparation.ensure_started()
    assert future.cancelled()
    assert preparation.observe(handle()).outcome is Outcome.CANCELLED
    assert preparation.ensure_started() is future
    assert not kernels


def test_wrong_incarnation_is_rejected_before_preparation(catalog):
    service, _, kernels = catalog
    preparation = FunctionCatalogPreparation(service)
    identity = ProcessIdentity.current()
    wrong = FunctionCatalogPreparationHandle(
        ExecutionConnectionSpec(port=22319),
        replace(identity, create_time=identity.create_time + 1),
    )
    with pytest.raises(RuntimeError):
        preparation.observe(wrong)
    assert not kernels


def test_startup_uses_original_main_thread_warmup(catalog, monkeypatch):
    service, _, child_kernels = catalog
    main_kernels = []
    monkeypatch.setattr(
        FunctionCatalogPreparation, "prepare_persistent_catalog",
        lambda **kwargs: main_kernels.append("main"),
    )
    preparation = FunctionCatalogPreparation(service)
    preparation.prepare_before_serving()
    assert preparation.observe(handle()).outcome is Outcome.READY
    assert service.projections_current()
    assert main_kernels == ["main"]
    assert not child_kernels
    preparation.cancel_and_join()
