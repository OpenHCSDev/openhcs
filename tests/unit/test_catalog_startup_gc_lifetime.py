"""Startup graph lifetime must not exempt later jobs or retired sources from GC."""

from __future__ import annotations

import subprocess
import sys
import textwrap

import pytest
from zmqruntime import OperationCancellation

from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation


def test_startup_freeze_preserves_job_gc_and_releases_source_cycles():
    # Isolate permanent-generation state from pytest and its plugin objects.
    program = textwrap.dedent("""        import gc
        import os
        import weakref
        from openhcs.processing.backends.lib_registry.registry_service import RegistryService
        from openhcs.processing.custom_functions.source_namespace import (
            CustomFunctionSource, CustomFunctionSourceNamespace,
        )
        bindings = {"__name__": "startup_lifetime_control"}
        exec("def captured_source(): pass", bindings)
        function = bindings["captured_source"]
        namespace = CustomFunctionSourceNamespace(
            CustomFunctionSource("captured_source", "lifetime-control"), bindings,
        )
        namespace.bind(function)
        captured = weakref.ref(function)
        RegistryService.freeze_prepared_catalog_once()
        assert gc.isenabled()
        assert gc.get_freeze_count() > 0
        del function, namespace, bindings
        gc.collect()
        assert captured() is not None

        child = os.fork()
        if child == 0:
            assert RegistryService._startup_heap_prepared
            assert RegistryService._startup_heap_frozen
            inherited_count = gc.get_freeze_count()
            RegistryService.freeze_prepared_catalog_once()
            assert gc.get_freeze_count() == inherited_count
            assert gc.isenabled()
            RegistryService.release_prepared_catalog()
            gc.collect()
            assert captured() is None
            os._exit(0)
        _, status = os.waitpid(child, 0)
        assert os.waitstatus_to_exitcode(status) == 0
        assert RegistryService._startup_heap_frozen
        assert captured() is not None

        class Job:
            pass
        job = Job()
        job.cycle = job
        pending_job = weakref.ref(job)
        del job
        gc.collect()
        assert pending_job() is None

        RegistryService.clear_metadata_cache()
        assert gc.get_freeze_count() == 0
        gc.collect()
        assert captured() is None
        permanent_before_second_startup = gc.get_freeze_count()
        RegistryService.freeze_prepared_catalog_once()
        assert gc.get_freeze_count() == permanent_before_second_startup
        assert gc.isenabled()
    """)
    result = subprocess.run(
        [sys.executable, "-c", program], capture_output=True, text=True, timeout=60,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_startup_freeze_occurs_after_projections_and_releases_on_shutdown(monkeypatch):
    events = []

    class Catalog:
        def prepare_projections(self, *, status_callback, cancellation):
            events.append("projections")

    preparation = FunctionCatalogPreparation(Catalog())
    monkeypatch.setattr(
        preparation, "prepare_persistent_catalog",
        lambda **kwargs: events.append("declarations"),
    )
    monkeypatch.setattr(
        RegistryService, "freeze_prepared_catalog_once",
        lambda: events.append("freeze"),
    )
    monkeypatch.setattr(
        RegistryService, "release_prepared_catalog",
        lambda: events.append("release"),
    )
    preparation._prepare_current_process(
        status_callback=lambda message: None, cancellation=OperationCancellation(),
    )
    preparation.cancel_and_join()
    assert events == ["declarations", "projections", "freeze", "release"]


def test_failed_projection_does_not_freeze_the_startup_heap(monkeypatch):
    class Catalog:
        def prepare_projections(self, **kwargs):
            raise ValueError("projection failure")

    preparation = FunctionCatalogPreparation(Catalog())
    monkeypatch.setattr(preparation, "prepare_persistent_catalog", lambda **kwargs: None)
    monkeypatch.setattr(
        RegistryService, "freeze_prepared_catalog_once",
        lambda: pytest.fail("failed preparation froze its heap"),
    )
    with pytest.raises(ValueError, match="projection failure"):
        preparation._prepare_current_process(
            status_callback=lambda message: None, cancellation=OperationCancellation(),
        )


def test_cancelled_startup_does_not_freeze_completed_projections(monkeypatch):
    from concurrent.futures import CancelledError

    cancellation = OperationCancellation()

    class Catalog:
        def prepare_projections(self, **kwargs):
            cancellation.cancel()

    preparation = FunctionCatalogPreparation(Catalog())
    monkeypatch.setattr(preparation, "prepare_persistent_catalog", lambda **kwargs: None)
    monkeypatch.setattr(
        RegistryService, "freeze_prepared_catalog_once",
        lambda: pytest.fail("cancelled startup froze its heap"),
    )
    with pytest.raises(CancelledError):
        preparation._prepare_current_process(
            status_callback=lambda message: None, cancellation=cancellation,
        )
