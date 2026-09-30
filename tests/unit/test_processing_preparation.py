"""Preparation preserves declaration effects and independent cache lifetimes."""

import multiprocessing
import os
import signal
import subprocess
import sys
import textwrap
import time
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType

import psutil
import pytest

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import (
    prepare_processing_callable,
    reset_processing_callable_preparation_cache,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.processing_preparation import (
    CallablePreparation,
    PreparationCacheBatch,
    PreparationOperation,
)


@dataclass(frozen=True)
class AdditionalChildCachePreparation(PreparationOperation):
    name: str
    output_directory: Path

    @property
    def identity(self):
        return (type(self), self.name)

    def execute(self):
        (self.output_directory / self.name).write_text(str(os.getpid()))

    def can_prepare_in_child(self):
        return True


@pytest.fixture
def declared_module(monkeypatch):
    module = ModuleType("_openhcs_preparation_test")
    monkeypatch.setitem(sys.modules, module.__name__, module)
    reset_processing_callable_preparation_cache()
    yield module
    reset_processing_callable_preparation_cache()


def declare_process(module):
    def process(image):
        return image

    process.__module__ = module.__name__
    return process


def test_hooks_are_read_after_preceding_registry_and_module_effects(
    monkeypatch, declared_module
):
    events = []
    process = declare_process(declared_module)
    process.__dict__[FunctionContractAttribute.processing_prepare] = "invalid"

    def prepare_callable():
        events.append("callable")

    def prepare_module():
        events.append("module")
        process.__dict__[FunctionContractAttribute.processing_prepare] = (
            prepare_callable
        )

    def prepare_registries(modules):
        events.append(tuple(module.__name__ for module in modules))
        declared_module.__dict__[FunctionContractAttribute.processing_prepare] = (
            prepare_module
        )

    monkeypatch.setattr(
        AutoRegisterRegistryPreparation,
        "prepare_module_registered_families",
        prepare_registries,
    )
    prepare_processing_callable(process)
    prepare_processing_callable(process)
    assert events == [(declared_module.__name__,), "module", "callable"]


def test_invalid_callable_hook_fails_after_module_preparation(declared_module):
    events = []
    process = declare_process(declared_module)
    declared_module.__dict__[FunctionContractAttribute.processing_prepare] = (
        lambda: events.append("module")
    )
    process.__dict__[FunctionContractAttribute.processing_prepare] = 42
    with pytest.raises(TypeError, match="must be callable"):
        prepare_processing_callable(process)
    assert events == ["module"]


def test_failed_hook_remains_retryable_then_success_is_shared(declared_module):
    attempts = []
    process = declare_process(declared_module)

    def prepare():
        attempts.append(len(attempts))
        if len(attempts) == 1:
            raise RuntimeError("not ready")

    process.__dict__[FunctionContractAttribute.processing_prepare] = prepare
    with pytest.raises(RuntimeError, match="not ready"):
        CallablePreparation.from_callable(process).prepare()
    prepare_processing_callable(process)
    prepare_processing_callable(process)
    assert attempts == [0, 1]


def test_replaced_module_hook_keeps_its_distinct_identity(declared_module):
    events = []
    process = declare_process(declared_module)
    first = lambda: events.append("first")
    second = lambda: events.append("second")
    declared_module.__dict__[FunctionContractAttribute.processing_prepare] = first
    prepare_processing_callable(process)
    declared_module.__dict__[FunctionContractAttribute.processing_prepare] = second
    prepare_processing_callable(process)
    prepare_processing_callable(process)
    assert events == ["first", "second"]


def test_callable_without_module_runs_only_its_declared_hook(declared_module):
    events = []
    process = declare_process(declared_module)
    process.__module__ = None
    process.__dict__[FunctionContractAttribute.processing_prepare] = (
        lambda: events.append("callable")
    )
    prepare_processing_callable(process)
    prepare_processing_callable(process)
    assert events == ["callable"]
    assert PreparationCacheBatch.from_callables((process,)).preparations == ()


def test_cache_batch_deduplicates_modules_before_discovery(
    monkeypatch, declared_module
):
    calls = []
    process = declare_process(declared_module)

    def discover(module):
        calls.append(module.__name__)
        return ()

    monkeypatch.setattr(
        AutoRegisterRegistryPreparation,
        "module_registry_families",
        staticmethod(discover),
    )
    monkeypatch.setattr(
        "openhcs.core.processing_preparation.multiprocessing.get_all_start_methods",
        lambda: ["fork"],
    )
    PreparationCacheBatch.from_callables((process, process)).populate_child_caches()
    assert calls == [declared_module.__name__]


def test_new_operation_inherits_readiness_without_a_scheduler_roster(declared_module):
    events = []

    class AdditionalPreparation(PreparationOperation):
        @property
        def identity(self):
            return type(self)

        def execute(self):
            events.append("prepared")

    AdditionalPreparation().prepare()
    AdditionalPreparation().prepare()
    assert events == ["prepared"]
    assert not AdditionalPreparation().can_prepare_in_child()
    PreparationOperation.reset()
    AdditionalPreparation().prepare()
    assert events == ["prepared", "prepared"]


@pytest.mark.skipif(
    "fork" not in multiprocessing.get_all_start_methods(), reason="fork required"
)
def test_new_cache_operation_runs_in_children_and_still_prepares_parent(
    declared_module, tmp_path
):
    operations = tuple(
        AdditionalChildCachePreparation(name, tmp_path) for name in ("first", "second")
    )
    PreparationCacheBatch(operations).populate_child_caches()
    assert all(
        int((tmp_path / operation.name).read_text()) != os.getpid()
        for operation in operations
    )
    for operation in operations:
        operation.prepare()
    assert all(
        int((tmp_path / operation.name).read_text()) == os.getpid()
        for operation in operations
    )


def test_registry_preparation_derives_obligations_even_with_cached_metadata(
    monkeypatch, declared_module
):
    from types import SimpleNamespace

    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )

    process = declare_process(declared_module)
    events = []
    process.__dict__[FunctionContractAttribute.processing_prepare] = (
        lambda: events.append("hook")
    )
    metadata = {
        "first": SimpleNamespace(func=process),
        "alias": SimpleNamespace(func=process),
    }
    monkeypatch.setattr(RegistryService, "_metadata_cache", metadata)
    monkeypatch.setattr(
        PreparationCacheBatch,
        "populate_child_caches",
        lambda batch: events.append(
            tuple(item.module_name for item in batch.preparations)
        ),
    )

    assert RegistryService.prepare_in_current_process() is metadata
    assert RegistryService.prepare_in_current_process() is metadata
    assert events == [(declared_module.__name__,), "hook", (declared_module.__name__,)]


@pytest.mark.skipif(
    "fork" not in multiprocessing.get_all_start_methods(), reason="fork required"
)
def test_cancelling_registry_child_reaps_its_live_cache_workers(tmp_path):
    """SIGTERM must unwind the owned worker scope, without leaving descendants."""

    script = textwrap.dedent("""
        import os
        import sys
        import time
        from pathlib import Path
        from openhcs.core.processing_preparation import PreparationOperation, PreparationCacheBatch
        from openhcs.processing.backends.lib_registry.registry_service import RegistryService
        from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation

        directory = Path(sys.argv[1])
        class SlowPreparation(PreparationOperation):
            def __init__(self, name): self.name = name
            @property
            def identity(self): return self.name
            def can_prepare_in_child(self): return True
            def execute(self):
                (directory / self.name).write_text(str(os.getpid()))
                time.sleep(60)

        batch = PreparationCacheBatch(tuple(SlowPreparation(name) for name in ('first', 'second')))
        RegistryService.prepare_in_current_process = batch.populate_child_caches
        FunctionCatalogPreparation.prepare_persistent_catalog()
    """)
    process = subprocess.Popen(
        (sys.executable, "-c", script, str(tmp_path)),
        cwd=Path(__file__).parents[2],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        deadline = time.monotonic() + 15
        while not all((tmp_path / name).exists() for name in ("first", "second")):
            assert process.poll() is None, process.communicate()
            assert time.monotonic() < deadline, "cache workers did not start"
            time.sleep(0.02)
        worker_pids = tuple(
            int((tmp_path / name).read_text()) for name in ("first", "second")
        )
        process.send_signal(signal.SIGTERM)
        _, stderr = process.communicate(timeout=5)
        assert process.returncode != 0
        assert "CancelledError" in stderr
        assert all(not psutil.pid_exists(pid) for pid in worker_pids)
    finally:
        if process.poll() is None:
            process.kill()
            process.communicate(timeout=5)
