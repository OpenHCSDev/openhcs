"""Declared kernel work shares readiness without inspecting arbitrary hooks."""

import multiprocessing
import os
import sys
from types import ModuleType

import pytest
from metaclass_registry import AutoRegisterMeta
from numba import config as numba_config

from openhcs.core.callable_contract import prepare_processing_callable
from openhcs.core.processing_preparation import (
    PreparationCacheBatch,
    PreparationOperation,
)
from openhcs.processing.backends.cellprofiler._preparation import (
    CellProfilerCallableKernelPreparation,
)


@pytest.fixture
def kernel_module(monkeypatch):
    module = ModuleType("_openhcs_declared_kernel_test")
    monkeypatch.setitem(sys.modules, module.__name__, module)
    PreparationOperation.reset()
    yield module
    PreparationOperation.reset()


def declare_callable(module, hook):
    def process(image):
        return image

    process.__module__ = module.__name__
    process.__openhcs_prepare__ = hook
    return process


def test_real_declarations_own_independent_registry_obligations():
    from openhcs.processing.backends.cellprofiler.grid import (
        IdentifyObjectsInGridKernelPreparation,
    )
    from openhcs.processing.backends.cellprofiler.morphology import (
        ExpandOrShrinkObjectsKernelPreparation,
    )
    from openhcs.processing.backends.cellprofiler.primary_objects import (
        IdentifyPrimaryObjectsKernelPreparation,
    )
    from openhcs.processing.backends.cellprofiler.shape import (
        ObjectSizeShapeKernelPreparation,
    )

    declarations = (
        IdentifyObjectsInGridKernelPreparation,
        ExpandOrShrinkObjectsKernelPreparation,
        IdentifyPrimaryObjectsKernelPreparation,
        ObjectSizeShapeKernelPreparation,
    )
    assert "__registry__" not in vars(CellProfilerCallableKernelPreparation)
    assert len({id(declaration.__registry__) for declaration in declarations}) == 4
    for declaration in declarations:
        assert declaration in declaration.__registry__.values()
        assert declaration().identity == declaration().identity


def test_declared_cache_admission_requires_cpu_and_empty_explicit_cache(
    monkeypatch, tmp_path
):
    from openhcs.processing.backends.cellprofiler.grid import (
        IdentifyObjectsInGridKernelPreparation,
    )

    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    monkeypatch.setattr(numba_config, "CACHE_DIR", str(tmp_path))
    assert IdentifyObjectsInGridKernelPreparation.can_prepare_in_child()
    index = tmp_path / "nested" / "compiled.nbi"
    index.parent.mkdir()
    index.touch()
    assert not IdentifyObjectsInGridKernelPreparation.can_prepare_in_child()
    index.unlink()
    monkeypatch.setattr(numba_config, "CACHE_DIR", "")
    assert not IdentifyObjectsInGridKernelPreparation.can_prepare_in_child()
    monkeypatch.setattr(numba_config, "CACHE_DIR", str(tmp_path))
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "false")
    assert not IdentifyObjectsInGridKernelPreparation.can_prepare_in_child()


def test_non_cpu_backend_admission_does_not_discover_lazy_providers(monkeypatch):
    from openhcs.processing.backends.cellprofiler._backend import (
        CellProfilerBackendStrategyMixin,
    )

    class UndiscoveredProviders(dict):
        def values(self):
            raise AssertionError("CPU admission must precede lazy discovery")

    class UndiscoveredBackend(CellProfilerBackendStrategyMixin):
        __registry__ = UndiscoveredProviders()

    monkeypatch.setenv("OPENHCS_CPU_ONLY", "false")
    assert not UndiscoveredBackend.can_prepare_in_child()


@pytest.mark.skipif(
    "fork" not in multiprocessing.get_all_start_methods(), reason="fork required"
)
def test_new_declarations_populate_children_then_share_parent_hook_readiness(
    monkeypatch, kernel_module, tmp_path
):
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    monkeypatch.setattr(numba_config, "CACHE_DIR", str(tmp_path / "cache"))

    class FirstKernel(
        CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta
    ):
        __registry__ = {}

        def execute(self):
            with (tmp_path / "first").open("a") as stream:
                stream.write(f"{os.getpid()}\n")

    class SecondKernel(
        CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta
    ):
        __registry__ = {}

        def execute(self):
            with (tmp_path / "second").open("a") as stream:
                stream.write(f"{os.getpid()}\n")

    kernel_module.FirstKernel = FirstKernel
    kernel_module.SecondKernel = SecondKernel
    process = declare_callable(kernel_module, FirstKernel().prepare)
    batch = PreparationCacheBatch.from_callables((process, process))
    batch.populate_child_caches()
    assert not PreparationOperation._completed
    for name in ("first", "second"):
        pids = (tmp_path / name).read_text().splitlines()
        assert len(pids) == 1 and int(pids[0]) != os.getpid()

    prepare_processing_callable(process)
    prepare_processing_callable(process)
    FirstKernel().prepare()
    for name in ("first", "second"):
        pids = (tmp_path / name).read_text().splitlines()
        assert len(pids) == 2 and int(pids[1]) == os.getpid()


def test_failure_keeps_kernel_and_enclosing_module_retryable(kernel_module):
    attempts = []

    class RetryKernel(
        CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta
    ):
        __registry__ = {}

        def execute(self):
            attempts.append(len(attempts))
            if len(attempts) == 1:
                raise RuntimeError("kernel not ready")

    kernel_module.RetryKernel = RetryKernel
    process = declare_callable(kernel_module, RetryKernel().prepare)
    with pytest.raises(RuntimeError, match="kernel not ready"):
        prepare_processing_callable(process)
    assert not PreparationOperation._completed
    prepare_processing_callable(process)
    prepare_processing_callable(process)
    RetryKernel().prepare()
    assert attempts == [0, 1]
