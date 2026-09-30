"""Declared kernel work shares readiness without inspecting arbitrary hooks."""

import multiprocessing
import os
import signal
import subprocess
import sys
import textwrap
from types import ModuleType

import psutil
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


def test_fixture_capture_keeps_callable_preparation_in_parent(monkeypatch, tmp_path):
    from openhcs.processing.backends.cellprofiler.grid import (
        IdentifyObjectsInGridKernelPreparation,
    )

    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    monkeypatch.setattr(numba_config, "CACHE_DIR", str(tmp_path / "cache"))
    monkeypatch.setenv("OPENHCS_CAPTURE_CELLPROFILER_FIXTURES_DIR", str(tmp_path))
    assert not IdentifyObjectsInGridKernelPreparation.can_prepare_in_child()


def test_capture_preparation_retains_registry_module_callable_effect_order(
    monkeypatch, kernel_module, tmp_path
):
    events = []

    class CapturedKernel(
        CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta
    ):
        __registry__ = {}

        def execute(self):
            events.append("kernel")

    kernel_module.CapturedKernel = CapturedKernel
    process = declare_callable(kernel_module, CapturedKernel().execute)
    kernel_module.__openhcs_prepare__ = lambda: events.append("module")
    monkeypatch.setenv("OPENHCS_CAPTURE_CELLPROFILER_FIXTURES_DIR", str(tmp_path))
    prepare_processing_callable(process)
    prepare_processing_callable(process)
    assert events == ["module", "kernel"]


def test_late_module_capture_effect_reaches_real_shape_callable_hook(
    monkeypatch, kernel_module, tmp_path
):
    from openhcs.processing.backends.cellprofiler.shape import (
        ObjectSizeShapeKernelPreparation,
        measure_object_size_shape,
    )

    monkeypatch.delenv("OPENHCS_CAPTURE_CELLPROFILER_FIXTURES_DIR", raising=False)
    kernel_module.ObjectSizeShapeKernelPreparation = ObjectSizeShapeKernelPreparation
    process = declare_callable(
        kernel_module, measure_object_size_shape.__openhcs_prepare__
    )

    def enable_capture():
        monkeypatch.setenv("OPENHCS_CAPTURE_CELLPROFILER_FIXTURES_DIR", str(tmp_path))

    kernel_module.__openhcs_prepare__ = enable_capture
    prepare_processing_callable(process)
    captured = set(tmp_path.glob("*.npz"))
    assert captured
    prepare_processing_callable(process)
    assert set(tmp_path.glob("*.npz")) == captured


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


@pytest.mark.skipif(
    "fork" not in multiprocessing.get_all_start_methods(), reason="fork required"
)
def test_cache_children_do_not_acquire_inherited_parent_readiness_lock(tmp_path):
    script = textwrap.dedent("""
        import os, signal, sys
        from pathlib import Path
        from types import ModuleType
        from openhcs.core.processing_preparation import (
            ModuleRegistryPreparation, PreparationCacheBatch,
            PreparationCacheWorker, PreparationOperation,
        )
        from openhcs.processing.backends.cellprofiler._preparation import (
            CellProfilerCallableKernelPreparation,
        )
        from metaclass_registry import AutoRegisterMeta
        from numba import config
        output = Path(sys.argv[1])
        config.CACHE_DIR = str(output / 'cache')
        def cancelled(signum, frame): raise SystemExit(128 + signum)
        signal.signal(signal.SIGTERM, cancelled)
        original_start = PreparationCacheWorker.start
        def record_start(cls, context, operation):
            worker = original_start(context, operation)
            with (output / 'owned_pids').open('a') as stream:
                stream.write(f'{worker.process.pid}\\n')
            return worker
        PreparationCacheWorker.start = classmethod(record_start)
        class First(CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta):
            __registry__ = {}
            def execute(self): (output / 'first').write_text(str(os.getpid()))
        class Second(CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta):
            __registry__ = {}
            def execute(self): (output / 'second').write_text(str(os.getpid()))
        module = ModuleType('_openhcs_inherited_lock_control')
        module.First, module.Second = First, Second
        sys.modules[module.__name__] = module
        PreparationOperation.reset()
        PreparationOperation._lock.acquire()
        try:
            PreparationCacheBatch((ModuleRegistryPreparation(module.__name__),)).populate_child_caches()
            assert not PreparationOperation._completed
        finally:
            PreparationOperation._lock.release()
        (output / 'completed').write_text('cache work finished while parent lock held')
    """)
    environment = os.environ.copy()
    environment["OPENHCS_CPU_ONLY"] = "true"
    process = subprocess.Popen(
        (sys.executable, "-c", script, str(tmp_path)),
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=5)
    except subprocess.TimeoutExpired:
        timed_out = True
        process.send_signal(signal.SIGTERM)
        stdout, stderr = process.communicate(timeout=5)
    finally:
        if process.poll() is None:
            process.kill()
            process.communicate(timeout=5)
    assert (tmp_path / "owned_pids").is_file(), stdout + stderr
    owned = [int(pid) for pid in (tmp_path / "owned_pids").read_text().splitlines()]
    assert len(owned) == 2
    assert all(not psutil.pid_exists(pid) for pid in owned)
    assert not timed_out, "cache children waited on the inherited lock"
    assert process.returncode == 0, stdout + stderr
    assert (tmp_path / "completed").is_file()
    assert all(
        int((tmp_path / name).read_text()) in owned for name in ("first", "second")
    )
