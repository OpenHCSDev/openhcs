"""Cold-cache preparation keeps parent ownership and explicit failure semantics."""

import multiprocessing
import os
from pathlib import Path
from types import SimpleNamespace
from typing import ClassVar

import pytest
from metaclass_registry import AutoRegisterMeta
from numba import config as numba_config

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import (
    CallableContract,
    CompilerPreparedAutoRegisterFamily,
    reset_processing_callable_preparation_cache,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
    FunctionInvocationKey,
)
from openhcs.core.steps.function_runtime import prepare_compiled_context_callables
from openhcs.processing.backends.cellprofiler._backend import (
    CellProfilerBackendStrategyMixin,
)
from openhcs.processing.backends.cellprofiler.intensity import (
    ObjectIntensityBackendStrategy,
)


class _FirstCacheFamily(CompilerPreparedAutoRegisterFamily, metaclass=AutoRegisterMeta):
    __registry_key__ = "registry_key"
    __skip_if_no_key__ = True
    registry_key = None
    output_directory: Path
    fail = False

    @classmethod
    def can_prepare_in_child(cls):
        return True

    @classmethod
    def prepare_registered_family(cls):
        if cls.fail:
            raise RuntimeError("preparation failed")
        (cls.output_directory / cls.__name__).write_text(str(os.getpid()))


class _SecondCacheFamily(_FirstCacheFamily):
    # A distinct registry is needed: sharing a registry must not submit twice.
    __registry__: ClassVar[dict] = {}


@pytest.mark.skipif(
    "fork" not in multiprocessing.get_all_start_methods(), reason="fork required"
)
def test_child_preparation_deduplicates_registries_and_propagates_failure(
    monkeypatch, tmp_path
):
    monkeypatch.setattr(_FirstCacheFamily, "output_directory", tmp_path, raising=False)
    monkeypatch.setattr(_SecondCacheFamily, "output_directory", tmp_path, raising=False)
    monkeypatch.setattr(
        AutoRegisterRegistryPreparation,
        "module_registry_families",
        staticmethod(
            lambda module: (_FirstCacheFamily, _FirstCacheFamily, _SecondCacheFamily)
        ),
    )
    import sys

    AutoRegisterRegistryPreparation.prepare_module_caches_in_children(
        (sys.modules[__name__],)
    )
    assert {path.name for path in tmp_path.iterdir()} == {
        "_FirstCacheFamily",
        "_SecondCacheFamily",
    }
    assert all(int(path.read_text()) != os.getpid() for path in tmp_path.iterdir())

    monkeypatch.setattr(_SecondCacheFamily, "fail", True)
    with pytest.raises(RuntimeError, match="preparation failed"):
        AutoRegisterRegistryPreparation.prepare_module_caches_in_children(
            (sys.modules[__name__],)
        )


def test_backend_child_preparation_requires_empty_explicit_cpu_cache(
    monkeypatch, tmp_path
):
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    monkeypatch.setattr(numba_config, "CACHE_DIR", str(tmp_path))
    assert ObjectIntensityBackendStrategy.can_prepare_in_child()
    assert not CellProfilerBackendStrategyMixin.can_prepare_in_child()

    index = tmp_path / "nested" / "compiled.nbi"
    index.parent.mkdir()
    index.touch()
    assert not ObjectIntensityBackendStrategy.can_prepare_in_child()
    index.unlink()
    monkeypatch.setattr(numba_config, "CACHE_DIR", "")
    assert not ObjectIntensityBackendStrategy.can_prepare_in_child()
    monkeypatch.setattr(numba_config, "CACHE_DIR", str(tmp_path))
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "false")
    assert not ObjectIntensityBackendStrategy.can_prepare_in_child()


def test_platform_without_fork_keeps_parent_preparation_path(monkeypatch):
    monkeypatch.setattr(multiprocessing, "get_all_start_methods", lambda: ["spawn"])

    def modules():
        raise AssertionError(
            "unsupported child preparation must not discover registries"
        )
        yield

    AutoRegisterRegistryPreparation.prepare_module_caches_in_children(modules())


def test_compiled_context_preparation_runs_parent_hook_after_children(
    monkeypatch, tmp_path
):
    events = []
    monkeypatch.setattr(_FirstCacheFamily, "output_directory", tmp_path, raising=False)
    monkeypatch.setattr(_SecondCacheFamily, "output_directory", tmp_path, raising=False)
    monkeypatch.setattr(
        AutoRegisterRegistryPreparation,
        "module_registry_families",
        staticmethod(lambda module: (_FirstCacheFamily, _SecondCacheFamily)),
    )

    def process(image):
        return image

    process.__dict__[FunctionContractAttribute.processing_prepare] = (
        lambda: events.append("parent")
    )
    invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("process", "default", 0),
        contract=CallableContract.from_callable(process),
    )
    pattern = CompiledFunctionPattern(
        groups=(CompiledFunctionGroup("default", (invocation,)),), is_grouped=False
    )
    context = SimpleNamespace(
        step_plans={0: SimpleNamespace(step_index=0, compiled_function_pattern=pattern)}
    )

    def prepare_children(modules):
        events.append(tuple(module.__name__ for module in modules))

    monkeypatch.setattr(
        AutoRegisterRegistryPreparation,
        "prepare_module_caches_in_children",
        prepare_children,
    )
    reset_processing_callable_preparation_cache()
    prepare_compiled_context_callables({"A01": context})
    assert events == [(__name__,), "parent"]
    assert all(int(path.read_text()) == os.getpid() for path in tmp_path.iterdir())
