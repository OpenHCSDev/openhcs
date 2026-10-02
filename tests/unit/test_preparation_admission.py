"""Demand and resource admission through the original preparation owners."""

from dataclasses import dataclass
from types import ModuleType, SimpleNamespace
import sys
import os

import pytest

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.function_patterns import (
    CompiledFunctionGroup, CompiledFunctionInvocation, CompiledFunctionPattern,
    FunctionInvocationKey,
)
from openhcs.core.processing_preparation import (
    PreparationCacheBatch, PreparationCacheWorker, PreparationOperation,
)
from openhcs.core.steps.function_runtime import prepare_compiled_context_callables
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


@pytest.fixture(autouse=True)
def isolated_completion():
    PreparationOperation.reset()
    yield
    PreparationOperation.reset()


@dataclass(frozen=True)
class DeclaredCache(PreparationOperation):
    name: str
    events: list

    @property
    def identity(self):
        return self.name

    def execute(self):
        self.events.append(("execute", self.name))

    def can_prepare_in_child(self):
        super().can_prepare_in_child()
        self.events.append(("admit", self.name))
        return True


class AdmissionAudit(PreparationOperation):
    def can_prepare_in_child(self):
        self.events.append(("before", self.name))
        result = super().can_prepare_in_child()
        self.events.append(("after", self.name))
        return result


class AuditBefore(AdmissionAudit, DeclaredCache):
    pass


class AuditAfter(DeclaredCache, AdmissionAudit):
    pass


def simulated_workers(monkeypatch, affinity):
    """Use actual scheduling/cleanup but no child or socket, under one CPU."""
    import openhcs.core.processing_preparation as owner
    monkeypatch.setattr(owner.multiprocessing, "get_all_start_methods", lambda: ["fork"])
    monkeypatch.setattr(os, "sched_getaffinity", lambda pid: set(range(affinity)))
    active, started, peak, closed = [], [], [], []

    class Worker:
        def __init__(self, operation):
            self.operation = operation
            self.result_connection = object()
            self.process = SimpleNamespace(pid=len(started) + 1)
            self.closed = False

        def wait(self):
            self.operation.execute()

        def close(self):
            if not self.closed:
                self.closed = True
                active.remove(self)
                closed.append(self.operation.name)

    def start(context, operation):
        worker = Worker(operation)
        active.append(worker)
        started.append(operation.name)
        peak.append(len(active))
        return worker

    monkeypatch.setattr(PreparationCacheWorker, "start", staticmethod(start))
    monkeypatch.setattr(owner, "wait", lambda connections: (connections[0],))
    return started, peak, closed


def test_default_budget_does_not_spawn_implicit_four_worker_pool(monkeypatch):
    events = []
    started, _, _ = simulated_workers(monkeypatch, 1)
    operations = tuple(DeclaredCache(str(index), events) for index in range(7))
    PreparationCacheBatch(operations).populate_child_caches()
    assert not started and not events


@pytest.mark.parametrize("affinity,budget,expected", [(1, 8, 0), (8, 1, 0), (2, 8, 2), (8, 2, 2), (8, 3, 3)])
@pytest.mark.parametrize("declaration", [AuditBefore, AuditAfter])
def test_new_cooperative_capability_obeys_affinity_budget_and_refills(
    monkeypatch, affinity, budget, expected, declaration,
):
    events = []
    started, peak, closed = simulated_workers(monkeypatch, affinity)
    operations = tuple(declaration(str(index), events) for index in range(7))
    PreparationCacheBatch(operations).populate_child_caches(max_workers=budget)
    if expected:
        assert max(peak) == expected
        assert started == closed == [operation.name for operation in operations]
        for operation in operations:
            hooks = [kind for kind, name in events if name == operation.name]
            expected_hooks = ["before", "admit", "after", "execute"]
            if declaration is AuditAfter:
                expected_hooks = ["before", "after", "admit", "execute"]
            assert hooks == expected_hooks
    else:
        assert not started and not events
    # Child cache success is not parent process-local readiness.
    assert not PreparationOperation._completed
    for operation in operations:
        operation.prepare()
        operation.prepare()
        assert events.count(("execute", operation.name)) == (2 if expected else 1)


@pytest.mark.parametrize("budget", [0, -1])
def test_invalid_budget_cannot_discover_or_launch(monkeypatch, budget):
    with pytest.raises(ValueError, match="positive"):
        PreparationCacheBatch(()).populate_child_caches(max_workers=budget)


@pytest.mark.parametrize("fails", [False, True])
def test_startup_prepares_entire_catalog_and_dynamic_compilation_remains_guarded(
    monkeypatch, fails,
):
    events = []
    module = ModuleType("_admitted_preparation_source")
    monkeypatch.setitem(sys.modules, module.__name__, module)

    def selected(image):
        return image

    def unselected(image):
        return image

    def dynamic(image):
        return image

    for function in (selected, unselected, dynamic):
        function.__module__ = module.__name__

    def prepare_selected():
        events.append("selected")
        if fails:
            raise RuntimeError("selected preparation failed")
    selected.__dict__[FunctionContractAttribute.processing_prepare] = prepare_selected
    unselected.__dict__[FunctionContractAttribute.processing_prepare] = lambda: events.append("unselected")
    dynamic.__dict__[FunctionContractAttribute.processing_prepare] = lambda: events.append("dynamic")
    metadata = {"selected": SimpleNamespace(func=selected), "unselected": SimpleNamespace(func=unselected)}
    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    monkeypatch.setattr(RegistryService, "_available_registry_instances", classmethod(lambda cls: ()))
    monkeypatch.setattr(RegistryService, "_metadata_from_instances", classmethod(lambda cls, instances: metadata))
    monkeypatch.setattr(AutoRegisterRegistryPreparation, "module_registry_families", staticmethod(lambda module: ()))
    monkeypatch.setattr(PreparationCacheBatch, "populate_child_caches", lambda self, **kwargs: None)
    if fails:
        for _ in range(2):
            with pytest.raises(RuntimeError, match="selected preparation failed"):
                RegistryService.prepare_in_current_process()
        assert events == ["selected", "selected"]
        events.clear()
        fails = False
    assert RegistryService.prepare_in_current_process() is metadata
    assert RegistryService.prepare_in_current_process() is metadata
    assert events == ["selected", "unselected"]

    invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("selected", "default", 0),
        contract=CallableContract.from_callable(selected),
    )
    dynamic_invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("dynamic", "default", 1),
        contract=CallableContract.from_callable(dynamic),
    )
    group = CompiledFunctionGroup("default", (invocation, dynamic_invocation))
    pattern = CompiledFunctionPattern(groups=(group,), is_grouped=False)
    context = SimpleNamespace(step_plans={0: SimpleNamespace(step_index=0, compiled_function_pattern=pattern)})
    prepare_compiled_context_callables({"A01": context}, max_workers=1)
    prepare_compiled_context_callables({"A01": context}, max_workers=1)
    assert events == ["selected", "unselected", "dynamic"]


def test_unavailable_affinity_does_not_admit_speculative_parallelism(monkeypatch):
    events = []
    started, _, _ = simulated_workers(monkeypatch, 8)
    monkeypatch.delattr(os, "sched_getaffinity")
    PreparationCacheBatch(tuple(DeclaredCache(str(i), events) for i in range(3))).populate_child_caches(max_workers=8)
    assert not started and not events


def test_affinity_query_failure_is_not_misreported_as_success(monkeypatch):
    events = []
    started, _, _ = simulated_workers(monkeypatch, 8)
    def fail(pid):
        raise OSError("affinity admission failed")
    monkeypatch.setattr(os, "sched_getaffinity", fail)
    with pytest.raises(OSError, match="affinity admission failed"):
        PreparationCacheBatch(tuple(DeclaredCache(str(i), events) for i in range(3))).populate_child_caches(max_workers=8)
    assert not started and not events


def test_failure_in_refilled_slot_closes_every_exact_worker(monkeypatch):
    events = []
    started, peak, closed = simulated_workers(monkeypatch, 2)
    class FailingCache(DeclaredCache):
        def execute(self):
            super().execute()
            raise RuntimeError("refilled cache failed")
    operations = (*tuple(DeclaredCache(str(i), events) for i in range(4)), FailingCache("failed", events), DeclaredCache("not-started", events))
    with pytest.raises(RuntimeError, match="refilled cache failed"):
        PreparationCacheBatch(operations).populate_child_caches(max_workers=8)
    assert max(peak) == 2
    assert set(closed) == set(started)
    assert not PreparationOperation._completed


def test_selected_hook_failure_is_not_admitted_as_completed(monkeypatch):
    events = []
    def hook():
        events.append("attempt")
        raise RuntimeError("selected preparation failed")
    from openhcs.core.processing_preparation import CallableHookPreparation
    operation = CallableHookPreparation(hook, None, "new_selected")
    for _ in range(2):
        with pytest.raises(RuntimeError, match="selected preparation failed"):
            operation.prepare()
    assert events == ["attempt", "attempt"]
    assert operation.identity not in PreparationOperation._completed
