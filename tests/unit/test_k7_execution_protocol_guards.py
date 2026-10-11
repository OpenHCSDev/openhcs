"""K7 guards: scope variants, context phases and execution results are types."""

from __future__ import annotations

import ast
import dataclasses
import inspect
import pickle
import sys
from pathlib import Path

import pytest

import openhcs
from openhcs.core.artifacts.plans import ArtifactPlan
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    DynamicGroupScope,
    SingleKeyScope,
    StaticGroupScope,
    UngroupedScope,
)
import openhcs.core.context.processing_context as processing_context
from openhcs.core.context.processing_context import (
    CompiledContext,
    CompilingContext,
    ExecutingContext,
    ProcessingContext,
)
from openhcs.core.orchestrator import execution_result
from openhcs.core.orchestrator.execution_result import (
    ExecutionCancelled,
    ExecutionFailed,
    ExecutionResult,
    ExecutionSucceeded,
    MergeAllRuntimeRecords,
    MergeDatasetInputRecords,
    OmitRuntimeRecords,
    RuntimeObservationMode,
)
from openhcs.domains.microscopy.axes import Microscopy

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]

# Names whose only meaning was a None/flag variant re-decided by the caller.
DELETED_NAMES = frozenset(
    {
        "is_ungrouped",
        "has_single_static_key",
        "require_single_static_key",
        "PathPlannerGroupScope",
        "producer_group_scope",
        "has_dynamic_group_scope",
        "single_group_key",
        "is_frozen",
        "_is_frozen",
        "bind_execution_runtime",
        "reset_completed_step_outputs",
        "ZMQExecutionAxisOutcome",
        "is_cancelled",
    }
)


def _concrete_subclasses(base: type) -> set[type]:
    """Instantiable members of a family, as their modules publish them."""
    found: set[type] = set()
    pending = list(base.__subclasses__())
    while pending:
        cls = pending.pop()
        pending.extend(cls.__subclasses__())
        module = sys.modules.get(cls.__module__)
        if (
            cls.__module__.startswith("openhcs.")
            and getattr(module, cls.__name__, None) is cls
            and not inspect.isabstract(cls)
        ):
            found.add(cls)
    return found


def _names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            names.add(node.id)
        elif isinstance(node, ast.Attribute):
            names.add(node.attr)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.arg):
            names.add(node.arg)
        elif isinstance(node, ast.keyword) and node.arg:
            names.add(node.arg)
    return names


def test_replaced_execution_protocol_names_do_not_exist() -> None:
    offenders = {
        path.relative_to(REPO_ROOT).as_posix(): sorted(
            DELETED_NAMES & _names(ast.parse(path.read_text()))
        )
        for path in (REPO_ROOT / "openhcs").rglob("*.py")
    }
    assert {path: names for path, names in offenders.items() if names} == {}


def test_scope_variants_are_the_declared_family() -> None:
    assert _concrete_subclasses(ComponentGroupScope) == {
        UngroupedScope,
        DynamicGroupScope,
        StaticGroupScope,
        SingleKeyScope,
    }
    assert not hasattr(ComponentGroupScope, "from_raw")


def test_artifact_plans_hold_one_group_scope() -> None:
    names = {field.name for field in dataclasses.fields(ArtifactPlan)}
    assert "group_scope" in names
    assert not names & {"group_keys", "group_component"}


def test_context_phases_and_results_are_the_declared_families() -> None:
    assert _concrete_subclasses(ProcessingContext) == {
        CompilingContext,
        CompiledContext,
        ExecutingContext,
    }
    # ExecutionStopped is the shared base of the two stopped outcomes.
    assert _concrete_subclasses(ExecutionResult) - {
        execution_result.ExecutionStopped
    } == {
        ExecutionSucceeded,
        ExecutionFailed,
        ExecutionCancelled,
    }
    assert set(RuntimeObservationMode.__subclasses__()) == {
        OmitRuntimeRecords,
        MergeAllRuntimeRecords,
        MergeDatasetInputRecords,
    }
    assert not hasattr(execution_result, "ExecutionStatus")
    assert not hasattr(processing_context, "_is_frozen")


@pytest.mark.parametrize(
    ("scope", "keys", "contained", "outside"),
    [
        (UngroupedScope(), (None,), None, "1"),
        (DynamicGroupScope(Microscopy.Channel), (None,), "7", None),
        (StaticGroupScope(Microscopy.Channel, ("1", "2")), ("1", "2"), "2", "3"),
        (SingleKeyScope(Microscopy.Channel, "1"), ("1",), "1", "2"),
    ],
)
def test_each_scope_variant_reads_back_from_its_raw_spelling(
    scope, keys, contained, outside
) -> None:
    assert ComponentGroupScope.of(keys, component=scope.component) == scope
    assert scope.contains_runtime_key(contained)
    assert not scope.contains_runtime_key(outside)
    assert pickle.loads(pickle.dumps(scope)) == scope


def test_context_phases_carry_only_their_own_state(tmp_path) -> None:
    compiling = CompilingContext(axis_id="A01", filemanager=object())
    assert not hasattr(compiling, "runtime_value_store")
    compiled = compiling.freeze()
    assert not hasattr(compiled, "runtime_value_store")
    with pytest.raises(AttributeError):
        compiled.axis_id = "B01"
    first = compiled.executing()
    second = compiled.executing()
    assert first.runtime_value_store is not second.runtime_value_store
    assert first.axis_id == compiled.axis_id
    with pytest.raises(AttributeError):
        first.step_plans = {}
    restored = pickle.loads(pickle.dumps(compiled))
    assert restored.axis_id == "A01"
    with pytest.raises(AttributeError):
        restored.axis_id = "B01"


def test_stopped_results_own_their_message_and_combination() -> None:
    failed = ExecutionFailed("A01", error_message="boom").at_combination(
        "A01__combo_0", execution_result.RuntimeExecutionObservation()
    )
    assert not failed.is_success()
    assert failed.failed_combination == "A01__combo_0"
    assert ExecutionSucceeded("A01").is_success()
    assert ExecutionCancelled("A01", error_message="stop").stops_lane
    assert not {"error_message", "failed_combination"} & {
        field.name for field in dataclasses.fields(ExecutionSucceeded)
    }
