"""G7 guards: worker IPC and progress events are declared types, not dicts or tags."""

from __future__ import annotations

import ast
import re
from pathlib import Path

import openhcs
from openhcs.core.orchestrator import worker_execution
from openhcs.core.progress import ProgressEvent, ProgressExecutionContext, ProgressPhase
from openhcs.core.progress import ProgressStatus

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]
ORCHESTRATOR = REPO_ROOT / "openhcs/core/orchestrator"

DELETED_NAMES = frozenset(
    {
        "ProgressEventPayload",
        "create_event",
        "from_transport_fields",
        "to_transport_fields",
        "identity_for_event",
        "SubjectRuntimeStateDeclarationBase",
        "PlateRuntimeState",
        "WellFilterConfig",
        "WellFilterMode",
        "StepWellFilterConfig",
        "WellFilterProcessor",
        "well_filter",
        "well_filter_mode",
        "well_filter_config",
        "owned_wells",
        "execution_plate_id",
        "auto_add_output_plate_to_plate_manager",
    }
)


def _python_files(*roots: str) -> list[Path]:
    return [
        path
        for root in roots
        for path in (REPO_ROOT / root).rglob("*.py")
        if "benchmark/results" not in path.as_posix()
    ]


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
        elif isinstance(node, ast.alias):
            names.add(node.asname or node.name.rsplit(".", 1)[-1])
    return names


def test_replaced_runtime_names_do_not_exist() -> None:
    offenders = {
        path.relative_to(REPO_ROOT).as_posix(): sorted(
            DELETED_NAMES & _names(ast.parse(path.read_text()))
        )
        for path in _python_files("openhcs", "tests", "benchmark", "scripts")
        if path.name != Path(__file__).name
    }
    assert {path: names for path, names in offenders.items() if names} == {}


def test_worker_connections_carry_declared_messages() -> None:
    """Nothing sent between the orchestrator and a worker is a tuple, tag or None."""

    offenders = []
    for path in ORCHESTRATOR.rglob("*.py"):
        for node in ast.walk(ast.parse(path.read_text())):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "send"
                and node.args
                and isinstance(
                    node.args[0], (ast.Tuple, ast.Constant, ast.List, ast.Dict)
                )
            ):
                offenders.append(f"{path.name}:{node.lineno}")
            if (
                isinstance(node, ast.Compare)
                and any(
                    isinstance(operand, ast.Constant) and isinstance(operand.value, str)
                    for operand in (node.left, *node.comparators)
                )
                and re.search(r"kind|operation|command|message", ast.unparse(node))
            ):
                offenders.append(f"{path.name}:{node.lineno}")
    assert offenders == []


def test_every_worker_message_is_a_declared_family_member() -> None:
    commands = {
        cls.__name__
        for cls in vars(worker_execution).values()
        if isinstance(cls, type) and issubclass(cls, worker_execution.WorkerCommand)
    }
    replies = {
        cls.__name__
        for cls in vars(worker_execution).values()
        if isinstance(cls, type) and issubclass(cls, worker_execution.WorkerReply)
    }
    assert commands == {
        "WorkerCommand",
        "AnsweredWorkerCommand",
        "PrepareWorker",
        "ExecuteInheritedLane",
        "ExecuteShippedLane",
        "MapPartitions",
        "FinishExecution",
        "StopWorker",
    }
    assert replies == {"WorkerReply", "WorkerResult", "WorkerFailure", "WorkerProgress"}


def test_progress_event_codec_is_its_declaration() -> None:
    assert "to_dict" not in vars(ProgressEvent)
    assert "from_dict" not in vars(ProgressEvent)
    event = ProgressExecutionContext("execution-1", "/data/set").event(
        axis_id="A",
        step_name="step",
        phase=ProgressPhase.STEP_STARTED,
        status=ProgressStatus.STARTED,
        percent=0.0,
        completed=0,
        total=2,
        partition_values=["A", "B"],
        context={"note": "kept"},
    )
    wire = event.to_dict()
    assert wire["subject_id"] == "/data/set"
    assert wire["phase"] == "step_started"
    assert ProgressEvent.from_dict({**wire, "progress_sequence": 4}) == event


def test_progress_queues_receive_events_not_dicts() -> None:
    offenders = []
    for path in _python_files("openhcs"):
        for node in ast.walk(ast.parse(path.read_text())):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "put"
                and node.args
                and isinstance(node.args[0], ast.Call)
                and isinstance(node.args[0].func, ast.Attribute)
                and node.args[0].func.attr == "to_dict"
            ):
                offenders.append(f"{path.relative_to(REPO_ROOT)}:{node.lineno}")
    assert offenders == []
