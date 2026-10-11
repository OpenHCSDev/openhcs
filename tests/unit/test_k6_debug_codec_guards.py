"""K6 guards: one value-to-JSON encoder, and the progress and filter kinds are families."""

from __future__ import annotations

import ast
from dataclasses import make_dataclass
from enum import Enum
from pathlib import Path

import pytest
from python_introspect import dataclass_from_mapping, to_jsonable

from openhcs.core import config, debug, debug_view_models
from openhcs.core.progress import ProgressEvent, types as progress_types

REPO = Path(__file__).resolve().parents[2]
OPENHCS = REPO / "openhcs"
DEBUG_AND_PROGRESS = (
    OPENHCS / "core" / "debug.py",
    OPENHCS / "core" / "debug_views.py",
    OPENHCS / "core" / "debug_view_models.py",
    *sorted((OPENHCS / "core" / "progress").glob("*.py")),
)
HAND_CODEC_METHODS = {
    "to_json_dict",
    "from_json_dict",
    "to_dict",
    "from_dict",
    "context_body",
    "from_context_body",
}


def _functions(path: Path):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    return [
        node
        for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]


def _is_value_to_json_switch(function: ast.FunctionDef) -> bool:
    """A function that calls itself and branches on Enum or dataclass values."""

    calls_itself = any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == function.name
        for node in ast.walk(function)
    )
    checked: set[str] = set()
    for node in ast.walk(function):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
            continue
        if node.func.id in {"is_dataclass", "asdict", "fields"}:
            checked.add("dataclass")
        if node.func.id == "isinstance" and len(node.args) == 2:
            kinds = node.args[1]
            for kind in kinds.elts if isinstance(kinds, ast.Tuple) else [kinds]:
                if isinstance(kind, (ast.Name, ast.Attribute)):
                    checked.add(kind.id if isinstance(kind, ast.Name) else kind.attr)
    return calls_itself and bool(checked & {"Enum", "dataclass"})


def test_only_python_introspect_encodes_values_to_json():
    switches = [
        f"{path.relative_to(REPO)}:{function.lineno} {function.name}"
        for path in sorted(OPENHCS.rglob("*.py"))
        for function in _functions(path)
        if _is_value_to_json_switch(function)
        and any(word in function.name for word in ("json", "cell_text"))
    ]
    assert switches == []


def test_debug_and_progress_modules_write_no_value_switch_or_hand_codec():
    control_codecs = [
        node.name
        for node in ast.walk(ast.parse(DEBUG_AND_PROGRESS[0].read_text(encoding="utf-8")))
        if isinstance(node, ast.ClassDef)
        and any(
            isinstance(item, ast.FunctionDef) and item.name.endswith("control_response")
            for item in node.body
        )
    ]
    assert control_codecs == ["DebugControlResponse"]
    offenders = [
        f"{path.relative_to(REPO)}:{function.lineno} {function.name}"
        for path in DEBUG_AND_PROGRESS
        for function in _functions(path)
        if _is_value_to_json_switch(function) or function.name in HAND_CODEC_METHODS
    ]
    assert offenders == []


def test_progress_and_filter_kinds_are_families_not_enums():
    for family in (
        progress_types.ProgressPhase,
        progress_types.ProgressStatus,
        progress_types.ProgressStream,
        config.PartitionFilterMode,
    ):
        assert not issubclass(family, Enum), family
        assert family.__registry__, family
    for removed in ("ProgressChannelRole", "DeclaredProgressContextPayload"):
        assert not hasattr(progress_types, removed)
    for removed in (
        "DebugEventType",
        "DebugBoundaryOutcome",
        "DebugTimelineNodeState",
        "DebugPausedWorkerState",
        "DebugControlMessageType",
        "DebugSnapshotReadControlPayload",
        "DebugWorkerCommandControlPayload",
        "DebugArtifactExportControlPayload",
        "DebugRuntimeInspectionControlPayload",
    ):
        assert not hasattr(debug, removed), removed
    for removed in ("DebugViewSectionKind", "DebugViewTableProjection", "debug_view_jsonable"):
        assert not hasattr(debug_view_models, removed), removed


def test_no_enum_is_declared_in_debug_or_progress_modules():
    declared = {
        (path.name, node.name)
        for path in DEBUG_AND_PROGRESS
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8")))
        if isinstance(node, ast.ClassDef)
        and any(
            (isinstance(base, ast.Name) and base.id == "Enum")
            or (isinstance(base, ast.Attribute) and base.attr == "Enum")
            for base in node.bases
        )
    }
    assert declared == set()


@pytest.mark.parametrize(
    "family",
    [
        progress_types.ProgressPhase,
        progress_types.ProgressStatus,
        config.PartitionFilterMode,
        debug.DebugBoundary,
        debug.DebugWorkerState,
        debug.DebugReplayMode,
        debug.DebugCommandType,
    ],
)
def test_every_family_member_round_trips_through_its_wire_spelling(family):
    holder = make_dataclass("Holder", [("value", type[family])], frozen=True)
    members = tuple(family.__registry__.values())
    assert members
    for member in members:
        assert to_jsonable(member) == member.name
        assert dataclass_from_mapping(holder, {"value": member.name}).value is member


def test_every_phase_and_status_round_trips_through_a_progress_event():
    for phase in progress_types.ProgressPhase.__registry__.values():
        for status in progress_types.ProgressStatus.__registry__.values():
            event = ProgressEvent(
                execution_id="e",
                subject_id="s",
                axis_id="a",
                step_name="step",
                phase=phase,
                status=status,
                percent=0.0,
                timestamp=1.0,
                completed=0,
                total=1,
                pid=1,
            )
            restored = ProgressEvent.from_dict(event.to_dict())
            assert restored == event
            assert restored.stream is phase.stream
