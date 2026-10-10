"""U1 guards: session state lives in the session, and clients only render it."""

from __future__ import annotations

import ast
import subprocess
import sys
from pathlib import Path

import openhcs
from openhcs.authoring.session.operations import (
    HeadlessOperation,
    RendererOperation,
    SessionOperation,
)

PACKAGE = Path(openhcs.__file__).parent
SESSION_PACKAGE = PACKAGE / "authoring" / "session"

SESSION_STATE_ATTRIBUTES = frozenset(
    {
        "plate_configs",
        "plate_compiled_data",
        "plate_init_pending",
        "plate_compile_pending",
        "plate_terminal_activity_status",
        "_active_debug_sessions",
        "_debug_snapshots_by_plate",
        "_debug_terminal_summaries_by_plate",
        "pipeline_steps",
        "current_plate",
        "selected_plate_path",
        "_execution_state",
        "execution_state",
        "debug_session_state",
        "debug_terminal_summary",
        "runtime_progress_projection",
        "debug_runtime_projection",
        "live_measurement_model",
        "global_config",
    }
)


def _modules(root: Path):
    for path in sorted(root.rglob("*.py")):
        yield path, ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def test_no_widget_holds_session_state() -> None:
    """No class under the GUI package assigns a session-state attribute to itself."""

    offenders = []
    for path, tree in _modules(PACKAGE / "pyqt_gui"):
        for node in ast.walk(tree):
            targets = (
                node.targets
                if isinstance(node, ast.Assign)
                else [node.target]
                if isinstance(node, (ast.AnnAssign, ast.AugAssign))
                else []
            )
            for target in targets:
                if (
                    isinstance(target, ast.Attribute)
                    and isinstance(target.value, ast.Name)
                    and target.value.id == "self"
                    and target.attr in SESSION_STATE_ATTRIBUTES
                ):
                    offenders.append(f"{path.relative_to(PACKAGE)}:{node.lineno} self.{target.attr}")
    assert offenders == []


def test_session_package_imports_no_qt_and_no_gui() -> None:
    offenders = []
    for path, tree in _modules(SESSION_PACKAGE):
        for node in ast.walk(tree):
            names = (
                [alias.name for alias in node.names]
                if isinstance(node, ast.Import)
                else [node.module or ""]
                if isinstance(node, ast.ImportFrom)
                else []
            )
            for name in names:
                if name.split(".")[0] == "PyQt6" or name.startswith("openhcs.pyqt_gui"):
                    offenders.append(f"{path.relative_to(PACKAGE)}:{node.lineno} {name}")
    assert offenders == []


def test_agent_dtos_load_no_pyqt() -> None:
    script = (
        "import importlib, pkgutil, sys\n"
        "import openhcs.agent.dto as dto\n"
        "for info in pkgutil.iter_modules(dto.__path__, 'openhcs.agent.dto.'):\n"
        "    importlib.import_module(info.name)\n"
        "print(sorted(m for m in sys.modules if m.split('.')[0] == 'PyQt6'))\n"
    )
    completed = subprocess.run(
        [sys.executable, "-c", script],
        capture_output=True,
        text=True,
        check=True,
        cwd=PACKAGE.parent,
    )
    assert completed.stdout.strip().splitlines()[-1] == "[]"


def test_actions_are_operation_classes_not_enum_rosters() -> None:
    assert not (PACKAGE / "agent" / "ui_bridge_actions.py").exists()
    offenders = []
    for root in (PACKAGE / "agent", SESSION_PACKAGE):
        for path, tree in _modules(root):
            for node in ast.walk(tree):
                if isinstance(node, ast.Lambda) and [
                    argument.arg for argument in node.args.args
                ] in (["widget"], ["window"], ["manager"]):
                    offenders.append(f"{path.relative_to(PACKAGE)}:{node.lineno} lambda")
    for path, tree in _modules(SESSION_PACKAGE):
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and any(
                isinstance(base, ast.Name) and base.id.endswith("Enum")
                for base in node.bases
            ):
                offenders.append(f"{path.relative_to(PACKAGE)}:{node.lineno} enum")
    assert offenders == []


def test_every_operation_declares_itself_and_headless_ones_are_tools() -> None:
    from openhcs.agent.capabilities import get_capability_registry

    tools = {capability.name: capability for capability in get_capability_registry().capabilities}
    for operation in SessionOperation.all():
        assert operation.label and operation.tooltip and operation.description, operation
        assert isinstance(operation.request, type), operation
        tool_name = f"openhcs_{operation.operation_id}"
        assert (tool_name in tools) is issubclass(operation, HeadlessOperation), operation
        if issubclass(operation, RendererOperation):
            assert not issubclass(operation, HeadlessOperation), operation
        if tool_name in tools:
            assert tools[tool_name].input_contract is operation.request
            assert tools[tool_name].side_effects == operation.side_effects


def test_pipeline_formats_are_importers_not_suffix_branches() -> None:
    offenders = []
    for root in (PACKAGE / "pyqt_gui", SESSION_PACKAGE):
        for path in sorted(root.rglob("*.py")):
            text = path.read_text(encoding="utf-8")
            for marker in ('== ".cppipe"', '!= ".cppipe"', '#openhcs-cppipe='):
                if marker in text:
                    offenders.append(f"{path.relative_to(PACKAGE)} {marker}")
    assert offenders == []


def test_dataset_scope_kinds_and_importers_register_from_the_domain() -> None:
    from openhcs.core.dataset_sources.dataset_scopes import DatasetScopeKind
    from openhcs.core.pipeline_import import PipelineImporter

    assert ".cppipe" in PipelineImporter.__registry__
    assert ".py" in PipelineImporter.__registry__
    assert "#openhcs-cppipe=" in DatasetScopeKind.__registry__
