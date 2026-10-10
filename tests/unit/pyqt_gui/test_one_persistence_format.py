"""User state persists only as generated Python (surface F1)."""

from __future__ import annotations

import ast
from pathlib import Path

from pyqt_reactive.protocols import register_codegen_provider
from pyqt_reactive.services.function_pattern_code_document import (
    FunctionPatternCodeDocumentService,
)

from openhcs.core.path_cache import PathCacheKey
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends import cellprofiler as cellprofiler_backend
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)
from openhcs.pyqt_gui.services.function_step_code_document import (
    FunctionStepCodeDocumentDriver,
)
from openhcs.pyqt_gui.services.main_window_workflows import MainWindowPipelineActions
from openhcs.pyqt_gui.services.reactor_providers import OpenHCSCodegenProvider
from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget
from tests.unit.pyqt_gui.session_harness import (
    release_widgets,
    GuiServiceStub,
    add_datasets,
    caller_session,
    qt_app,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
PERSISTENCE_TREES = (
    REPO_ROOT / "openhcs" / "pyqt_gui",
    REPO_ROOT / "openhcs" / "ui" / "shared",
)
# In-memory ZMQ replies, not files.
TRANSPORT_MODULES = frozenset(
    {REPO_ROOT / "openhcs" / "pyqt_gui" / "services" / "ui_bridge_server.py"}
)
PICKLE_MODULES = frozenset({"pickle", "dill", "cloudpickle"})


def _normalize(low: float) -> tuple:
    """One function-pattern entry in the form the documents render (no defaults)."""
    return (
        RegistryService.registered_callable(stack_percentile_normalize),
        {"low_percentile": low, "high_percentile": 98.0},
    )


def test_pipeline_round_trips_through_python_file(tmp_path: Path) -> None:
    app = qt_app()
    target = tmp_path / "pipeline.py"
    with caller_session() as session:
        saved_scope, loaded_scope = add_datasets(session, tmp_path, "saved", "loaded")
        editor = PipelineEditorWidget(GuiServiceStub(), session)
        actions = MainWindowPipelineActions(None, editor)
        try:
            session.set_pipeline(
                saved_scope,
                [
                    FunctionStep(func=_normalize(2.0), name="Normalize"),
                    FunctionStep(func=cellprofiler_backend.crop, name="Crop"),
                ],
            )
            session.select((saved_scope,))
            app.processEvents()
            actions.save_pipeline(target)
            session.select((loaded_scope,))
            app.processEvents()
            actions.open_pipeline(target)
            app.processEvents()

            loaded = session.pipeline_steps(loaded_scope)
            assert [step.name for step in loaded] == ["Normalize", "Crop"]
            assert loaded[0].func == session.pipeline_steps(saved_scope)[0].func
            assert loaded[1].func[0] is RegistryService.registered_callable(
                cellprofiler_backend.crop
            )
            function, kwargs = loaded[0].func
            assert (function, {key: kwargs[key] for key in _normalize(2.0)[1]}) == (
                _normalize(2.0)
            )
            assert [step.name for step in editor.displayed_steps] == ["Normalize", "Crop"]
            assert editor.code_document_source(clean=True) == target.read_text(
                encoding="utf-8"
            )
        finally:
            editor.close()
            release_widgets(qt_app(), editor)


def test_step_settings_round_trip_through_python_file(tmp_path: Path) -> None:
    step = FunctionStep(func=_normalize(3.0), name="Normalize")
    applied: list[FunctionStep] = []
    driver = FunctionStepCodeDocumentDriver(
        title="Edit Step",
        current_step=lambda: step,
        apply_step=applied.append,
    )
    target = tmp_path / "step.py"

    target.write_text(driver.read_document().source, encoding="utf-8")
    driver.apply_source(target.read_text(encoding="utf-8"))

    assert len(applied) == 1
    assert applied[0].name == "Normalize"
    assert applied[0].func == _normalize(3.0)
    reloaded = FunctionStepCodeDocumentDriver(
        title="Edit Step",
        current_step=lambda: applied[0],
        apply_step=applied.append,
    )
    assert reloaded.read_document().source == target.read_text(encoding="utf-8")


def test_function_pattern_round_trips_through_python_file(tmp_path: Path) -> None:
    register_codegen_provider(OpenHCSCodegenProvider())
    service = FunctionPatternCodeDocumentService()
    pattern = {"1": _normalize(2.5), "2": [_normalize(4.0), _normalize(5.0)]}
    target = tmp_path / "pattern.py"

    target.write_text(
        service.generate_complete_function_pattern_code(pattern, clean_mode=True),
        encoding="utf-8",
    )

    assert service.pattern_from_source(target.read_text(encoding="utf-8")) == pattern


def _pickle_uses(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    aliases: set[str] = set()
    uses: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name.split(".")[0] in PICKLE_MODULES:
                    aliases.add(alias.asname or alias.name)
                    uses.append(f"{path}:{node.lineno} import {alias.name}")
        elif isinstance(node, ast.ImportFrom) and node.module is not None:
            if node.module.split(".")[0] in PICKLE_MODULES:
                uses.append(f"{path}:{node.lineno} from {node.module} import")
    for node in ast.walk(tree):
        if (
            isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id in aliases
            and node.attr in {"dump", "load", "Pickler", "Unpickler"}
        ):
            uses.append(f"{path}:{node.lineno} {node.value.id}.{node.attr}")
    return uses


def test_gui_persistence_modules_do_not_pickle() -> None:
    offenders: list[str] = []
    for tree in PERSISTENCE_TREES:
        for path in sorted(tree.rglob("*.py")):
            if path in TRANSPORT_MODULES:
                assert not any(
                    use.endswith((".dump", ".load"))
                    for use in _pickle_uses(path)
                ), f"{path} may pickle in memory for ZMQ only"
                continue
            offenders.extend(_pickle_uses(path))
    assert offenders == []


def test_gui_offers_no_pickle_file_formats() -> None:
    retired = ("*.func", "*.pipeline", "*.step", ".func\"", ".pipeline\"", ".step\"")
    offenders = [
        f"{path}: {marker}"
        for tree in PERSISTENCE_TREES
        for path in sorted(tree.rglob("*.py"))
        for marker in retired
        if marker in path.read_text(encoding="utf-8")
    ]
    assert offenders == []
    assert [key.name for key in PathCacheKey] == ["PLATE_IMPORT"]
