"""The step editor window hosts the declared step tabs and follows its pipeline step."""

from __future__ import annotations

from types import SimpleNamespace

import pytest
from formbridge.protocols import codegen_provider, component_selection
from formbridge.protocols.component_selection import FunctionSelectionProviderABC
from objectstate import ObjectState, ObjectStateRegistry
from PyQt6.QtCore import QObject, pyqtSignal
from PyQt6.QtWidgets import QLabel
from pyqt_reactive.services.window_navigation import RegisteredWindowNavigationRequest
from pyqt_reactive.widgets.shared import ActionTabMaterialization

from openhcs.authoring.session.step_scopes import build_step_scope_id
from openhcs.core.config import PipelineConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import percentile_normalize
from openhcs.pyqt_gui.services.reactor_providers import (
    OpenHCSCodegenProvider,
    OpenHCSComponentSelectionProvider,
)
from openhcs.pyqt_gui.windows.dual_editor_session import StepEditorTab
from openhcs.pyqt_gui.windows.dual_editor_tabs import (
    ArtifactsTab,
    FunctionPatternTab,
    StepSettingsTab,
)
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow

PLATE = "dual-editor-plate"


class NoSelectionProvider(FunctionSelectionProviderABC):
    def select_function(self, parent=None, **context):
        raise AssertionError("These tests never open function selection")


class PlateSignals(QObject):
    orchestrator_config_changed = pyqtSignal(str, object)
    compiled = pyqtSignal(str, object)
    runtime = pyqtSignal(object)
    debug = pyqtSignal(object)


@pytest.fixture
def open_step_editor(qapp, monkeypatch):
    monkeypatch.setattr(
        component_selection,
        "_component_selection_provider",
        OpenHCSComponentSelectionProvider(),
    )
    monkeypatch.setattr(
        component_selection, "_function_selection_provider", NoSelectionProvider()
    )
    monkeypatch.setattr(codegen_provider, "_codegen_provider", OpenHCSCodegenProvider())
    plate = ObjectState(PipelineConfig(), scope_id=PLATE)
    ObjectStateRegistry.register(plate, _skip_snapshot=True)
    orchestrator = SimpleNamespace(pipeline_config=plate.to_object())
    windows: list[DualEditorWindow] = []

    def open_editor(step: FunctionStep, **kwargs) -> DualEditorWindow:
        state = ObjectState(step, scope_id=build_step_scope_id(PLATE, step), parent_state=plate)
        ObjectStateRegistry.register(state, _skip_snapshot=True)
        window = DualEditorWindow(
            step, orchestrator=orchestrator, plate_scope=PLATE, step_index=0, **kwargs
        )
        windows.append(window)
        qapp.processEvents()
        return window

    yield open_editor
    for window in windows:
        window._cleanup_managed_resources()
        window.deleteLater()
    qapp.processEvents()


def _step() -> FunctionStep:
    return FunctionStep(func=(percentile_normalize, {"high_percentile": 99.8}), name="norm")


def _tab_labels(window: DualEditorWindow) -> list[str]:
    bar = window.tab_body.tab_bar
    return [bar.tabText(index) for index in range(bar.count())]


def _field_request(window: DualEditorWindow, field_path: str):
    return RegisteredWindowNavigationRequest(
        window=window, requested_scope_id=window.scope_id, field_path=field_path
    )


def test_window_hosts_the_three_declared_step_tabs(open_step_editor) -> None:
    window = open_step_editor(_step())

    assert [type(tab) for tab in window.tabs] == [StepSettingsTab, FunctionPatternTab, ArtifactsTab]
    assert _tab_labels(window) == ["Step Settings", "Function Pattern", "Artifacts"]
    assert window.windowTitle() == "Edit Step: 1. norm"
    assert window.save_button.text() == "Save"
    assert not window.save_button.isEnabled()
    assert window.form_managers() == (window.tab(StepSettingsTab).editor.form_manager,)
    assert (
        window.window_code_document_driver()
        is window.tab(StepSettingsTab).editor.code_document_driver()
    )


def test_navigation_shows_the_tab_that_owns_the_field(open_step_editor) -> None:
    window = open_step_editor(_step())
    driver = window.window_navigation_driver()

    assert driver.owning_tabs(_field_request(window, "func")) == (window.tab(FunctionPatternTab),)
    assert driver.owning_tabs(_field_request(window, "name")) == (window.tab(StepSettingsTab),)
    # The step's ObjectState holds ``func`` but the step form shows no such field,
    # so only the function tab claims it; no tab order decides.
    step_form = window.tab(StepSettingsTab).editor.form_manager
    assert "func" in step_form.state.parameters
    assert not step_form.owns_field_path("func")
    assert not step_form.owns_field_path("func.token:abc|func")

    driver.prepare(_field_request(window, "func"))
    assert window.tab_body.current_widget() is window.tab(FunctionPatternTab).editor
    driver.prepare(_field_request(window, "name"))
    assert window.tab_body.current_widget() is window.tab(StepSettingsTab).editor


def test_edit_marks_dirty_and_save_hands_the_step_to_the_caller(open_step_editor, qapp) -> None:
    saved: list[FunctionStep] = []
    original = _step()
    window = open_step_editor(original, is_new=True, on_save_callback=saved.append)
    assert window.windowTitle() == "New Step: 1. norm"
    assert window.save_button.text() == "Create"

    window.state.update_parameter("name", "renamed")
    qapp.processEvents()
    assert window.windowTitle() == "* New Step: 1. renamed"
    assert window.save_button.isEnabled()

    window.save_managed_window(close_window=False)

    assert [step.name for step in saved] == ["renamed"]
    assert original.name == "norm"
    assert window.edited.pipeline_step is saved[0]
    assert window.windowTitle() == "Edit Step: 1. renamed"
    assert window.save_button.text() == "Save"


def test_empty_step_name_is_refused(open_step_editor, monkeypatch) -> None:
    from PyQt6.QtWidgets import QMessageBox

    warnings: list[str] = []
    monkeypatch.setattr(
        QMessageBox, "warning", lambda _parent, _title, text: warnings.append(text)
    )
    saved: list[FunctionStep] = []
    window = open_step_editor(_step(), on_save_callback=saved.append)
    window.state.update_parameter("name", " ")

    window.save_managed_window()

    assert warnings == ["Step name cannot be empty."]
    assert saved == []


def test_mutation_guard_blocks_save(open_step_editor, monkeypatch) -> None:
    from PyQt6.QtWidgets import QMessageBox

    errors: list[str] = []
    monkeypatch.setattr(
        QMessageBox, "critical", lambda _parent, _title, text: errors.append(text)
    )
    saved: list[FunctionStep] = []

    def refuse() -> None:
        raise RuntimeError("plate is running")

    window = open_step_editor(_step(), on_save_callback=saved.append, before_mutation=refuse)
    window.save_managed_window()

    assert saved == []
    assert errors == ["Failed to save:\nplate is running"]


def test_step_that_moved_or_was_replaced_is_followed_through_every_tab(open_step_editor) -> None:
    step = _step()
    window = open_step_editor(step)
    artifacts = window.tab(ArtifactsTab)
    indices: list[int] = []
    artifacts.view.set_step_index = indices.append
    other = FunctionStep(func=percentile_normalize, name="other")

    window._on_pipeline_changed([other, step])

    assert window.edited.list_position == 1
    assert window.tab(StepSettingsTab).editor.step_index == 1
    assert indices == [1]
    assert window.windowTitle() == "Edit Step: 2. norm"

    replaced: list[FunctionStep] = []
    artifacts.pipeline_step_replaced = replaced.append
    window._on_pipeline_changed([other, window.edited.step])

    assert replaced == [window.edited.step]
    assert window.edited.pipeline_step is window.edited.step

    window._on_pipeline_changed([other])
    assert window.edited.list_position == 1


def test_artifact_and_config_signals_are_owned_by_their_tabs(open_step_editor) -> None:
    signals = PlateSignals()
    window = open_step_editor(_step())
    artifacts = window.tab(ArtifactsTab)
    settings = window.tab(StepSettingsTab)
    runtime: list[object] = []
    configs: list[object] = []
    artifacts.view.apply_runtime_notification = runtime.append
    settings.editor.use_pipeline_config = configs.append
    artifacts.follow_artifact_signals(
        compiled_artifact_signal=signals.compiled,
        runtime_artifact_signal=signals.runtime,
        debug_snapshot_signal=signals.debug,
    )
    settings.follow_orchestrator_config(signals.orchestrator_config_changed)
    ours = SimpleNamespace(event=SimpleNamespace(subject_id=PLATE))
    theirs = SimpleNamespace(event=SimpleNamespace(subject_id="another-plate"))

    signals.runtime.emit(theirs)
    signals.runtime.emit(ours)
    signals.orchestrator_config_changed.emit("another-plate", None)
    signals.orchestrator_config_changed.emit(PLATE, None)

    assert runtime == [ours]
    assert configs == [window.edited.orchestrator.pipeline_config]

    window._cleanup_managed_resources()
    signals.runtime.emit(ours)
    signals.orchestrator_config_changed.emit(PLATE, None)

    assert runtime == [ours]
    assert len(configs) == 1


def test_a_fourth_step_tab_is_hosted_without_touching_the_window(open_step_editor) -> None:
    """New-case: declare a tab; ``DualEditorWindow`` is not edited."""
    declared_before = StepEditorTab.declared_tabs()

    class NotesTab(StepEditorTab):
        label = "Notes"

        def build(self) -> ActionTabMaterialization:
            self.moved_to: list[int] = []
            return ActionTabMaterialization(QLabel(f"notes for {self.edit.step.name}"))

        def set_step_index(self, index: int) -> None:
            self.moved_to.append(index)

    try:
        step = _step()
        window = open_step_editor(step)

        assert _tab_labels(window) == ["Step Settings", "Function Pattern", "Artifacts", "Notes"]
        notes = window.tab(NotesTab)
        notes.select()
        assert window.tab_body.current_widget().text() == "notes for norm"
        window._on_pipeline_changed([FunctionStep(func=percentile_normalize, name="x"), step])
        assert notes.moved_to == [1]
    finally:
        # A class statement is a declaration: withdraw this one so later windows
        # in the same process host the three real tabs only.
        StepEditorTab.declared_tabs = classmethod(lambda cls: declared_before)  # type: ignore[method-assign]
