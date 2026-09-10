"""Exercise step code application with live function parameter widgets."""

import pytest
from PyQt6.QtWidgets import QVBoxLayout, QWidget
from objectstate import ObjectState, ObjectStateRegistry

from openhcs.core.config import PipelineConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import percentile_normalize
from openhcs.pyqt_gui.services.reactor_providers import (
    OpenHCSCodegenProvider,
    OpenHCSComponentSelectionProvider,
)
from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
from pyqt_reactive.protocols import (
    FunctionSelectionProviderABC,
    codegen_provider,
    component_selection,
)
from pyqt_reactive.widgets.function_list_editor import FunctionListEditorWidget


class NoSelectionProvider(FunctionSelectionProviderABC):
    def select_function(self, parent=None, **context):
        raise AssertionError("Editing an existing parameter must not open function selection")


@pytest.fixture
def step_editor(qapp, qtbot, monkeypatch):
    ObjectStateRegistry.clear()
    monkeypatch.setattr(component_selection, "_component_selection_provider", OpenHCSComponentSelectionProvider())
    monkeypatch.setattr(component_selection, "_function_selection_provider", NoSelectionProvider())
    monkeypatch.setattr(codegen_provider, "_codegen_provider", OpenHCSCodegenProvider())
    plate = ObjectState(PipelineConfig(), scope_id="roundtrip-plate")
    step = FunctionStep(func=(percentile_normalize, {"high_percentile": 99.8}))
    state = ObjectState(step, scope_id="roundtrip-plate::step", parent_state=plate)
    ObjectStateRegistry.register(plate, _skip_snapshot=True)
    ObjectStateRegistry.register(state, _skip_snapshot=True)
    host = QWidget()
    qtbot.addWidget(host)
    layout = QVBoxLayout(host)
    host.func_editor = FunctionListEditorWidget(
        step.func, scope_id=state.scope_id, parent=host,
    )
    editor = StepParameterEditorWidget(
        step, parent=host, scope_id=state.scope_id, pipeline_config=plate.to_object(),
    )
    layout.addWidget(editor)
    layout.addWidget(host.func_editor)
    host.show()
    qtbot.waitUntil(lambda: bool(host.func_editor.function_panes))
    yield editor, host.func_editor
    host.close()
    ObjectStateRegistry.clear()


@pytest.mark.parametrize("value", [99.6, 99.8, 25])
def test_step_code_updates_existing_function_state_and_widget(step_editor, qtbot, value):
    editor, functions = step_editor
    original_state = functions.function_panes[0].form_manager.state
    new_step = FunctionStep(func=(percentile_normalize, {"high_percentile": value}))
    editor._apply_step_from_code_document(new_step)
    qtbot.waitUntil(
        lambda: functions.function_panes[0].form_manager.widgets[
            "high_percentile"
        ].value() == value
    )
    pane = functions.function_panes[0]
    assert pane.form_manager.state is original_state
    assert pane.form_manager.widgets["high_percentile"].cleanText() == str(value)
    assert original_state.parameters["high_percentile"] == value
    assert original_state.get_saved_resolved_value("high_percentile") == 99.8
    original_state.update_parameter("high_percentile", 97.5)
    current_step = editor._current_step_for_code_document()
    assert current_step.func[0][1]["high_percentile"] == 97.5
    assert "'high_percentile': 97.5" in functions._generate_complete_python_code()


def test_step_code_can_switch_between_chain_and_grouped_patterns(step_editor, qtbot):
    editor, functions = step_editor
    for pattern in (
        {"1": [(percentile_normalize, {"high_percentile": 95.5})]},
        [(percentile_normalize, {"high_percentile": 95.5})],
        {"2": [(percentile_normalize, {"high_percentile": 95.5})]},
    ):
        editor._apply_step_from_code_document(FunctionStep(func=pattern))
        assert functions.is_dict_mode == isinstance(pattern, dict)
        qtbot.waitUntil(lambda: bool(functions.function_panes))
        pane = functions.function_panes[0]
        assert pane.form_manager.widgets["high_percentile"].value() == 95.5
        assert pane.form_manager.state.parameters["high_percentile"] == 95.5
        assert editor._current_step_for_code_document().func == pattern


def test_removing_an_explicit_kwarg_restores_the_existing_widget_default(step_editor):
    editor, functions = step_editor
    state = functions.function_panes[0].form_manager.state
    editor._apply_step_from_code_document(FunctionStep(func=percentile_normalize))
    pane = functions.function_panes[0]
    assert pane.form_manager.state is state
    assert pane.form_manager.widgets["high_percentile"].value() == 99.0
    assert editor._current_step_for_code_document().func is percentile_normalize


def test_hidden_group_values_are_projected_from_their_child_states(step_editor, qtbot):
    editor, functions = step_editor
    pattern = {
        "1": [(percentile_normalize, {"high_percentile": 95.5})],
        "2": [(percentile_normalize, {"high_percentile": 96.5})],
    }
    editor._apply_step_from_code_document(FunctionStep(func=pattern))
    first_state = functions.function_panes[0].form_manager.state
    functions._select_pattern_key("2", commit_current_view=True, persist_selection=True)
    qtbot.waitUntil(lambda: functions.function_panes[0].form_manager.state is not first_state)
    first_state.update_parameter("high_percentile", 98.5)
    resolved = editor._current_step_for_code_document().func
    assert resolved["1"][0][1]["high_percentile"] == 98.5
    assert resolved["2"][0][1]["high_percentile"] == 96.5
