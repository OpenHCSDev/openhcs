from __future__ import annotations

import re
from contextlib import contextmanager
from copy import copy
from dataclasses import dataclass
from pathlib import Path

import pytest
from objectstate.object_state import ObjectState, ObjectStateRegistry
from PyQt6.QtCore import Qt
from pyqt_reactive.forms.parameter_form_manager import (
    FormManagerConfig,
    ParameterFormManager,
)
from pyqt_reactive.services.function_navigation import (
    build_function_token_field_path,
)
from pyqt_reactive.services.function_pattern_code_document import (
    FunctionPatternCodeDocumentService,
)
from pyqt_reactive.services.pattern_data_manager import (
    FUNC_EDITOR_PATTERN_TOKENS_META_KEY,
)
from pyqt_reactive.services.scope_token_service import ScopeTokenService
from pyqt_reactive.theming import ColorScheme

from openhcs.authoring.session.compilation import CompiledDataset
from openhcs.authoring.session.events import PipelineChanged
from openhcs.authoring.session.operations.pipelines import (
    AddPipelineStep,
    DeletePipelineSteps,
    EditPipelineStep,
)
from openhcs.authoring.session.pipelines import (
    PipelineEditorStateRoot,
    PipelineObjectStateBinding,
)
from openhcs.authoring.session.step_scopes import StepEditorScope
from openhcs.constants.constants import OrchestratorState
from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.axes import Ungrouped
from openhcs.core.config import (
    LazyProcessingConfig,
    LazyStepWellFilterConfig,
    PipelineConfig,
)
from openhcs.core.debug import DebugCommandType
from openhcs.core.execution_state import ManagerExecutionState
from openhcs.core.pipeline.function_contracts import artifact_inputs
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps.function_step import FunctionStep
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.interop.cellprofiler.dataset_scope import CellProfilerPipelineScope
from openhcs.processing.backends.cellprofiler import correct_illumination_apply
from openhcs.processing.backends.cellprofiler.illumination import (
    IlluminationCorrectionMethod,
)
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow
from openhcs.ui.shared.code_editor_form_updater import CodeEditorFormUpdater
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity
from tests.unit.pyqt_gui.session_harness import add_datasets, qt_app, session_gui

TEST_PLATE_SCOPE = "plate"


def _cellprofiler_scope() -> str:
    return CellProfilerPipelineScope.scope_for(
        Path("/tmp/plate"), Path("/tmp/plate/Analysis_Final.cppipe")
    ).scope_id


@dataclass
class EditorGui:
    """A pipeline editor showing one initialized dataset of a session."""

    gui: object
    scope_id: str

    @property
    def session(self):
        return self.gui.session

    @property
    def editor(self):
        return self.gui.pipeline_editor

    def set_steps(self, steps) -> None:
        self.session.set_pipeline(self.scope_id, list(steps))
        self.gui.settle()

    def select_rows(self, *rows: int) -> None:
        self.editor.item_list.clearSelection()
        for row in rows:
            self.editor.item_list.item(row).setSelected(True)
        self.gui.settle()
        self.editor.update_button_states()


@contextmanager
def editor_gui(tmp_path, *, initialized: bool = True):
    with session_gui() as gui:
        (scope_id,) = add_datasets(gui.session, tmp_path, "plate")
        if initialized:
            gui.session.set_dataset_state(scope_id, OrchestratorState.READY)
        gui.settle()
        yield EditorGui(gui, scope_id)


def _document(*steps: FunctionStep) -> str:
    return PipelineDocumentCodec.render(
        PipelineDocumentCodec.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=list(steps)
        )
    )


def _identity(image):
    return image


def test_function_pattern_form_exposes_explicit_kwargs_outside_callable_signature() -> (
    None
):
    qt_app()
    ObjectStateRegistry.clear()
    step = FunctionStep(
        func=(
            correct_illumination_apply,
            {
                "name_the_output_image": "CorrectedStain1",
                "truncate_low": True,
                "truncate_high": True,
                "method": IlluminationCorrectionMethod.DIVIDE,
                "select_the_illumination_function": "IllumStain1",
                "select_the_input_image": "OrigStain1",
                "enabled": True,
            },
        ),
        name="CorrectIlluminationApply",
    )

    try:
        PipelineObjectStateBinding.update_plate_steps("plate", [step])
        editor_state = PipelineObjectStateBinding.editor_state_for_plate("plate")
        step_state = ObjectStateRegistry.get_by_scope(editor_state.step_scope_ids[0])
        assert step_state is not None
        [function_token] = step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY]
        child_state = ObjectStateRegistry.get_by_scope(
            f"{step_state.scope_id}::{function_token}"
        )
        assert child_state is not None
        manager = ParameterFormManager(
            child_state,
            FormManagerConfig(color_scheme=ColorScheme()),
        )

        expected = {
            "method",
            "truncate_low",
            "truncate_high",
            "enabled",
            "select_the_input_image",
            "select_the_illumination_function",
            "name_the_output_image",
        }
        assert expected <= set(manager.parameters)
        assert expected <= set(manager.parameter_types)
        entry = FunctionPatternCodeDocumentService().child_scope_entry(
            child_state.scope_id
        )
        assert entry.func is correct_illumination_apply
        assert entry.kwargs["name_the_output_image"] == "CorrectedStain1"
    finally:
        ObjectStateRegistry.clear()


def test_step_code_mode_applies_callable_pattern_through_parameter_form() -> None:
    """A parsed FunctionStep can update the live form's Callable field."""

    qt_app()
    ObjectStateRegistry.clear()
    original = FunctionStep(func=stack_percentile_normalize, name="Normalize")
    replacement = FunctionStep(
        func=(stack_percentile_normalize, {"low_percentile": 0.75}),
        name="Normalize edited",
    )
    manager = None

    try:
        PipelineObjectStateBinding.update_plate_steps(TEST_PLATE_SCOPE, [original])
        [step_scope_id] = PipelineObjectStateBinding.editor_state_for_plate(
            TEST_PLATE_SCOPE
        ).step_scope_ids
        step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
        assert step_state is not None
        manager = ParameterFormManager(
            step_state,
            FormManagerConfig(color_scheme=ColorScheme()),
        )

        CodeEditorFormUpdater.update_form_from_instance(manager, replacement)

        assert step_state.parameters["name"] == "Normalize edited"
        func, kwargs = step_state.parameters["func"]
        assert func is stack_percentile_normalize
        assert kwargs["low_percentile"] == 0.75
    finally:
        if manager is not None:
            manager.deleteLater()
        ObjectStateRegistry.clear()


class RuntimeCallable:
    """Callable object with a non-function scope prefix."""

    def __call__(self, image, threshold: int = 1):
        return image


@dataclass(frozen=True)
class RuntimeSettings:
    threshold: int = 1


def runtime_with_settings(
    image,
    settings: RuntimeSettings = RuntimeSettings(),
):
    return image


def test_pipeline_binding_replaces_one_step_before_returning_projection() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    original = FunctionStep(func=runtime_with_settings, name="Original")
    PipelineObjectStateBinding.update_plate_steps(TEST_PLATE_SCOPE, [original])
    [current] = PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)
    [scope_id] = PipelineObjectStateBinding.editor_state_for_plate(
        TEST_PLATE_SCOPE
    ).step_scope_ids

    [projected] = PipelineObjectStateBinding.replace_plate_step(
        TEST_PLATE_SCOPE,
        current,
        FunctionStep(func=runtime_with_settings, name="Edited"),
    )

    [stored] = PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)
    [replacement_scope_id] = PipelineObjectStateBinding.editor_state_for_plate(
        TEST_PLATE_SCOPE
    ).step_scope_ids
    assert projected.name == "Edited"
    assert stored.name == "Edited"
    assert replacement_scope_id == scope_id


def test_step_registration_preserves_and_updates_nested_function_kwargs() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope("plate")
    initial_settings = RuntimeSettings(threshold=3)
    replacement_settings = RuntimeSettings(threshold=7)

    PipelineObjectStateBinding.update_plate_steps(
        "plate",
        [
            FunctionStep(
                func=(runtime_with_settings, {"settings": initial_settings}),
                name="Nested settings",
            )
        ],
    )

    initial_editor_state = PipelineObjectStateBinding.editor_state_for_plate("plate")
    initial_step_scope_id = initial_editor_state.step_scope_ids[0]
    initial_step_state = ObjectStateRegistry.get_by_scope(initial_step_scope_id)
    assert initial_step_state is not None
    function_token = initial_step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY][0]
    function_scope_id = f"{initial_step_scope_id}::{function_token}"
    initial_function_state = ObjectStateRegistry.get_by_scope(function_scope_id)
    assert initial_function_state is not None
    assert initial_function_state.parameters["settings"] == initial_settings
    assert initial_function_state.parameters["settings.threshold"] == 3
    assert initial_function_state.reconstruct_top_level_parameters() == {
        "settings": initial_settings,
    }

    initial_step = PipelineObjectStateBinding.steps_for_plate("plate")[0]
    assert initial_step.func[1]["settings"] == initial_settings

    PipelineObjectStateBinding.update_plate_steps(
        "plate",
        [
            FunctionStep(
                func=(runtime_with_settings, {"settings": replacement_settings}),
                name="Nested settings",
            )
        ],
    )

    replacement_function_state = ObjectStateRegistry.get_by_scope(function_scope_id)
    assert replacement_function_state is initial_function_state
    assert replacement_function_state.parameters["settings"] == replacement_settings
    assert replacement_function_state.parameters["settings.threshold"] == 7
    assert replacement_function_state.reconstruct_top_level_parameters() == {
        "settings": replacement_settings,
    }

    replacement_step = PipelineObjectStateBinding.steps_for_plate("plate")[0]
    assert replacement_step.func[1]["settings"] == replacement_settings

    PipelineObjectStateBinding.update_plate_steps(
        "plate",
        [
            FunctionStep(
                func=runtime_with_settings,
                name="Nested settings",
            )
        ],
    )

    reset_function_state = ObjectStateRegistry.get_by_scope(function_scope_id)
    assert reset_function_state is initial_function_state
    assert reset_function_state.parameters["settings"] == RuntimeSettings()
    assert reset_function_state.parameters["settings.threshold"] == 1
    assert reset_function_state.reconstruct_top_level_parameters() == {
        "settings": RuntimeSettings(),
    }

    reset_step = PipelineObjectStateBinding.steps_for_plate("plate")[0]
    assert reset_step.func[1]["settings"] == RuntimeSettings()


def test_reconstructed_pipeline_save_notifies_only_edited_step() -> None:
    """Selecting a new test plate must not expand every callable baseline."""

    from openhcs.demo.synthetic_plate_pipeline import pipeline_steps

    plate_scope = "synthetic-plate"
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(plate_scope)
    events: list[tuple[str, set[str]]] = []

    def record_change(scope_id: str, changed_paths: set[str]) -> None:
        events.append((scope_id, set(changed_paths)))

    try:
        PipelineObjectStateBinding.update_plate_steps(
            plate_scope,
            list(pipeline_steps),
        )
        selected_steps = PipelineObjectStateBinding.steps_for_plate(plate_scope)
        editor_state = PipelineObjectStateBinding.editor_state_for_plate(plate_scope)

        edited_steps = list(selected_steps)
        edited_steps[2] = copy(edited_steps[2])
        edited_steps[2].name = "Edited only"

        ObjectStateRegistry.add_resolved_changed_callback(record_change)
        PipelineObjectStateBinding.update_plate_steps(plate_scope, edited_steps)

        assert events == [(editor_state.step_scope_ids[2], {"name"})]
    finally:
        ObjectStateRegistry.remove_resolved_changed_callback(record_change)
        ObjectStateRegistry.clear()


def test_reconstructed_pipeline_preserves_explicit_default_function_kwarg() -> None:
    """Canonical parent baselines retain explicitly authored default kwargs."""

    def threshold_image(image, threshold: int = 1):
        del threshold
        return image

    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope("plate")
    try:
        PipelineObjectStateBinding.update_plate_steps(
            "plate",
            [
                FunctionStep(
                    func=(threshold_image, {"threshold": 1}),
                    name="Threshold",
                )
            ],
        )

        reconstructed = PipelineObjectStateBinding.steps_for_plate("plate")

        assert reconstructed[0].func == (threshold_image, {"threshold": 1})
    finally:
        ObjectStateRegistry.clear()


def test_pipeline_diff_adds_and_removes_compile_time_function_kwarg() -> None:
    """Code-mode diffs rebuild child state when callable fields change."""

    def process(image):
        return image

    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope("plate")
    try:
        PipelineObjectStateBinding.update_plate_steps(
            "plate",
            [FunctionStep(func=process, name="Process")],
        )
        PipelineObjectStateBinding.update_plate_steps(
            "plate",
            [
                FunctionStep(
                    func=(process, {"artifact_name": "Nuclei"}),
                    name="Process",
                )
            ],
        )

        [with_identity] = PipelineObjectStateBinding.steps_for_plate("plate")
        assert with_identity.func == (process, {"artifact_name": "Nuclei"})

        PipelineObjectStateBinding.update_plate_steps(
            "plate",
            [FunctionStep(func=process, name="Process")],
        )
        [without_identity] = PipelineObjectStateBinding.steps_for_plate("plate")
        assert without_identity.func is process
    finally:
        ObjectStateRegistry.clear()


def test_step_registration_persists_function_editor_scope_tokens() -> None:
    ObjectStateRegistry._states.clear()
    ScopeTokenService.clear_scope("plate")

    runtime_callable = RuntimeCallable()
    step = FunctionStep(
        func=(runtime_callable, {"threshold": 3}),
        name="Crop",
    )
    PipelineObjectStateBinding.update_plate_steps("plate", [step])
    editor_state = PipelineObjectStateBinding.editor_state_for_plate("plate")
    step_state = ObjectStateRegistry.get_by_scope(editor_state.step_scope_ids[0])
    assert step_state is not None

    assert step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY] == [
        "func_0",
    ]
    assert len(editor_state.step_scope_ids) == 1
    step_scope_id = editor_state.step_scope_ids[0]
    child_scope_id = f"{step_scope_id}::func_0"
    assert ObjectStateRegistry.get_by_scope(child_scope_id) is not None
    assert sorted(
        scope_id
        for scope_id in ObjectStateRegistry._states
        if scope_id.startswith(step_scope_id)
    ) == [
        step_scope_id,
        child_scope_id,
    ]


def test_complete_pipeline_diff_preserves_reordered_and_edited_step_scopes() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    try:
        PipelineObjectStateBinding.update_plate_steps(
            TEST_PLATE_SCOPE,
            [
                FunctionStep(func=stack_percentile_normalize, name="Normalize"),
                FunctionStep(func=correct_illumination_apply, name="Correct"),
            ],
        )
        previous_scope_ids = PipelineObjectStateBinding.editor_state_for_plate(
            TEST_PLATE_SCOPE
        ).step_scope_ids
        normalize_scope, correct_scope = previous_scope_ids
        normalize_state = ObjectStateRegistry.get_by_scope(normalize_scope)
        assert normalize_state is not None

        PipelineObjectStateBinding.update_plate_steps(
            TEST_PLATE_SCOPE,
            [
                FunctionStep(func=correct_illumination_apply, name="Correct"),
                FunctionStep(func=stack_percentile_normalize, name="New normalize"),
            ],
        )

        replacement = PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)
        replacement_scope_ids = PipelineObjectStateBinding.editor_state_for_plate(
            TEST_PLATE_SCOPE
        ).step_scope_ids
        assert replacement_scope_ids == (correct_scope, normalize_scope)
        assert [
            FunctionPatternCodeDocumentService.function_and_kwargs(step.func)[0]
            for step in replacement
        ] == [
            correct_illumination_apply,
            stack_percentile_normalize,
        ]
        assert replacement[1].name == "New normalize"
        assert ObjectStateRegistry.get_by_scope(normalize_scope) is normalize_state
        assert normalize_state.dirty_fields == {"name"}
    finally:
        ObjectStateRegistry.clear()


def test_complete_pipeline_round_trip_preserves_repeated_step_scopes() -> None:
    from openhcs.demo.synthetic_plate_pipeline import pipeline_steps

    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    try:
        PipelineObjectStateBinding.update_plate_steps(
            TEST_PLATE_SCOPE,
            list(pipeline_steps),
        )
        original_scope_ids = PipelineObjectStateBinding.editor_state_for_plate(
            TEST_PLATE_SCOPE
        ).step_scope_ids
        original_states = tuple(
            ObjectStateRegistry.get_by_scope(scope_id)
            for scope_id in original_scope_ids
        )
        original_steps = PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)
        ObjectStateRegistry.ensure_baseline_snapshot()
        source = PipelineDocumentCodec.render(
            PipelineDocumentCodec.from_values(
                pipeline_config=PipelineConfig(),
                pipeline_steps=original_steps,
            )
        )
        edited_steps = PipelineDocumentCodec.from_source(source).pipeline_steps
        edited_steps[0] = copy(edited_steps[0])
        edited_steps[0].name = "Launch Readiness Enhancement"

        with ObjectStateRegistry.atomic("edit complete pipeline"):
            PipelineObjectStateBinding.update_plate_steps(
                TEST_PLATE_SCOPE,
                edited_steps,
            )

        assert (
            PipelineObjectStateBinding.editor_state_for_plate(
                TEST_PLATE_SCOPE
            ).step_scope_ids
            == original_scope_ids
        )
        assert all(
            ObjectStateRegistry.get_by_scope(scope_id) is original_state
            for scope_id, original_state in zip(
                original_scope_ids,
                original_states,
            )
        )
        assert len(PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)) == len(
            pipeline_steps
        )
        assert ObjectStateRegistry.time_travel_back()
        assert len(PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)) == len(
            pipeline_steps
        )
        assert (
            PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)[0].name
            == "Image Enhancement Processing"
        )
        assert ObjectStateRegistry.time_travel_forward()
        assert len(PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)) == len(
            pipeline_steps
        )
        assert (
            PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)[0].name
            == "Launch Readiness Enhancement"
        )
    finally:
        ObjectStateRegistry.clear()


def test_complete_pipeline_diff_adds_and_removes_only_changed_occurrences() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    try:
        PipelineObjectStateBinding.update_plate_steps(
            TEST_PLATE_SCOPE,
            [
                FunctionStep(func=stack_percentile_normalize, name="Normalize"),
                FunctionStep(func=correct_illumination_apply, name="Correct"),
            ],
        )
        normalize_scope, correct_scope = (
            PipelineObjectStateBinding.editor_state_for_plate(
                TEST_PLATE_SCOPE
            ).step_scope_ids
        )

        PipelineObjectStateBinding.update_plate_steps(
            TEST_PLATE_SCOPE,
            [FunctionStep(func=correct_illumination_apply, name="Correct")],
        )

        assert PipelineObjectStateBinding.editor_state_for_plate(
            TEST_PLATE_SCOPE
        ).step_scope_ids == (correct_scope,)
        assert ObjectStateRegistry.get_by_scope(normalize_scope) is None

        PipelineObjectStateBinding.update_plate_steps(
            TEST_PLATE_SCOPE,
            [
                FunctionStep(func=correct_illumination_apply, name="Correct"),
                FunctionStep(func=stack_percentile_normalize, name="Added"),
            ],
        )
        correct_after_add, added_scope = (
            PipelineObjectStateBinding.editor_state_for_plate(
                TEST_PLATE_SCOPE
            ).step_scope_ids
        )
        assert correct_after_add == correct_scope
        assert added_scope not in {normalize_scope, correct_scope}
    finally:
        ObjectStateRegistry.clear()


def test_step_registration_does_not_publish_runtime_artifact_parameters() -> None:
    ObjectStateRegistry._states.clear()
    ScopeTokenService.clear_scope("plate")

    @artifact_inputs("positions")
    def assemble(image, positions=None, threshold: int = 1):
        del positions, threshold
        return image

    PipelineObjectStateBinding.update_plate_steps(
        "plate",
        [FunctionStep(func=assemble, name="Assemble")],
    )
    editor_state = PipelineObjectStateBinding.editor_state_for_plate("plate")
    step_scope_id = editor_state.step_scope_ids[0]
    step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
    assert step_state is not None
    token = step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY][0]
    child_state = ObjectStateRegistry.get_by_scope(f"{step_scope_id}::{token}")
    assert child_state is not None

    assert "positions" not in child_state.parameters
    reconstructed_step = PipelineObjectStateBinding.steps_for_plate("plate")[0]
    assert reconstructed_step.func == (assemble, {"threshold": 1})


def test_step_registration_exposes_public_cellprofiler_settings_in_function_child_state() -> (
    None
):
    ObjectStateRegistry._states.clear()
    ScopeTokenService.clear_scope("plate")

    runtime_callable = RuntimeCallable()
    step = FunctionStep(
        func=(
            runtime_callable,
            {
                "threshold": 3,
                "select_the_input_image": "OrigBlue",
            },
        ),
        name="Crop",
    )
    PipelineObjectStateBinding.update_plate_steps("plate", [step])
    editor_state = PipelineObjectStateBinding.editor_state_for_plate("plate")
    step_scope_id = editor_state.step_scope_ids[0]
    step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
    assert step_state is not None
    token = step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY][0]
    child_state = ObjectStateRegistry.get_by_scope(f"{step_scope_id}::{token}")
    assert child_state is not None
    reconstructed_step = PipelineObjectStateBinding.steps_for_plate("plate")[0]
    reconstructed_kwargs = reconstructed_step.func[1]

    assert child_state.reconstruct_top_level_parameters() == {
        "threshold": 3,
        "select_the_input_image": "OrigBlue",
    }
    assert reconstructed_kwargs["threshold"] == 3
    assert reconstructed_kwargs["select_the_input_image"] == "OrigBlue"


def test_pipeline_editor_root_preserves_only_text_and_step_scope_ids() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope("plate")

    steps = [
        FunctionStep(
            func=(RuntimeCallable(), {"threshold": 3}),
            name="ImportedStep",
        )
    ]
    PipelineObjectStateBinding.update_plate_steps("plate", steps)
    PipelineObjectStateBinding.update_editor_text(
        "plate",
        name="ImportedPipeline",
        description="Imported description",
    )

    editor_state = PipelineObjectStateBinding.editor_state_for_plate("plate")
    step_scope_id = editor_state.step_scope_ids[0]
    assert editor_state == PipelineEditorStateRoot(
        name="ImportedPipeline",
        description="Imported description",
        step_scope_ids=(step_scope_id,),
    )
    assert [
        step.name for step in PipelineObjectStateBinding.steps_for_plate("plate")
    ] == ["ImportedStep"]
    assert not hasattr(editor_state, "metadata")
    assert not hasattr(editor_state, "pipeline_config")


def test_pipeline_object_state_binding_public_surface_is_editor_list_only() -> None:
    public_methods = {
        name
        for name, value in PipelineObjectStateBinding.__dict__.items()
        if not name.startswith("_")
        and (isinstance(value, (classmethod, staticmethod)) or callable(value))
    }

    assert public_methods == {
        "commit_plate_state",
        "discard_staged_step",
        "editor_state_for_plate",
        "registered_plate_steps",
        "replace_plate_step",
        "stage_step",
        "steps_for_plate",
        "update_editor_text",
        "update_plate_steps",
    }
    assert tuple(PipelineEditorStateRoot.__dataclass_fields__) == (
        "name",
        "description",
        "step_scope_ids",
    )
    assert PipelineEditorStateRoot.__slots__ == (
        "name",
        "description",
        "step_scope_ids",
    )


def test_groupby_none_is_concrete_object_state_override() -> None:
    ObjectStateRegistry.clear()

    assert not (Ungrouped == None)  # noqa: E711
    assert not (None == Ungrouped)  # noqa: E711

    state = ObjectState(
        FunctionStep(
            name="IdentifyPrimaryObjects",
            processing_config=LazyProcessingConfig(),
        ),
        scope_id="plate::functionstep_0",
    )

    state.update_parameter("processing_config.group_by", Ungrouped)

    assert state.parameters["processing_config.group_by"] is Ungrouped
    assert "processing_config.group_by" in state.signature_diff_fields

    state.reset_parameter("processing_config.group_by")

    assert state.parameters["processing_config.group_by"] is None
    assert "processing_config.group_by" not in state.signature_diff_fields


def test_dual_editor_step_scope_uses_logical_plate_scope() -> None:
    logical_scope = _cellprofiler_scope()
    ScopeTokenService.clear_scope(logical_scope)

    step = FunctionStep(name="Threshold")
    window = DualEditorWindow.__new__(DualEditorWindow)
    window.plate_scope = logical_scope
    window.editing_step = step

    assert window._build_step_scope_id() == f"{logical_scope}::functionstep_0"


def test_step_editor_scope_parse_preserves_cppipe_plate_scope() -> None:
    plate_scope = _cellprofiler_scope()
    scope_id = f"{plate_scope}::functionstep_17::cellprofilerruntimecallable_0"

    parsed = StepEditorScope.parse(scope_id)

    assert parsed.plate_scope == plate_scope
    assert parsed.step_scope_id == f"{plate_scope}::functionstep_17"
    assert parsed.step_token.raw == "functionstep_17"
    assert parsed.is_function_scope is True


def test_step_editor_scope_handler_pattern_accepts_runtime_callable_tokens() -> None:
    plate_scope = _cellprofiler_scope()
    scope_id = f"{plate_scope}::functionstep_17::runtimecallable_0"

    assert re.match(StepEditorScope.handler_pattern(), scope_id)


def test_step_editor_child_scope_resolves_to_parent_window_navigation() -> None:
    plate_scope = _cellprofiler_scope()
    child_token = "cellprofilerruntimecallable_0"
    scope_id = f"{plate_scope}::functionstep_17::{child_token}"

    assert (
        StepEditorScope.window_scope_id_for_scope(scope_id)
        == f"{plate_scope}::functionstep_17"
    )
    assert StepEditorScope.window_field_path_for_scope(
        scope_id,
        "adaptive_window_size",
    ) == build_function_token_field_path(
        child_token,
        fallback_base_field_path="func.adaptive_window_size",
    )


def test_code_document_follows_the_current_dataset(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        assert harness.editor.debug_toolbar is not None
        assert harness.editor.current_plate == harness.scope_id
        assert harness.editor.code_document_writable()

        harness.session.select(())
        harness.gui.settle()

        assert harness.editor.current_plate == ""
        assert harness.editor.displayed_steps == []
        assert not harness.editor.code_document_writable()


def test_code_document_driver_reads_validates_and_applies(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps([FunctionStep(name="Original")])
        changed = []
        harness.session.subscribe(
            lambda record: changed.append(record.event.scope_id)
            if isinstance(record.event, PipelineChanged)
            else None
        )
        driver = harness.editor.code_document_driver()
        assert driver is not None

        document = driver.read_document(clean=True)
        assert document.title == "Edit Pipeline"
        assert "pipeline_config" in document.source
        assert "pipeline_steps" in document.source
        assert "Original" in document.source
        driver.validate_source(_document(FunctionStep(name="Applied")))
        with pytest.raises(SyntaxError):
            driver.validate_source("pipeline_steps = [\n")
        with pytest.raises(ValueError, match="pipeline_steps"):
            driver.validate_source("not_pipeline_steps = []\n")

        driver.apply_source(_document(FunctionStep(name="Replacement")))
        harness.gui.settle()

        assert [
            step.name for step in harness.session.pipeline_steps(harness.scope_id)
        ] == ["Replacement"]
        assert [step.name for step in harness.editor.displayed_steps] == ["Replacement"]
        assert harness.editor.item_list.count() == 1
        assert changed == [harness.scope_id]


def test_code_document_applies_while_a_batch_runs_but_not_while_compiling(
    tmp_path,
) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps([FunctionStep(name="Original")])
        driver = harness.editor.code_document_driver()
        harness.session.execution_state = ManagerExecutionState.RUNNING

        driver.apply_source(_document(FunctionStep(name="Replacement")))

        assert [
            step.name for step in harness.session.pipeline_steps(harness.scope_id)
        ] == ["Replacement"]

        harness.session.compile_pending.add(harness.scope_id)
        with pytest.raises(RuntimeError, match="affected dataset"):
            driver.apply_source(_document(FunctionStep(name="Rejected")))
        assert [
            step.name for step in harness.session.pipeline_steps(harness.scope_id)
        ] == ["Replacement"]


def test_code_document_commits_the_reconciled_step_tree(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps(
            [
                FunctionStep(
                    name="Normalize before",
                    func=(stack_percentile_normalize, {"low_percentile": 0.5}),
                )
            ]
        )
        scope_id = harness.scope_id
        [step_scope_id] = PipelineObjectStateBinding.editor_state_for_plate(
            scope_id
        ).step_scope_ids
        step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
        assert step_state is not None
        [function_token] = step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY]
        assert (
            ObjectStateRegistry.get_by_scope(f"{step_scope_id}::{function_token}")
            is not None
        )

        harness.editor.code_document_driver().apply_source(
            _document(
                FunctionStep(
                    name="Normalize after",
                    func=(stack_percentile_normalize, {"low_percentile": 0.75}),
                )
            )
        )

        [reconciled_scope_id] = PipelineObjectStateBinding.editor_state_for_plate(
            scope_id
        ).step_scope_ids
        assert reconciled_scope_id == step_scope_id
        assert ObjectStateRegistry.get_by_scope(step_scope_id) is step_state
        [reconciled_token] = step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY]
        function_state = ObjectStateRegistry.get_by_scope(
            f"{step_scope_id}::{reconciled_token}"
        )
        assert function_state is not None
        editor_state = ObjectStateRegistry.get_by_scope(
            PipelineScopeIdentity.from_plate_scope(scope_id).scope_id
        )
        assert editor_state is not None
        assert step_state.saved_object.name == "Normalize after"
        assert function_state.parameters["low_percentile"] == 0.75
        for state in (step_state, function_state, editor_state):
            assert not state.is_raw_dirty
            assert not state.dirty_fields


def test_code_document_reads_function_child_object_state(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps(
            [
                FunctionStep(
                    name="Normalize",
                    func=(
                        stack_percentile_normalize,
                        {"low_percentile": 0.5, "high_percentile": 99.5},
                    ),
                )
            ]
        )
        (step,) = harness.editor.displayed_steps
        step_scope = harness.editor.step_scope_id(step)
        step_state = ObjectStateRegistry.get_by_scope(step_scope)
        assert step_state is not None
        [function_token] = step_state.metadata[FUNC_EDITOR_PATTERN_TOKENS_META_KEY]
        function_state = ObjectStateRegistry.get_by_scope(
            f"{step_scope}::{function_token}"
        )
        assert function_state is not None

        function_state.update_parameter("low_percentile", 0.75)
        source = harness.editor.code_document_source(clean=True)

        assert "'low_percentile': 0.75" in source
        assert "'low_percentile': 0.5" not in source


def test_drag_reorder_moves_steps_by_transport_safe_row_identity(tmp_path) -> None:
    def locally_declared_function(image):
        return image

    with editor_gui(tmp_path) as harness:
        harness.set_steps(
            [
                FunctionStep(func=locally_declared_function, name="Local"),
                FunctionStep(func=stack_percentile_normalize, name="Normalize"),
            ]
        )
        steps = harness.editor.displayed_steps
        source_token = ScopeTokenService.object_token(steps[0])
        target_token = ScopeTokenService.object_token(steps[1])
        item_list = harness.editor.item_list
        source_item = item_list.item(0)
        assert source_token is not None
        assert target_token is not None
        assert source_item.data(Qt.ItemDataRole.UserRole) == source_token
        assert item_list.mimeData([source_item]) is not None

        item_list.insertItem(1, item_list.takeItem(0))
        harness.editor._on_items_reordered(0, 1)
        harness.gui.settle()

        assert [
            step.name for step in harness.session.pipeline_steps(harness.scope_id)
        ] == ["Normalize", "Local"]
        assert [
            item_list.item(index).data(Qt.ItemDataRole.UserRole)
            for index in range(item_list.count())
        ] == [target_token, source_token]


def test_time_travel_broadcasts_only_pipeline_level_restores(
    tmp_path, monkeypatch
) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps([FunctionStep(name="First"), FunctionStep(name="Second")])
        broadcasts = []
        monkeypatch.setattr(
            harness.gui.services.event_bus, "emit_pipeline_changed", broadcasts.append
        )

        harness.editor.on_time_travel_complete(
            [(f"{harness.scope_id}::functionstep_0", object())], None
        )
        assert broadcasts == []

        harness.editor.on_time_travel_complete(
            [(PipelineScopeIdentity.from_plate_scope(harness.scope_id).scope_id, object())],
            None,
        )
        assert [[step.name for step in steps] for steps in broadcasts] == [
            ["First", "Second"]
        ]
        assert [step.name for step in harness.editor.displayed_steps] == [
            "First",
            "Second",
        ]


def test_step_display_is_numbered_without_renaming_the_step(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps([FunctionStep(name="Measure"), FunctionStep(name="Measure")])
        first, second = harness.editor.displayed_steps

        first_display = harness.editor._format_item_content(first, 0, None)
        second_display = harness.editor._format_item_content(second, 1, None)
        _, semantic_name = harness.editor.format_item_for_display(second, step_index=1)

        assert first_display.layout.name.text == "1. Measure"
        assert second_display.layout.name.text == "2. Measure"
        assert semantic_name == "Measure"
        assert [step.name for step in harness.editor.displayed_steps] == [
            "Measure",
            "Measure",
        ]


class CallbackSignal:
    def __init__(self) -> None:
        self.callbacks = []

    def connect(self, callback) -> None:
        self.callbacks.append(callback)

    def emit(self) -> None:
        for callback in self.callbacks:
            callback()


class StepEditorRecorder:
    """Stands in for the step editor window; asserts its step scope is registered."""

    opened: list["StepEditorRecorder"] = []

    def __init__(self, *, step_data, is_new, on_save_callback, plate_scope, **kwargs):
        del kwargs
        self.step_data = step_data
        self.is_new = is_new
        self.on_save_callback = on_save_callback
        self.rejected = CallbackSignal()
        self.scope_id = ScopeTokenService.build_scope_id(plate_scope, step_data)
        self.state = ObjectStateRegistry.get_by_scope(self.scope_id)
        assert self.state is not None
        StepEditorRecorder.opened.append(self)

    def set_original_step_for_change_detection(self) -> None:
        pass

    def connect_orchestrator_config_signal(self, signal) -> None:
        del signal

    def connect_artifact_signals(self, **signals) -> None:
        del signals

    def show(self) -> None:
        pass

    def raise_(self) -> None:
        pass

    def activateWindow(self) -> None:
        pass


@pytest.fixture
def step_editors(monkeypatch):
    StepEditorRecorder.opened = []
    monkeypatch.setattr(
        "openhcs.pyqt_gui.widgets.pipeline_editor.DualEditorWindow",
        StepEditorRecorder,
    )
    return StepEditorRecorder.opened


def _names(steps) -> list[str]:
    return [step.name for step in steps]


def test_add_step_registers_state_before_opening_and_supports_edit(
    tmp_path, step_editors
) -> None:
    with editor_gui(tmp_path) as harness:
        scope_id = harness.scope_id
        add_button = harness.editor.buttons[AddPipelineStep.operation_id]
        assert add_button.isEnabled()

        add_button.click()

        (add_editor,) = step_editors
        assert add_editor.is_new is True
        assert harness.session.pipeline_steps(scope_id) == []
        assert (
            PipelineObjectStateBinding.editor_state_for_plate(scope_id).step_scope_ids
            == ()
        )
        add_editor.state.update_parameter("name", "Added Step")
        edited_step = add_editor.state.to_object()
        assert edited_step is not add_editor.step_data
        add_editor.on_save_callback(edited_step)
        harness.gui.settle()

        assert _names(harness.editor.displayed_steps) == ["Added Step"]
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Added Step"]
        history = ObjectStateRegistry.get_branch_history()
        assert history[-2].label.startswith("edit name")
        assert history[-1].label.startswith("add step Added Step")
        assert history[-1].parent_id == history[-2].id
        assert add_editor.scope_id in history[-2].all_states
        assert add_editor.scope_id in history[-1].all_states

        harness.select_rows(0)
        harness.editor.show_item_editor(harness.editor.displayed_steps[0])

        edit_editor = step_editors[1]
        assert edit_editor.is_new is False
        assert edit_editor.scope_id == add_editor.scope_id

        add_button.click()
        rejected_editor = step_editors[2]
        rejected_state = rejected_editor.state
        rejected_state.update_parameter("name", "Rejected Staged Edit")
        rejected_editor.rejected.emit()

        assert PipelineObjectStateBinding.editor_state_for_plate(
            scope_id
        ).step_scope_ids == (add_editor.scope_id,)
        assert ObjectStateRegistry.get_by_scope(rejected_editor.scope_id) is None
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Added Step"]
        discard_snapshot = ObjectStateRegistry.get_branch_history()[-1]
        assert discard_snapshot.label.startswith("discard staged step Step_2")
        assert rejected_editor.scope_id not in discard_snapshot.all_states

        assert ObjectStateRegistry.time_travel_back()
        assert (
            ObjectStateRegistry.get_by_scope(rejected_editor.scope_id) is rejected_state
        )
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Added Step"]
        assert ObjectStateRegistry.time_travel_forward()
        assert ObjectStateRegistry.get_by_scope(rejected_editor.scope_id) is None
        assert ObjectStateRegistry.get_by_scope(add_editor.scope_id) is add_editor.state
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Added Step"]

        history_head_id = ObjectStateRegistry.get_branch_history()[-1].id
        add_button.click()
        unedited_rejected_editor = step_editors[3]
        unedited_rejected_editor.rejected.emit()

        assert (
            ObjectStateRegistry.get_by_scope(unedited_rejected_editor.scope_id) is None
        )
        assert ObjectStateRegistry.get_branch_history()[-1].id == history_head_id
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Added Step"]


def test_add_step_history_preserves_the_open_step_across_edit_rewind_and_forward(
    tmp_path, step_editors
) -> None:
    """Accepted Add owns a snapshot before later field edits can be rewound."""

    with editor_gui(tmp_path) as harness:
        scope_id = harness.scope_id
        unrelated_state = ObjectState(
            FunctionStep(name="Existing History"),
            scope_id="other-plate::functionstep_0",
        )
        ObjectStateRegistry.register(unrelated_state, _skip_snapshot=True)
        unrelated_state.update_parameter("name", "Existing History Edited")

        harness.editor.buttons[AddPipelineStep.operation_id].click()
        (add_editor,) = step_editors
        add_editor.on_save_callback(add_editor.step_data)

        history = ObjectStateRegistry.get_branch_history()
        add_snapshot = history[-1]
        assert add_snapshot.label.startswith("add step Step_1")
        assert add_editor.scope_id in add_snapshot.all_states
        assert add_snapshot.parent_id == history[-2].id
        assert add_editor.scope_id not in history[-2].all_states

        add_editor.state.update_parameter("name", "Edited Step")
        edit_snapshot = ObjectStateRegistry.get_branch_history()[-1]
        assert edit_snapshot.label.startswith("edit name")
        assert edit_snapshot.parent_id == add_snapshot.id

        assert ObjectStateRegistry.time_travel_back()
        assert ObjectStateRegistry.get_by_scope(add_editor.scope_id) is add_editor.state
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Step_1"]
        assert ObjectStateRegistry.time_travel_back()
        assert ObjectStateRegistry.get_by_scope(add_editor.scope_id) is None
        assert harness.session.pipeline_steps(scope_id) == []
        assert ObjectStateRegistry.time_travel_forward()
        assert ObjectStateRegistry.get_by_scope(add_editor.scope_id) is add_editor.state
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Step_1"]
        assert ObjectStateRegistry.time_travel_forward()
        assert _names(harness.session.pipeline_steps(scope_id)) == ["Edited Step"]
        harness.gui.settle()
        assert _names(harness.editor.displayed_steps) == ["Edited Step"]

        add_editor.state.update_parameter("name", "Editable After Rewind")
        assert _names(harness.session.pipeline_steps(scope_id)) == [
            "Editable After Rewind"
        ]


def test_step_well_filter_live_resolution_is_visible_in_the_row(tmp_path) -> None:
    """Inherited step well filters fan out into the visible row preview."""

    with editor_gui(tmp_path) as harness:
        harness.set_steps(
            [
                FunctionStep(
                    name="Threshold",
                    step_well_filter_config=LazyStepWellFilterConfig(),
                )
            ]
        )
        dataset_state = ObjectStateRegistry.get_by_scope(harness.scope_id)

        dataset_state.update_parameter("well_filter_config.well_filter", "A01")
        ObjectStateRegistry._notify_change()
        (step,) = harness.editor.displayed_steps
        styled_text, _ = harness.editor.format_item_for_display(step, step_index=0)

        preview_by_path = {
            segment.field_path: segment.text
            for segment in styled_text.layout.preview_segments
            if segment.field_path
        }
        assert preview_by_path["step_well_filter_config.well_filter"] == ":A01"


def test_a_pipeline_config_scope_is_not_a_current_orchestrator() -> None:
    """Rows can refresh against a PipelineConfig scope before any orchestrator."""

    with session_gui() as gui:
        ObjectStateRegistry.register(ObjectState(PipelineConfig(), scope_id="plate"))
        gui.session.select(("plate",))
        gui.settle()

        assert gui.pipeline_editor._get_current_orchestrator() is None
        assert gui.session.is_initialized("plate") is False
        gui.pipeline_editor.update_button_states()
        assert not gui.pipeline_editor.buttons[AddPipelineStep.operation_id].isEnabled()


def test_delete_and_edit_need_a_step_selection(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        harness.set_steps([FunctionStep(name="One")])
        buttons = harness.editor.buttons

        harness.select_rows()
        assert buttons[DeletePipelineSteps.operation_id].isEnabled() is False
        assert buttons[EditPipelineStep.operation_id].isEnabled() is False

        harness.select_rows(0)
        assert buttons[DeletePipelineSteps.operation_id].isEnabled() is True
        assert buttons[EditPipelineStep.operation_id].isEnabled() is True


def _compiled(scope_id: str) -> CompiledDataset:
    return CompiledDataset(
        compile_artifact_id="compile-1",
        steps=(),
        inspection=CompiledArtifactInspection(
            compile_artifact_id="compile-1", plate_id=scope_id, steps=()
        ),
    )


def test_debug_toolbar_follows_the_current_dataset_compilation(tmp_path) -> None:
    with editor_gui(tmp_path) as harness:
        toolbar = harness.editor.debug_toolbar
        assert toolbar.command_enabled(DebugCommandType.STEP) is False

        harness.session.set_compiled(harness.scope_id, _compiled(harness.scope_id))
        harness.gui.settle()
        assert toolbar.command_enabled(DebugCommandType.STEP) is True

        harness.session.set_compiled(harness.scope_id, None)
        harness.gui.settle()
        assert toolbar.command_enabled(DebugCommandType.STEP) is False

        harness.session.compiled[harness.scope_id] = _compiled(harness.scope_id)
        harness.session.set_dataset_state(harness.scope_id, OrchestratorState.COMPILED)
        harness.gui.settle()
        assert toolbar.command_enabled(DebugCommandType.STEP) is True


def test_pipeline_update_refreshes_existing_step_scope_state() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    original = FunctionStep(
        name="IdentifyPrimaryObjects",
        processing_config=LazyProcessingConfig(group_by=Microscopy.Channel),
    )
    PipelineObjectStateBinding.update_plate_steps(TEST_PLATE_SCOPE, [original])
    replacement = FunctionStep(
        name="IdentifyPrimaryObjects",
        processing_config=LazyProcessingConfig(group_by=Ungrouped),
    )
    replacement._scope_token = original._scope_token

    PipelineObjectStateBinding.update_plate_steps(TEST_PLATE_SCOPE, [replacement])

    resolved = PipelineObjectStateBinding.steps_for_plate(TEST_PLATE_SCOPE)
    assert resolved[0].processing_config.group_by is Ungrouped


def test_pipeline_update_transfers_existing_step_scope_token_for_reapply() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    PipelineObjectStateBinding.update_plate_steps(
        TEST_PLATE_SCOPE, [FunctionStep(name="CountCells")]
    )
    replacement = FunctionStep(name="CountCells")

    PipelineObjectStateBinding.update_plate_steps(TEST_PLATE_SCOPE, [replacement])

    pipeline_state = ObjectStateRegistry.get_by_scope(f"{TEST_PLATE_SCOPE}::pipeline")
    assert pipeline_state is not None
    assert pipeline_state.parameters["step_scope_ids"] == (
        f"{TEST_PLATE_SCOPE}::functionstep_0",
    )
    assert (
        ObjectStateRegistry.get_by_scope(f"{TEST_PLATE_SCOPE}::functionstep_1") is None
    )
    assert ScopeTokenService.object_token(replacement) == "functionstep_0"


def test_pipeline_update_unregisters_removed_step_scopes() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(TEST_PLATE_SCOPE)
    PipelineObjectStateBinding.update_plate_steps(
        TEST_PLATE_SCOPE, [FunctionStep(name="First"), FunctionStep(name="Second")]
    )

    PipelineObjectStateBinding.update_plate_steps(
        TEST_PLATE_SCOPE, [FunctionStep(name="First")]
    )

    assert (
        ObjectStateRegistry.get_by_scope(f"{TEST_PLATE_SCOPE}::functionstep_0")
        is not None
    )
    assert (
        ObjectStateRegistry.get_by_scope(f"{TEST_PLATE_SCOPE}::functionstep_1") is None
    )
