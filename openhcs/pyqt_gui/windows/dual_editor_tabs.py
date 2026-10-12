"""The step editor's tabs. Each is one ``StepEditorTab`` declaration, in tab order."""

from __future__ import annotations

from functools import cache

from objectstate.context_manager import config_context
from objectstate.object_state import ObjectStateRegistry
from PyQt6.QtCore import Qt
from PyQt6.QtGui import QColor
from python_introspect import SignatureAnalyzer
from pyqt_reactive.widgets.function_list_editor import FunctionListEditorWidget
from pyqt_reactive.widgets.shared import ActionTabMaterialization

from openhcs.authoring.session.compilation import CompiledDataset
from openhcs.authoring.session.progress_notifications import (
    DebugSnapshotAvailableNotification,
    RuntimeArtifactAvailableNotification,
)
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.ui_tab_identities import DualEditorTab
from openhcs.pyqt_gui.widgets.artifact_plan_view import ArtifactPlanViewWidget
from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
from openhcs.pyqt_gui.windows.dual_editor_session import StepEditorTab


@cache
def _function_step_form_field_names() -> frozenset[str]:
    """Editable top-level FunctionStep fields, from the constructor signatures."""
    return frozenset(SignatureAnalyzer.analyze(AbstractStep.__init__)) | frozenset(
        SignatureAnalyzer.analyze(FunctionStep.__init__)
    )


def step_relative_form_path(param_name: str) -> tuple[str, ...]:
    """The step-relative path of a form parameter-change signal."""
    path_parts = tuple(part for part in param_name.split(".") if part)
    if len(path_parts) > 1 and path_parts[0] not in _function_step_form_field_names():
        return path_parts[1:]
    return path_parts


class StepSettingsTab(StepEditorTab):
    """The step's own parameters as a form."""

    label = DualEditorTab.STEP_SETTINGS.label

    def build(self) -> ActionTabMaterialization:
        edit = self.edit
        pipeline_config = edit.orchestrator.pipeline_config
        with config_context(pipeline_config), config_context(edit.step):
            self.editor = StepParameterEditorWidget(
                edit.step,
                service_adapter=None,
                color_scheme=self.window.color_scheme,
                pipeline_config=pipeline_config,
                scope_id=edit.scope_id,
                step_index=edit.list_position,
                scope_accent_color=self.window.get_scope_accent_color(),
                render_header=False,
                button_style="compact",
                source_bindings=edit.source_bindings,
                source_binding_context=edit.source_binding_context,
                before_mutation=edit.before_mutation,
            )
        self.editor.form_manager.parameter_changed.connect(self._on_form_parameter_changed)
        self._orchestrator_config_signals: list = []
        return ActionTabMaterialization(self.editor, self.editor.get_action_buttons())

    def form_managers(self):
        return (self.editor.form_manager,)

    def navigation_driver(self):
        return self.editor.window_navigation_driver()

    def code_document_driver(self):
        return self.editor.code_document_driver()

    def apply_scope_accent(self, accent_color: QColor) -> None:
        del accent_color
        tree_style = self.window.get_scope_tree_selection_stylesheet()
        tree = self.editor.hierarchy_tree
        if tree_style and tree:
            tree.setStyleSheet(f"{tree.styleSheet()}\n{tree_style}")
        self.editor.apply_scope_color_scheme(self.window._scope_color_scheme)

    def set_step_index(self, index: int) -> None:
        self.editor.step_index = index

    def follow_orchestrator_config(self, signal) -> None:
        """Re-resolve placeholders whenever this plate's pipeline config is replaced."""
        signal.connect(self._on_orchestrator_config_changed)
        self._orchestrator_config_signals.append(signal)

    def release(self) -> None:
        for signal in self._orchestrator_config_signals:
            signal.disconnect(self._on_orchestrator_config_changed)
        self._orchestrator_config_signals.clear()
        self.editor.tree_helper.cleanup_subscriptions()

    def _on_orchestrator_config_changed(self, plate_scope: str, _effective_config) -> None:
        if plate_scope == self.edit.plate_scope:
            self.editor.use_pipeline_config(self.edit.orchestrator.pipeline_config)

    def _on_form_parameter_changed(self, param_name: str, value) -> None:
        # A bare callable typed into the form's ``func`` field becomes a function pattern.
        if step_relative_form_path(param_name) == ("func",) and callable(value):
            self.edit.apply_function_pattern(value)


class FunctionPatternTab(StepEditorTab):
    """The step's function pattern as a list of function panes."""

    label = DualEditorTab.FUNCTION_PATTERN.label

    def build(self) -> ActionTabMaterialization:
        edit = self.edit
        self.editor = FunctionListEditorWidget(
            initial_functions=edit.step.func or [],
            context_identifier=edit.step.name,
            service_adapter=None,
            scope_id=edit.scope_id,
            render_header=False,
            button_style="compact",
            scope_index=edit.list_position,
            invocation_badge_provider=edit.function_invocation_badge_provider,
            before_mutation=edit.before_mutation,
        )
        self.editor.refresh_from_context()
        self.editor.apply_selected_pattern_key_from_state()
        self.editor.function_pattern_changed.connect(
            self._on_function_pattern_changed,
            type=Qt.ConnectionType.DirectConnection,
        )
        return ActionTabMaterialization(self.editor, self.editor.get_action_buttons())

    def navigation_driver(self):
        return self.editor.window_navigation_driver()

    def apply_scope_accent(self, accent_color: QColor) -> None:
        del accent_color
        self.editor.set_scope_color_scheme(self.window._scope_color_scheme)

    def write_pending_edits(self) -> None:
        self.edit.apply_function_pattern(self.editor.current_pattern)

    def refresh_from_state(self) -> None:
        self.editor.refresh_from_context()

    def set_step_index(self, index: int) -> None:
        self.editor.set_scope_index(index)

    def pipeline_step_replaced(self, step: FunctionStep) -> None:
        pattern = step.func
        if pattern:
            self.editor._initialize_pattern_data(pattern)
            self.editor._populate_function_list()

    def _on_function_pattern_changed(self) -> None:
        edit = self.edit
        pattern = edit.normalized_function_pattern(self.editor.current_pattern)
        if edit.function_pattern() == pattern:
            return
        with ObjectStateRegistry.atomic("edit func"):
            edit.apply_function_pattern(pattern)
        self.window.tab_edited_state(self)


class ArtifactsTab(StepEditorTab):
    """What the compiled plan and the last run produced for this step."""

    label = DualEditorTab.ARTIFACTS.label

    def build(self) -> ActionTabMaterialization:
        self.view = ArtifactPlanViewWidget(
            inspection=self.edit.compiled_inspection(),
            step_index=self.edit.list_position,
        )
        self._followed: list[tuple] = []
        return ActionTabMaterialization(self.view)

    def refresh_from_state(self) -> None:
        # An edited step no longer matches the compiled plan.
        self.view.set_inspection(None)

    def set_step_index(self, index: int) -> None:
        self.view.set_step_index(index)

    def pipeline_step_replaced(self, step: FunctionStep) -> None:
        del step
        self.view.set_inspection(None)

    def follow_artifact_signals(
        self,
        *,
        compiled_artifact_signal,
        runtime_artifact_signal,
        debug_snapshot_signal,
    ) -> None:
        """Show compile and runtime artifacts as the plate manager announces them."""
        for signal, slot in (
            (compiled_artifact_signal, self._on_compiled_artifact_state_changed),
            (runtime_artifact_signal, self._on_runtime_artifact_available),
            (debug_snapshot_signal, self._on_debug_snapshot_available),
        ):
            signal.connect(slot)
            self._followed.append((signal, slot))

    def release(self) -> None:
        for signal, slot in self._followed:
            signal.disconnect(slot)
        self._followed.clear()

    def _on_compiled_artifact_state_changed(
        self,
        plate_path: str,
        state: CompiledDataset | None,
    ) -> None:
        if plate_path != self.edit.plate_scope:
            return
        self.view.set_inspection(None if state is None else state.inspection)

    def _on_runtime_artifact_available(
        self,
        notification: RuntimeArtifactAvailableNotification,
    ) -> None:
        if notification.event.subject_id == self.edit.plate_scope:
            self.view.apply_runtime_notification(notification)

    def _on_debug_snapshot_available(
        self,
        notification: DebugSnapshotAvailableNotification,
    ) -> None:
        snapshot = notification.snapshot
        if notification.progress_event.subject_id == self.edit.plate_scope and snapshot is not None:
            self.view.apply_debug_snapshot(snapshot)
