"""PyQt debug/test-mode toolbar built on declared debug actions."""

from __future__ import annotations

from PyQt6.QtCore import pyqtSignal
from PyQt6.QtWidgets import QLabel, QPushButton, QVBoxLayout, QWidget

from openhcs.agent.ui_bridge_identities import (
    PipelineDebugSessionStateSurfaceIdentityDeclaration,
    PipelineDebugToolbarWidgetIdentity,
)
from openhcs.core.debug import DebugCommandType
from openhcs.core.execution_state import ManagerExecutionState
from formbridge.bridge.contracts import UiOwnedStateSurfaceDeclaration
from openhcs.pyqt_gui.widgets.shared.services.debug_session_projection import (
    DebugActionRenderModel,
    DebugSessionPanelText,
    DebugToolbarActionProjector,
)
from openhcs.core.debug_session_projection import DebugSessionProjectionContext
from openhcs.pyqt_gui.widgets.shared.services.pipeline_debug_actions import (
    DebugToolbarPlacement,
    InspectRuntimeValuesAction,
    PipelineDebugActionDeclarationBase,
    PrimaryPanel,
)
from pyqt_reactive.widgets.shared.button_panel import ButtonPanel
from pyqt_reactive.theming import ColorScheme


class DebugToolbarWidget(QWidget):
    """Compact command surface for bounded debug/test-mode runs."""

    UI_STATE_SURFACE_DECLARATIONS = (
        UiOwnedStateSurfaceDeclaration(
            identity=PipelineDebugSessionStateSurfaceIdentityDeclaration,
            title="Pipeline debug session state",
            payload_schema="openhcs.ui.pipeline_debug_session_state.v1",
            related_action_ids=tuple(
                declaration.action_id()
                for declaration in DebugToolbarActionProjector.declarations()
            ),
        ),
    )
    UI_BRIDGE_WIDGET_IDENTITY = PipelineDebugToolbarWidgetIdentity

    command_requested = pyqtSignal(object)
    runtime_inspection_requested = pyqtSignal()

    def __init__(
        self,
        parent: QWidget | None = None,
        *,
        color_scheme: ColorScheme | None = None,
    ) -> None:
        super().__init__(parent)
        self.phase_label = QLabel("No Plate")
        self.cursor_label = QLabel("Select a plate to debug.")
        self._buttons_by_id: dict[str, QPushButton] = {}
        self._action_models: dict[str, DebugActionRenderModel] = {}

        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(2)

        initial_context = DebugSessionProjectionContext(
            target=None,
            session=None,
            manager_execution_state=ManagerExecutionState.IDLE,
        )
        initial_models = DebugToolbarActionProjector.render_models(initial_context)
        layout.addWidget(self.phase_label)
        layout.addWidget(self.cursor_label)
        self.panels: dict[type[DebugToolbarPlacement], ButtonPanel] = {
            placement: self._build_panel(initial_models, placement, color_scheme)
            for placement in DebugToolbarPlacement.panels()
        }
        self.button_panel = self.panels[PrimaryPanel]
        for panel in self.panels.values():
            layout.addWidget(panel)
        self.set_action_models(initial_models)

    def _build_panel(
        self,
        initial_models: tuple[DebugActionRenderModel, ...],
        placement: type[DebugToolbarPlacement],
        color_scheme: ColorScheme | None,
    ) -> ButtonPanel:
        models = tuple(
            model for model in initial_models if model.placement is placement
        )
        panel = ButtonPanel(
            button_configs=[
                (model.label, model.action_id, model.tooltip) for model in models
            ],
            on_action=self.emit_debug_command,
            color_scheme=color_scheme,
            parent=self,
        )
        for model in models:
            button = panel.buttons[model.action_id]
            self._buttons_by_id[model.action_id] = button
        return panel

    @property
    def buttons(self) -> dict[type[DebugCommandType], QPushButton]:
        """Return command-keyed access derived from the action-id button store."""

        return {
            command: self._buttons_by_id[command.name]
            for command in DebugCommandType.__registry__.values()
            if command.name in self._buttons_by_id
        }

    @property
    def runtime_inspection_button(self) -> QPushButton | None:
        """Return the declared runtime-inspection button when rendered."""

        return self._buttons_by_id.get(InspectRuntimeValuesAction.action_id())

    def emit_debug_command(self, action_id: str) -> None:
        PipelineDebugActionDeclarationBase.for_action_id(action_id).emit_from(self)

    def set_debug_session_context(self, context: DebugSessionProjectionContext) -> None:
        """Project toolbar controls from the current PipelineEditor debug context."""

        panel_text = DebugSessionPanelText.from_context(context)
        self.phase_label.setText(panel_text.title)
        self.cursor_label.setText(panel_text.detail)
        self.set_action_models(DebugToolbarActionProjector.render_models(context))

    def set_action_models(
        self,
        models: tuple[DebugActionRenderModel, ...],
    ) -> None:
        """Apply projected debug action models to the rendered toolbar."""

        self._action_models = {model.action_id: model for model in models}
        for model in models:
            tooltip = self._tooltip_for_model(model)
            button = self._buttons_by_id[model.action_id]
            button.setText(model.label)
            button.setToolTip(tooltip)
            button.setEnabled(model.enabled)

    def command_enabled(self, command_type: type[DebugCommandType]) -> bool:
        model = self._action_models.get(command_type.name)
        if model is None:
            raise ValueError(
                f"Debug command is not exposed by the toolbar: {command_type}"
            )
        return model.enabled

    @staticmethod
    def _tooltip_for_model(model: DebugActionRenderModel) -> str:
        if model.disabled_reason is None:
            return model.tooltip
        return f"{model.tooltip}\n\nDisabled: {model.disabled_reason.message}"


__all__ = ("DebugToolbarWidget",)
