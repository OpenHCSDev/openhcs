"""The current dataset's pipeline, rendered as a Qt manager widget.

Steps live in the dataset's pipeline ObjectState (through the session). The
widget displays the step objects it last read from the session and re-reads
them on every pipeline event; every change goes through the session.
"""

import copy
import logging
import os
from dataclasses import dataclass
from functools import singledispatchmethod
from typing import Any, Callable, Optional, Tuple

from objectstate.object_state import ObjectStateRegistry
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtWidgets import QSplitter, QVBoxLayout
from pyqt_reactive.animation import WindowFlashOverlay
from pyqt_reactive.services.scope_token_service import ScopeTokenService
from pyqt_reactive.theming import ColorScheme
from pyqt_reactive.widgets.editors.simple_code_editor import SimpleCodeEditorService
from pyqt_reactive.widgets.shared.abstract_manager_widget import (
    AbstractManagerWidget,
    ListItemFormat,
)
from pyqt_reactive.widgets.shared.button_panel import ButtonPanel
from pyqt_reactive.widgets.shared.list_item_delegate import (
    LEADING_MARKER_ROLE_OFFSET,
    ListItemLeadingMarker,
)
from pyqt_reactive.widgets.shared.manager_action_controller import CodeEditorPayload
from pyqt_reactive.widgets.shared.manager_item_hooks import (
    AttributeItemIdProjection,
    ManagerItemHooks,
)
from pyqt_reactive.widgets.shared.manager_selection_controller import (
    ItemSelectionPayloadProjection,
)
from pyqt_reactive.widgets.shared.manager_state_binding import ManagerStateBinding
from pyqt_reactive.widgets.shared.manager_ui_scaffold import (
    create_manager_header,
    create_manager_list_widget,
)
from pyqt_reactive.widgets.shared.scope_visual_config import ListItemType
from typing_extensions import override

import openhcs.serialization.pycodify_formatters  # noqa: F401
from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentTarget
from openhcs.agent.ui_bridge_identities import (
    PipelineDebugSessionStateSurfaceIdentityDeclaration,
    PipelineEditorStateSurfaceIdentityDeclaration,
    PipelineEditorWidgetIdentity,
)
from openhcs.authoring.session.dataset_document import authored_pipeline_config
from openhcs.authoring.session.events import (
    AvailabilityChanged,
    DatasetStateChanged,
    ExecutionStateChanged,
    PipelineChanged,
    PipelineImported,
    SelectionChanged,
    SessionEvent,
)
from openhcs.authoring.session.operations.pipelines import (
    AddPipelineStep,
    EditPipelineStep,
    ShowPipelineCode,
)
from openhcs.authoring.session.pipelines import PipelineObjectStateBinding
from openhcs.authoring.session.session import Session
from openhcs.authoring.session.views import PipelineStepsView
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, ProcessingConfig
from openhcs.core.debug import DebugCursor
from openhcs.core.debug_session_projection import DebugSessionProjectionContext
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentCodec
from openhcs.core.progress.debug_projection import DebugRuntimeProjection
from openhcs.core.source_binding_context import SourceBindingContext
from openhcs.core.source_bindings import (
    SourceBindingsConfig,
    source_bindings_defaults_to_base,
)
from openhcs.core.steps.function_step import FunctionSpec, FunctionStep
from openhcs.pyqt_gui.services.embedded_code_documents import (
    EmbeddedCodeDocumentRegistrationABC,
)
from openhcs.pyqt_gui.services.ui_bridge_contracts import (
    UiOwnedStateSurfaceDeclaration,
    state_surface_declaration_for_identity,
)
from openhcs.pyqt_gui.session_rendering import (
    GuiRenderer,
    OperationPresenter,
    QtSessionEventRelay,
    SessionOperationButtons,
)
from openhcs.pyqt_gui.widgets.debug_toolbar import DebugToolbarWidget
from openhcs.pyqt_gui.widgets.shared.openhcs_manager_mixins import (
    OpenHCSSingleRowActionManagerMixin,
)
from openhcs.pyqt_gui.widgets.shared.services.gui_event_bus_broadcast import (
    GuiEventBusBroadcaster,
)
from openhcs.pyqt_gui.widgets.shared.services.pipeline_editor_workflows import (
    PipelineEditorCodeWorkflow,
    PipelineEditorDebugWorkflow,
    PipelineEditorFunctionPresentation,
)
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity
from openhcs.core.axes import Axis, GroupingDeclaration

logger = logging.getLogger(__name__)


StepFunctionDeclaration = FunctionSpec | dict[str, FunctionSpec] | None
PIPELINE_EDITOR_EXTERNAL_EDITOR_ENV = "OPENHCS_USE_EXTERNAL_EDITOR"
SHOW_PIPELINE_DEBUG_TOOLBAR = False


class PipelineEditorEmbeddedCodeDocumentRegistration(
    EmbeddedCodeDocumentRegistrationABC
):
    """Register the embedded PipelineEditor code document with WindowManager."""

    scope_id = PipelineEditorWidgetIdentity.require_value()

    @classmethod
    def window_for_main_window(cls, main_window):
        return main_window.pipeline_editor_widget

    @classmethod
    def code_document_driver_for_window(cls, window):
        return window.code_document_driver()


def pipeline_editor_external_editor_enabled() -> bool:
    """Return the explicit environment policy for launching pipeline code edits."""
    if PIPELINE_EDITOR_EXTERNAL_EDITOR_ENV not in os.environ:
        return False
    return os.environ[PIPELINE_EDITOR_EXTERNAL_EDITOR_ENV].lower() in (
        "1",
        "true",
        "yes",
    )


@dataclass(frozen=True, slots=True)
class StepFunctionTooltipSection:
    """Tooltip section for a step's function declaration."""

    function_presentation: PipelineEditorFunctionPresentation

    def lines(self, func: StepFunctionDeclaration) -> list[str]:
        if not func:
            return ["Function: None"]
        if isinstance(func, list):
            return [self.list_line(func)]
        if callable(func):
            return [f"Function: {self.function_presentation.func_name(func)}"]
        if isinstance(func, dict):
            return [f"Function: Dictionary with {len(func)} routing keys"]
        return []

    def list_line(self, functions: list[Callable]) -> str:
        if len(functions) == 1:
            return f"Function: {self.function_presentation.func_name(functions[0])}"

        func_names = [
            self.function_presentation.func_name(func) for func in functions[:3]
        ]
        if len(functions) > 3:
            func_names.append(f"... +{len(functions) - 3} more")
        return f"Functions: {', '.join(func_names)}"


class StepProcessingTooltipSection:
    """Tooltip section for a step's processing config."""

    def lines(self, processing_config: ProcessingConfig) -> list[str]:
        return [
            self.variable_components_line(processing_config.variable_components),
            self.group_by_line(processing_config.group_by),
            self.input_source_line(processing_config.input_source),
        ]

    def variable_components_line(
        self,
        variable_components: list[type[Axis]],
    ) -> str:
        if not variable_components:
            return "Variable Components: None"
        comp_names = [component.name for component in variable_components]
        return f"Variable Components: [{', '.join(comp_names)}]"

    def group_by_line(self, group_by: type[GroupingDeclaration] | None) -> str:
        if group_by is None or not group_by.grouping_axes():
            return "Group By: None"
        return f"Group By: {group_by.name}"

    def input_source_line(self, input_source: InputSource) -> str:
        if not input_source:
            return "Input Source: None"
        return f"Input Source: {input_source.name}"


@dataclass(frozen=True, slots=True)
class StepTooltipBuilder:
    """Build the detailed tooltip for one pipeline step."""

    function_section: StepFunctionTooltipSection
    processing_section: StepProcessingTooltipSection = StepProcessingTooltipSection()

    @classmethod
    def for_function_presentation(
        cls,
        function_presentation: PipelineEditorFunctionPresentation,
    ) -> "StepTooltipBuilder":
        return cls(
            function_section=StepFunctionTooltipSection(function_presentation),
        )

    def build(self, step: FunctionStep) -> str:
        tooltip_lines = [f"Step: {step.name}"]
        tooltip_lines.extend(self.function_section.lines(step.func))
        tooltip_lines.extend(self.processing_section.lines(step.processing_config))

        return "\n".join(tooltip_lines)


class PipelineEditorWidget(
    SessionOperationButtons,
    OpenHCSSingleRowActionManagerMixin,
    AbstractManagerWidget,
):
    """Build and edit the ordered processing steps for the current dataset.

    Add registered processing functions, edit their declaration-owned parameters,
    reorder or remove steps, and switch to Python code for whole-pipeline edits.
    A dataset must be selected and initialized before adding steps. Changes
    update the dataset's pipeline and require compilation before execution.
    """

    SESSION_VIEW = PipelineStepsView
    TITLE = PipelineEditorWidgetIdentity.require_title()
    UI_STATE_SURFACE_DECLARATIONS = (
        UiOwnedStateSurfaceDeclaration(
            identity=PipelineEditorStateSurfaceIdentityDeclaration,
            title="Pipeline editor state",
            payload_schema="openhcs.ui.pipeline_editor_state.v1",
            related_action_ids=(
                *(operation.operation_id for operation in PipelineStepsView.operations),
                *state_surface_declaration_for_identity(
                    DebugToolbarWidget.UI_STATE_SURFACE_DECLARATIONS,
                    PipelineDebugSessionStateSurfaceIdentityDeclaration,
                ).related_action_ids,
            ),
        ),
    )
    UI_BRIDGE_WIDGET_IDENTITY = PipelineEditorWidgetIdentity
    HELP_KNOWLEDGE_TARGET = KnowledgeBaseDocumentTarget(
        document_id="openhcs_basic_interface",
        section_id="pipeline-editor",
    )
    ENABLE_STATUS_SCROLLING = True
    CODE_EDITOR_PAYLOAD = CodeEditorPayload(
        declaration_type=PipelineDocument,
        missing_error_message="Pipeline code must define 'pipeline_steps'.",
    )
    ITEM_NAME_SINGULAR = "step"
    ITEM_NAME_PLURAL = "steps"
    SELECTION_PAYLOAD_PROJECTION = ItemSelectionPayloadProjection()
    SELECTION_CLEARED_PAYLOAD = None
    SCOPE_ITEM_TYPE = ListItemType.STEP
    STATE_BINDING = ManagerStateBinding(
        items_attr="displayed_steps",
        selection_attr="selected_step",
        selection_signal_attr="step_selected",
    )
    ITEM_HOOKS = ManagerItemHooks(
        id_projection=AttributeItemIdProjection("_scope_token"),
        preserve_selection_pred=lambda self: bool(self.displayed_steps),
    )
    LIST_ITEM_FORMAT = ListItemFormat(
        first_line=("func",),
        formatters={},
        append_signature_diff_fields=False,
    )

    step_selected = pyqtSignal(object)
    status_message = pyqtSignal(str)

    def __init__(
        self,
        service_adapter,
        session: Session,
        color_scheme: Optional[ColorScheme] = None,
        parent=None,
    ):
        self.session = session
        self.displayed_steps: list[FunctionStep] = []
        """The step objects on screen, as last read from the session."""
        self.selected_step = ""
        self._clipboard_steps: list[FunctionStep] = []
        self.debug_toolbar: DebugToolbarWidget | None = None
        self.debug_inspector_window: Any | None = None
        super().__init__(service_adapter, color_scheme, parent=parent)
        self.code_execution_workflow = PipelineEditorCodeWorkflow(self)
        self.function_presentation = PipelineEditorFunctionPresentation(self)
        self.step_tooltip_builder = StepTooltipBuilder.for_function_presentation(
            self.function_presentation
        )
        self.debug_workflow = PipelineEditorDebugWorkflow(self)
        self.LIST_ITEM_FORMAT = ListItemFormat(
            first_line=self.LIST_ITEM_FORMAT.first_line,
            preview_line=self.LIST_ITEM_FORMAT.preview_line,
            detail_line_field=self.LIST_ITEM_FORMAT.detail_line_field,
            formatters={"func": self.function_presentation.format_func_preview},
            append_signature_diff_fields=self.LIST_ITEM_FORMAT.append_signature_diff_fields,
        )
        self.show_debug_snapshot = self.debug_workflow.show_snapshot
        self._events = QtSessionEventRelay(session, parent=self)
        self._events.published.connect(
            lambda record: self.on_session_event(record.event)
        )
        self.setup_ui()
        self.setup_connections()
        self._load_current_steps()
        self.update_button_states()

    # -- session state, read through -----------------------------------------

    @property
    def current_plate(self) -> str:
        return self.session.current_scope_id

    def selection_scope_ids(self) -> tuple[str, ...]:
        return self.selected_step_scope_ids()

    def _load_current_steps(self) -> None:
        scope_id = self.current_plate
        self.displayed_steps = self.session.pipeline_steps(scope_id) if scope_id else []
        if scope_id:
            ScopeTokenService.seed_from_objects(scope_id, self.displayed_steps)

    # -- session events -------------------------------------------------------

    @singledispatchmethod
    def on_session_event(self, event: SessionEvent) -> None:
        del event

    @on_session_event.register
    def _(self, event: SelectionChanged) -> None:
        self._load_current_steps()
        self.clear_list_visual_state()
        self.update_item_list()
        WindowFlashOverlay.invalidate_cache_for_widget(self)
        self.update_button_states()

    @on_session_event.register
    def _(self, event: PipelineChanged) -> None:
        self._refresh_if_current(event.scope_id)

    @on_session_event.register
    def _(self, event: PipelineImported) -> None:
        self._refresh_if_current(event.scope_id)

    @on_session_event.register
    def _(self, event: DatasetStateChanged) -> None:
        if event.scope_id == self.current_plate:
            self.update_button_states()

    @on_session_event.register
    def _(self, event: AvailabilityChanged) -> None:
        self.update_button_states()

    @on_session_event.register
    def _(self, event: ExecutionStateChanged) -> None:
        self.update_button_states()

    def _refresh_if_current(self, scope_id: str) -> None:
        if scope_id != self.current_plate:
            return
        self._load_current_steps()
        self.update_item_list()
        self.update_button_states()
        GuiEventBusBroadcaster(self.event_bus).pipeline_changed(self.displayed_steps)

    # -- UI -------------------------------------------------------------------

    def setup_ui(self):
        """Create pipeline editor UI with a debug/test-mode toolbar."""

        header_parts = create_manager_header(
            title=self.TITLE,
            color_scheme=self.color_scheme,
            enable_status_scrolling=self.ENABLE_STATUS_SCROLLING,
        )
        self.manager_header = header_parts
        self.debug_toolbar = DebugToolbarWidget(self, color_scheme=self.color_scheme)
        self.debug_toolbar.setVisible(SHOW_PIPELINE_DEBUG_TOOLBAR)
        self.item_list = create_manager_list_widget(
            color_scheme=self.color_scheme,
            delegate_manager=self,
        )
        self.button_panel = ButtonPanel(
            button_configs=self.BUTTON_CONFIGS,
            on_action=self.handle_button_action,
            color_scheme=self.color_scheme,
            grid_columns=self.BUTTON_GRID_COLUMNS,
            parent=self,
        )
        self.buttons = self.button_panel.buttons
        self.context_help_button = self.install_context_help_button(
            title_layout=self.manager_header.title_layout,
            object_name="pipeline_editor_help_button",
        )

        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(2, 2, 2, 2)
        main_layout.setSpacing(2)
        main_layout.addWidget(header_parts.header)
        if SHOW_PIPELINE_DEBUG_TOOLBAR:
            main_layout.addWidget(self.debug_toolbar)

        splitter = QSplitter(Qt.Orientation.Vertical)
        splitter.addWidget(self.item_list)
        splitter.addWidget(self.button_panel)
        splitter.setSizes([1000, 1])
        splitter.setStretchFactor(0, 1)
        splitter.setStretchFactor(1, 0)
        main_layout.addWidget(splitter)

    def setup_connections(self):
        self.setup_manager_connections()
        self.debug_toolbar.runtime_inspection_requested.connect(
            self.debug_workflow.show_runtime_inspection
        )
        from PyQt6.QtGui import QKeySequence, QShortcut

        QShortcut(QKeySequence("Ctrl+C"), self, self._action_copy_steps)
        QShortcut(QKeySequence("Ctrl+V"), self, self._action_paste_steps)
        self.debug_toolbar.command_requested.connect(self.debug_workflow.handle_command)

    def update_button_states(self):
        super().update_button_states()
        if self.debug_toolbar is not None:
            self.debug_toolbar.set_debug_session_context(self.debug_session_context())

    # -- code document --------------------------------------------------------

    def code_document_title(self) -> str:
        return "Edit Pipeline"

    def code_document_writable(self) -> bool:
        return bool(self.current_plate)

    def code_document_source(self, clean: bool = True) -> str:
        """Render the current dataset's pipeline document."""

        scope_id = self.current_plate
        return PipelineDocumentCodec.render(
            PipelineDocumentCodec.from_values(
                pipeline_config=(
                    authored_pipeline_config(scope_id) if scope_id else PipelineConfig()
                ),
                pipeline_steps=self.session.pipeline_steps(scope_id) if scope_id else [],
            ),
            clean_mode=clean,
        )

    # -- display --------------------------------------------------------------

    def _numbered_step_display_name(
        self, step: FunctionStep, step_index: Optional[int]
    ) -> tuple[str, str]:
        step_name = step.name or "Unknown Step"
        if step.debug_pause:
            step_name = f"Pause | {step_name}"
        if step_index is None:
            return step_name, step_name
        return f"{step_index + 1}. {step_name}", step_name

    def format_item_for_display(
        self,
        step: FunctionStep,
        live_context_snapshot=None,
        step_index: Optional[int] = None,
    ) -> Tuple[str, str]:
        del live_context_snapshot
        display_name, step_name = self._numbered_step_display_name(step, step_index)
        item_format = self.LIST_ITEM_FORMAT
        if item_format is not None and step_index is not None:
            item_format = ListItemFormat(
                first_line=item_format.first_line,
                preview_line=item_format.preview_line,
                detail_line_field=item_format.detail_line_field,
                formatters={
                    **item_format.formatters,
                    "func": lambda func: self.function_presentation.format_func_preview(
                        func,
                        step_index=step_index,
                    ),
                },
                append_signature_diff_fields=item_format.append_signature_diff_fields,
            )
        styled = self._item_display_builder.build_from_format(
            item=step,
            item_name=display_name,
            item_format=item_format,
        )
        return styled, step_name

    def step_scope_id(self, step: FunctionStep) -> str:
        return self.session.step_scope_id(self.current_plate, step)

    def selected_step_scope_ids(self) -> tuple[str, ...]:
        if not self.current_plate:
            return ()
        return tuple(self.step_scope_id(step) for step in self.get_selected_items())

    def get_item_insert_index(self, item: FunctionStep, scope_key: str) -> Optional[int]:
        del item
        token = scope_key.rsplit("::", 1)[-1]
        parts = token.rsplit("_", 1)
        if len(parts) == 2 and parts[1].isdigit():
            return min(int(parts[1]), len(self.displayed_steps))
        return None

    def _handle_full_preview_refresh(self) -> None:
        self.update_item_list()

    @override
    def _get_item_scope_id(self, item: FunctionStep, index: int) -> str:
        del index
        return self.step_scope_id(item)

    @override
    def _format_item_content(self, item: FunctionStep, index: int, context: None) -> str:
        display_text, _ = self.format_item_for_display(item, context, step_index=index)
        return display_text

    @override
    def _get_list_item_tooltip(self, item: FunctionStep) -> str:
        return self.step_tooltip_builder.build(item)

    @override
    def _get_list_item_extra_data(
        self,
        item: FunctionStep,
        index: int,
    ) -> dict[int, bool | ListItemLeadingMarker | None]:
        cursor = self.debug_cursor()
        return {
            1: not item.enabled,
            LEADING_MARKER_ROLE_OFFSET: (
                ListItemLeadingMarker()
                if cursor is not None and cursor.step_index == index
                else None
            ),
        }

    def debug_cursor(self) -> DebugCursor | None:
        if not self.current_plate:
            return None
        displayed = self.session.displayed_debug_session(self.current_plate)
        return None if displayed is None else displayed.cursor

    @override
    def _get_list_placeholder(self) -> tuple[str, None] | None:
        if self._get_current_orchestrator() is None:
            return ("No dataset selected - select a dataset to view its pipeline", None)
        return None

    @override
    def prepare_list_update(self) -> None:
        if self.current_plate:
            ScopeTokenService.seed_from_objects(self.current_plate, self.displayed_steps)
        return None

    @override
    def _on_items_reordered(self, from_index: int, to_index: int) -> None:
        try:
            self.session.move_step(self.current_plate, from_index, to_index)
        except RuntimeError as exc:
            self.status_message.emit(str(exc))
            self.update_item_list()

    @override
    def _get_scope_for_item(self, item: FunctionStep) -> str:
        if not self.current_plate:
            return ""
        return self.step_scope_id(item)

    def closeEvent(self, event):
        ObjectStateRegistry.disconnect_listener(self._on_live_context_changed)
        self._events.close()
        super().closeEvent(event)

    def on_time_travel_complete(self, dirty_states, triggering_scope):
        del triggering_scope
        self._load_current_steps()
        self.update_item_list()
        self.update_button_states()
        if self.current_plate and any(
            scope_id
            == PipelineScopeIdentity.from_plate_scope(self.current_plate).scope_id
            for scope_id, _state in (dirty_states or ())
        ):
            GuiEventBusBroadcaster(self.event_bus).pipeline_changed(self.displayed_steps)

    # -- context for step editors ---------------------------------------------

    def _get_current_orchestrator(self) -> Optional[PipelineOrchestrator]:
        if not self.current_plate:
            return None
        candidate = ObjectStateRegistry.get_object(self.current_plate)
        return candidate if isinstance(candidate, PipelineOrchestrator) else None

    def current_source_binding_context(self) -> SourceBindingContext | None:
        orchestrator = self._get_current_orchestrator()
        if orchestrator is None:
            return None
        return orchestrator.source_binding_context(self.current_plate)

    def _current_source_bindings(self) -> SourceBindingsConfig | None:
        context = self.current_source_binding_context()
        if context is not None:
            return context.source_bindings
        orchestrator = self._get_current_orchestrator()
        if orchestrator is None:
            return None
        return source_bindings_defaults_to_base(
            orchestrator.pipeline_config.source_bindings_config
        )

    def debug_session_context(self) -> DebugSessionProjectionContext:
        if self.current_plate:
            return self.session.debug_context(self.current_plate)
        return DebugSessionProjectionContext(
            target=None,
            session=None,
            manager_execution_state=self.session.execution_state,
        )

    def debug_runtime_projection(self) -> DebugRuntimeProjection:
        return self.session.debug_runtime_projection

    def open_step_editor(
        self,
        step: FunctionStep,
        *,
        is_new: bool,
        on_save: Callable[[FunctionStep], None],
        step_index: int | None = None,
    ) -> DualEditorWindow:
        scope_id = self.current_plate
        plate_manager = self.service_adapter.main_window.plate_manager_widget
        editor = DualEditorWindow(
            step_data=step,
            is_new=is_new,
            on_save_callback=on_save,
            orchestrator=self._get_current_orchestrator(),
            parent=self,
            service_adapter=self.service_adapter,
            plate_scope=scope_id,
            source_bindings=self._current_source_bindings(),
            source_binding_context=self.current_source_binding_context(),
            function_invocation_badge_provider=(
                None
                if step_index is None
                else self.function_presentation.badge_provider(step, step_index=step_index)
            ),
            compiled_artifact_inspection_provider=self.session.compiled_inspection,
            before_mutation=(
                lambda: self.session.require_definition_mutation_allowed(scope_id)
            ),
            **({} if step_index is None else {"step_index": step_index}),
        )
        editor.set_original_step_for_change_detection()
        editor.connect_orchestrator_config_signal(
            plate_manager.orchestrator_config_changed
        )
        editor.connect_artifact_signals(
            compiled_artifact_signal=plate_manager.compiled_artifact_inspection_changed,
            runtime_artifact_signal=plate_manager.runtime_artifact_available,
            debug_snapshot_signal=plate_manager.debug_snapshot_available,
        )
        editor.show()
        editor.raise_()
        editor.activateWindow()
        return editor

    @override
    def action_add(self) -> None:
        self.handle_button_action(AddPipelineStep.operation_id)

    @override
    def show_item_editor(self, item: FunctionStep) -> None:
        del item
        self.handle_button_action(EditPipelineStep.operation_id)

    # -- clipboard ------------------------------------------------------------

    def _action_copy_steps(self):
        selected = self.get_selected_items()
        if not selected:
            self.status_message.emit("No steps selected to copy")
            return
        self._clipboard_steps = [copy.deepcopy(step) for step in selected]
        self.status_message.emit(
            f"Copied {len(selected)} step(s): {', '.join(step.name for step in selected)}"
        )

    def _action_paste_steps(self):
        if not self._clipboard_steps:
            self.status_message.emit("Clipboard is empty")
            return
        if not self.current_plate:
            self.status_message.emit("No dataset selected")
            return
        selected_rows = [index.row() for index in self.item_list.selectedIndexes()]
        insert_after = max(selected_rows) if selected_rows else len(self.displayed_steps) - 1
        pasted = [copy.deepcopy(step) for step in self._clipboard_steps]
        self.session.insert_steps(self.current_plate, insert_after + 1, pasted)
        self.status_message.emit(
            f"Pasted {len(pasted)} step(s) after position {insert_after + 1}"
        )


# ---------------------------------------------------------------------------
# How the desktop GUI presents the pipeline's renderer operations
# ---------------------------------------------------------------------------


class AddPipelineStepPresenter(OperationPresenter):
    operation = AddPipelineStep

    def present(self, renderer: GuiRenderer, request) -> None:
        editor_widget = renderer.pipeline_editor
        session = editor_widget.session
        scope_id = request.scope_id
        new_step = FunctionStep(
            func=[],
            name=f"Step_{len(session.pipeline_steps(scope_id)) + 1}",
        )
        # The step editor needs a registered step scope while it is open; the
        # pipeline gains the step only when the editor saves.
        ObjectStateRegistry.ensure_baseline_snapshot()
        staged_scope_id = PipelineObjectStateBinding.stage_step(scope_id, new_step)
        committed = False

        def save(edited_step: FunctionStep) -> None:
            nonlocal committed
            if committed:
                session.pipeline_changed(scope_id)
                return
            session.add_step(scope_id, new_step, edited_step, staged_scope_id)
            committed = True

        def discard() -> None:
            if committed:
                return
            history = ObjectStateRegistry.get_branch_history()
            snapshotted = bool(history and staged_scope_id in history[-1].all_states)
            PipelineObjectStateBinding.discard_staged_step(scope_id, staged_scope_id)
            if snapshotted:
                ObjectStateRegistry.record_snapshot(
                    f"discard staged step {new_step.name}",
                    staged_scope_id,
                )

        editor = editor_widget.open_step_editor(new_step, is_new=True, on_save=save)
        editor.rejected.connect(discard)


class EditPipelineStepPresenter(OperationPresenter):
    operation = EditPipelineStep

    def present(self, renderer: GuiRenderer, request) -> None:
        editor_widget = renderer.pipeline_editor
        session = editor_widget.session
        scope_id = request.scope_id
        steps = editor_widget.displayed_steps
        index, step = next(
            (index, step)
            for index, step in enumerate(steps)
            if editor_widget.step_scope_id(step) in request.step_scope_ids
        )
        editor_widget.open_step_editor(
            step,
            is_new=False,
            step_index=index,
            on_save=lambda edited: session.replace_step(scope_id, step, edited),
        )


class ShowPipelineCodePresenter(OperationPresenter):
    operation = ShowPipelineCode

    def present(self, renderer: GuiRenderer, request) -> None:
        del request
        editor_widget = renderer.pipeline_editor
        SimpleCodeEditorService(editor_widget).edit_code(
            initial_content=editor_widget.code_document_source(clean=True),
            title=editor_widget.code_document_title(),
            callback=editor_widget._handle_edited_code,
            use_external=pipeline_editor_external_editor_enabled(),
            declaration_type=PipelineDocument,
            code_data={"clean_mode": True},
        )
