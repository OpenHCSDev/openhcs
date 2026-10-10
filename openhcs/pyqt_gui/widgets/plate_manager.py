"""The session's dataset list, rendered as a Qt manager widget.

The widget holds no session state: rows, selection, pending work, compiled
artifacts and execution state are read from the :class:`Session`; buttons are
the :class:`DatasetListView` operations; changes arrive as session events.
"""

from __future__ import annotations

import logging
import os
from dataclasses import fields, replace
from functools import singledispatchmethod
from pathlib import Path
from typing import TYPE_CHECKING, Optional, Tuple

from objectstate import DataclassFieldAccess
from objectstate.object_state import ObjectState, ObjectStateRegistry
from PyQt6.QtCore import pyqtSignal
from pyqt_reactive.theming import ColorScheme
from pyqt_reactive.widgets.editors.simple_code_editor import SimpleCodeEditorService
from pyqt_reactive.widgets.shared.abstract_manager_widget import (
    AbstractManagerWidget,
    ListItemFormat,
)
from pyqt_reactive.widgets.shared.manager_item_hooks import (
    AttributeItemIdProjection,
    ManagerItemHooks,
)
from pyqt_reactive.widgets.shared.manager_selection_controller import (
    ItemIdSelectionPayloadProjection,
)
from pyqt_reactive.widgets.shared.manager_state_binding import ManagerStateBinding
from pyqt_reactive.widgets.shared.scope_visual_config import ListItemType
from typing_extensions import override

from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentTarget
from openhcs.agent.dto.session import DatasetRootsRequest
from openhcs.agent.ui_bridge_identities import (
    PlateManagerLiveMeasurementsStateSurfaceIdentityDeclaration,
    PlateManagerStateSurfaceIdentityDeclaration,
    PlateManagerWidgetIdentity,
)
from openhcs.authoring.session.dataset_document import (
    DatasetDocument,
    DatasetDocumentScope,
    render_dataset_document,
)
from openhcs.authoring.session.datasets import DatasetRow
from openhcs.authoring.session.events import (
    AvailabilityChanged,
    CompilationFailed,
    CompiledStateChanged,
    DatasetConfigChanged,
    DatasetsChanged,
    DatasetStateChanged,
    DebugSnapshotAvailable,
    ErrorReported,
    ExecutionStateChanged,
    GlobalConfigChanged,
    InitializationFailed,
    LiveMeasurementAvailable,
    LogsCleared,
    PipelineChanged,
    RuntimeArtifactAvailable,
    RuntimeProjectionChanged,
    SelectionChanged,
    SessionEvent,
    StatusReported,
)
from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    EditDatasetConfig,
    ShowDatasetCode,
    ShowDatasetImages,
    ShowLiveResults,
)
from openhcs.authoring.session.session import Session
from openhcs.authoring.session.views import (
    DatasetActivity,
    DatasetListView,
    output_relations,
)
from openhcs.core.config import PipelineConfig
from openhcs.core.orchestrator.orchestrator import OrchestratorState
from openhcs.core.path_cache import PathCacheKey
from openhcs.core.selection import SelectedAllSelectionMode
from openhcs.pyqt_gui.services.ui_bridge_contracts import (
    UiOwnedStateSurfaceDeclaration,
)
from openhcs.pyqt_gui.session_rendering import (
    GuiRenderer,
    OperationPresenter,
    QtSessionEventRelay,
    RequestPrompter,
    SessionOperationButtons,
)
from openhcs.pyqt_gui.widgets.shared.openhcs_manager_mixins import (
    OpenHCSSingleRowActionManagerMixin,
)
from openhcs.pyqt_gui.widgets.shared.services.gui_event_bus_broadcast import (
    GuiEventBusBroadcaster,
)
from openhcs.pyqt_gui.widgets.shared.services.plate_manager_workflows import (
    PlateManagerCodeWorkflow,
)
from openhcs.pyqt_gui.windows.config_window import ConfigWindow
from openhcs.pyqt_gui.windows.live_measurements_window import LiveMeasurementsWindow
from openhcs.pyqt_gui.windows.plate_viewer_window import PlateViewerWindow

if TYPE_CHECKING:
    from openhcs.pyqt_gui.config import UIConfig

logger = logging.getLogger(__name__)


def external_editor_enabled() -> bool:
    """Return the explicit environment policy for launching the code editor."""
    variable_name = "OPENHCS_USE_EXTERNAL_EDITOR"
    if variable_name not in os.environ:
        return False
    return os.environ[variable_name].lower() in ("1", "true", "yes")


class PlateManagerWidget(
    SessionOperationButtons,
    OpenHCSSingleRowActionManagerMixin,
    AbstractManagerWidget,
):
    """Manage datasets through initialization, compilation, and execution.

    Add a dataset directory, edit its configuration, initialize source metadata,
    compile its pipeline, then run it. Results opens live measurement snapshots;
    Viewer opens dataset images and metadata.
    """

    SESSION_VIEW = DatasetListView
    TITLE = PlateManagerWidgetIdentity.require_title()
    UI_STATE_SURFACE_DECLARATIONS = (
        UiOwnedStateSurfaceDeclaration(
            identity=PlateManagerStateSurfaceIdentityDeclaration,
            title="Plate manager state",
            payload_schema="openhcs.ui.plate_manager_state.v1",
            related_action_ids=tuple(
                operation.operation_id for operation in DatasetListView.operations
            ),
        ),
        UiOwnedStateSurfaceDeclaration(
            identity=PlateManagerLiveMeasurementsStateSurfaceIdentityDeclaration,
            title="Live measurement results",
            payload_schema="openhcs.ui.live_measurements_state.v1",
            related_action_ids=(ShowLiveResults.operation_id,),
        ),
    )
    UI_BRIDGE_WIDGET_IDENTITY = PlateManagerWidgetIdentity
    HELP_KNOWLEDGE_TARGET = KnowledgeBaseDocumentTarget(
        document_id="openhcs_basic_interface",
        section_id="plate-manager",
    )
    ENABLE_STATUS_SCROLLING = True
    ITEM_NAME_SINGULAR = "dataset"
    ITEM_NAME_PLURAL = "datasets"
    SELECTION_PAYLOAD_PROJECTION = ItemIdSelectionPayloadProjection()
    SELECTION_CLEARED_PAYLOAD = ""
    SCOPE_ITEM_TYPE = ListItemType.ORCHESTRATOR
    STATE_BINDING = ManagerStateBinding(
        items_attr="plates",
        selection_attr="selected_plate_path",
        selection_signal_attr="plate_selected",
    )
    ITEM_HOOKS = ManagerItemHooks(
        id_projection=AttributeItemIdProjection("scope_id"),
        preserve_selection_pred=lambda self: bool(self.plates),
    )
    LIST_ITEM_FORMAT = ListItemFormat(
        first_line=(),
        preview_line=("num_workers",),
        detail_line_field="path",
    )

    # Qt projections of session events, for other GUI components.
    plate_selected = pyqtSignal(str)
    status_message = pyqtSignal(str)
    orchestrator_config_changed = pyqtSignal(str, object)
    compiled_artifact_inspection_changed = pyqtSignal(str, object)
    runtime_progress_projection_changed = pyqtSignal(object)
    debug_snapshot_available = pyqtSignal(object)
    runtime_artifact_available = pyqtSignal(object)
    clear_subprocess_logs = pyqtSignal()

    def __init__(
        self,
        service_adapter,
        session: Session,
        color_scheme: Optional[ColorScheme] = None,
        gui_config: "UIConfig | None" = None,
        parent=None,
    ):
        if gui_config is None:
            raise TypeError("PlateManagerWidget requires the resolved UIConfig")
        self._ui_config = gui_config
        self.session = session
        self.live_measurements_window: LiveMeasurementsWindow | None = None
        super().__init__(service_adapter, color_scheme, parent=parent)
        self.code_execution_workflow = PlateManagerCodeWorkflow(session)
        self._events = QtSessionEventRelay(session, parent=self)
        self._events.published.connect(
            lambda record: self.on_session_event(record.event)
        )
        self.setup_ui()
        self.setup_manager_connections()
        self.update_button_states()

    # -- configuration --------------------------------------------------------

    def set_ui_config(self, config: "UIConfig") -> None:
        self._ui_config = config
        self.session.set_transport_config(config.zmq)
        self.session.progress.set_interval(config.progress.update_interval_ms / 1000)

    def setup_ui(self) -> None:
        super().setup_ui()
        self.context_help_button = self.install_context_help_button(
            title_layout=self.manager_header.title_layout,
            object_name="plate_manager_help_button",
        )

    def cleanup(self) -> None:
        self._events.close()
        self._time_travel_binding.disconnect()
        self._list_visual_state.dispose()

    # -- session state, read through -----------------------------------------

    @property
    def plates(self) -> list[DatasetRow]:
        return self.session.dataset_rows()

    @property
    def selected_plate_path(self) -> str:
        return self.session.current_scope_id

    @selected_plate_path.setter
    def selected_plate_path(self, scope_id: str) -> None:
        selected = self.selection_scope_ids()
        self.session.select(selected or ((scope_id,) if scope_id else ()))

    def selection_scope_ids(self) -> tuple[str, ...]:
        return tuple(row.scope_id for row in self.get_selected_items())

    # -- session events -------------------------------------------------------

    @singledispatchmethod
    def on_session_event(self, event: SessionEvent) -> None:
        del event

    @on_session_event.register
    def _(self, event: DatasetsChanged) -> None:
        self.update_item_list()

    @on_session_event.register
    def _(self, event: DatasetStateChanged) -> None:
        self.update_item_list()

    @on_session_event.register
    def _(self, event: PipelineChanged) -> None:
        self.update_item_list()

    @on_session_event.register
    def _(self, event: AvailabilityChanged) -> None:
        self.update_button_states()

    @on_session_event.register
    def _(self, event: ExecutionStateChanged) -> None:
        self.update_button_states()

    @on_session_event.register
    def _(self, event: StatusReported) -> None:
        self.status_message.emit(event.text)

    @on_session_event.register
    def _(self, event: ErrorReported) -> None:
        self.service_adapter.show_error_dialog(event.text)

    @on_session_event.register
    def _(self, event: InitializationFailed) -> None:
        self.service_adapter.show_error_dialog(event.message)

    @on_session_event.register
    def _(self, event: CompilationFailed) -> None:
        self.service_adapter.show_error_dialog(event.message)

    @on_session_event.register
    def _(self, event: SelectionChanged) -> None:
        self._post_update_list()
        self.plate_selected.emit(event.current_scope_id)

    @on_session_event.register
    def _(self, event: DatasetConfigChanged) -> None:
        self.orchestrator_config_changed.emit(event.scope_id, event.effective_config)

    @on_session_event.register
    def _(self, event: CompiledStateChanged) -> None:
        inspection = None if event.compiled is None else event.compiled.inspection
        self.compiled_artifact_inspection_changed.emit(event.scope_id, inspection)

    @on_session_event.register
    def _(self, event: RuntimeProjectionChanged) -> None:
        self.runtime_progress_projection_changed.emit(event.projection)

    @on_session_event.register
    def _(self, event: DebugSnapshotAvailable) -> None:
        self.debug_snapshot_available.emit(event.notification)

    @on_session_event.register
    def _(self, event: RuntimeArtifactAvailable) -> None:
        self.runtime_artifact_available.emit(event.notification)

    @on_session_event.register
    def _(self, event: LiveMeasurementAvailable) -> None:
        if self.live_measurements_window is not None:
            self.live_measurements_window.set_orchestrator(
                self.results_orchestrator(event.notification.event.plate_id)
            )
            self.live_measurements_window.refresh(select_latest=True)

    @on_session_event.register
    def _(self, event: LogsCleared) -> None:
        self.clear_subprocess_logs.emit()
        if self.live_measurements_window is not None:
            self.live_measurements_window.refresh()

    @on_session_event.register
    def _(self, event: GlobalConfigChanged) -> None:
        self.service_adapter.set_global_config(event.config)
        GuiEventBusBroadcaster(self.event_bus).config_changed(event.config)

    # -- list rendering -------------------------------------------------------

    def on_time_travel_complete(self, dirty_states, triggering_scope):
        del dirty_states, triggering_scope
        self.update_item_list()
        self.update_button_states()

    def format_item_for_display(
        self, item: DatasetRow, live_ctx=None
    ) -> Tuple[str, str]:
        del live_ctx
        return (self._format_item_content(item, 0, None), item.scope_id)

    @override
    def _format_item_content(self, item: DatasetRow, index: int, context: None):
        del index, context
        return self.build_item_display_from_format(
            item=item,
            item_name=item.name,
            status_prefix=DatasetActivity(self.session, item.scope_id).status_prefix,
            detail_line=item.scope_id,
        )

    @override
    def _get_list_item_tooltip(self, item: DatasetRow) -> str:
        orchestrator = ObjectStateRegistry.get_object(item.scope_id)
        return f"Status: {orchestrator.state.value}" if orchestrator else ""

    @override
    def _get_item_scope_id(self, item: DatasetRow, index: int) -> Optional[str]:
        del index
        return item.scope_id

    @override
    def _get_scope_for_item(self, item: DatasetRow) -> str:
        return item.scope_id

    @override
    def _post_update_list(self) -> None:
        if not self.plates:
            return
        if self.selected_plate_path:
            from pyqt_reactive.widgets.mixins import restore_selection_by_id

            restore_selection_by_id(self.item_list, self.selected_plate_path)
            return
        self.item_list.setCurrentRow(0)

    @override
    def _handle_items_reordered(self, from_index: int, to_index: int) -> None:
        self.session.reorder_dataset(from_index, to_index)

    def _get_current_orchestrator(self):
        return ObjectStateRegistry.get_object(self.selected_plate_path)

    def action_add(self) -> None:
        self.handle_button_action(AddDatasets.operation_id)

    @override
    def show_item_editor(self, item: DatasetRow) -> None:
        del item
        self.handle_button_action(EditDatasetConfig.operation_id)

    # -- code document --------------------------------------------------------

    def dataset_document(
        self,
        selection_mode: SelectedAllSelectionMode = SelectedAllSelectionMode.SELECTED,
    ) -> DatasetDocument:
        """The dataset code document: the selection, else every dataset."""

        every = tuple(row.scope_id for row in self.plates)
        scope_ids = (
            every
            if selection_mode is SelectedAllSelectionMode.ALL
            else self.selection_scope_ids() or every
        )
        return render_dataset_document(
            self.session, scope_ids, selection_mode=selection_mode
        )

    def code_document_operations(self, scope: DatasetDocumentScope):
        """Manager operations whose code application is bounded by ``scope``."""

        return replace(
            self._action_operations(),
            apply_code_namespace=PlateManagerCodeWorkflow(
                self.session, scope
            ).apply_namespace,
        )

    def show_dataset_code(self, selection_mode: SelectedAllSelectionMode) -> None:
        """Open the dataset code document in the code editor."""

        document = self.dataset_document(selection_mode)
        operations = self.code_document_operations(
            DatasetDocumentScope.from_carrier(document)
        )
        SimpleCodeEditorService(self).edit_code(
            initial_content=document.source,
            title="Edit Orchestrator Configuration",
            callback=lambda edited: self._action_controller.apply_edited_code(
                operations, edited
            ),
            use_external=external_editor_enabled(),
            declaration_type=type(document.payload),
            code_data={"clean_mode": document.clean_mode},
        )

    def results_orchestrator(self, scope_id: str | None):
        """The orchestrator whose results a dataset's live measurements show."""

        if scope_id is None:
            selected = self.selection_scope_ids()
            if not selected:
                return None
            scope_id = selected[0]
        relation = output_relations(
            tuple(self.plates), self.session.global_config.path_planning_config
        ).get(scope_id)
        if relation is not None and relation.source_scope_id is not None:
            return ObjectStateRegistry.get_object(relation.source_scope_id)
        orchestrator = ObjectStateRegistry.get_object(scope_id)
        if (
            orchestrator is not None
            and orchestrator.state is not OrchestratorState.CREATED
        ):
            return orchestrator
        return None


# ---------------------------------------------------------------------------
# How the desktop GUI presents the dataset list's renderer operations
# ---------------------------------------------------------------------------


class AddDatasetsPrompter(RequestPrompter):
    operation = AddDatasets

    def prompt(self, renderer: GuiRenderer) -> DatasetRootsRequest | None:
        manager = renderer.plate_manager
        selected = manager.service_adapter.show_cached_directory_dialog(
            cache_key=PathCacheKey.PLATE_IMPORT,
            title="Select Dataset Directory",
            fallback_path=Path.home(),
            allow_multiple=True,
        )
        if not selected:
            manager.status_message.emit("Dataset selection cancelled")
            return None
        return DatasetRootsRequest(roots=tuple(str(path) for path in selected))


class EditDatasetConfigPresenter(OperationPresenter):
    operation = EditDatasetConfig

    def present(self, renderer: GuiRenderer, request) -> None:
        manager = renderer.plate_manager
        session = manager.session
        states = [
            ObjectStateRegistry.get_by_scope(scope_id) for scope_id in request.scope_ids
        ]
        representative = states[0]
        if not isinstance(representative.saved_object, PipelineConfig):
            raise TypeError("Dataset ObjectState does not delegate to PipelineConfig.")

        def save(new_config: PipelineConfig) -> None:
            for config_field in fields(new_config):
                logger.debug(
                    "CONFIG SAVE %s = %s",
                    config_field.name,
                    DataclassFieldAccess.raw_value(new_config, config_field.name),
                )
            session.apply_dataset_configs(
                {scope_id: new_config for scope_id in request.scope_ids}
            )

        open_config_window(manager, representative, save, tuple(request.scope_ids))


def open_config_window(
    manager: PlateManagerWidget,
    state: ObjectState,
    on_save,
    mutation_scope_ids: tuple[str, ...],
) -> None:
    from openhcs.pyqt_gui.windows.config_window import (
        ConfigSaveParticipant,
        ConfigWindowTabSpec,
    )

    def require_mutation_allowed() -> None:
        for scope_id in mutation_scope_ids:
            manager.session.require_definition_mutation_allowed(scope_id)

    window = ConfigWindow(
        tabs=(
            ConfigWindowTabSpec(
                state=state,
                save_participant=ConfigSaveParticipant(apply=on_save, rollback=on_save),
                before_mutation=require_mutation_allowed,
            ),
        ),
        color_scheme=manager.color_scheme,
        parent=manager,
        scope_id=state.scope_id,
    )
    window.show()
    window.raise_()
    window.activateWindow()


class ShowDatasetCodePresenter(OperationPresenter):
    operation = ShowDatasetCode

    def present(self, renderer: GuiRenderer, request) -> None:
        del request
        renderer.plate_manager.show_dataset_code(SelectedAllSelectionMode.SELECTED)


class ShowLiveResultsPresenter(OperationPresenter):
    operation = ShowLiveResults

    def present(self, renderer: GuiRenderer, request) -> None:
        del request
        manager = renderer.plate_manager
        orchestrator = manager.results_orchestrator(None)
        if manager.live_measurements_window is None:
            manager.live_measurements_window = LiveMeasurementsWindow(
                manager.session.live_measurements,
                orchestrator=orchestrator,
                color_scheme=manager.color_scheme,
                zmq_config=manager._ui_config.zmq,
                progress_config=manager._ui_config.progress,
                parent=manager,
            )
        else:
            manager.live_measurements_window.set_orchestrator(orchestrator)
        window = manager.live_measurements_window
        window.refresh(select_latest=True)
        window.show()
        window.raise_()
        window.activateWindow()


class ShowDatasetImagesPresenter(OperationPresenter):
    operation = ShowDatasetImages

    def present(self, renderer: GuiRenderer, request) -> None:
        manager = renderer.plate_manager
        for scope_id in request.scope_ids:
            PlateViewerWindow(
                orchestrator=ObjectStateRegistry.get_object(scope_id),
                zmq_config=manager._ui_config.zmq,
                progress_config=manager._ui_config.progress,
                parent=manager,
            ).show()
