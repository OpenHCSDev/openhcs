"""Workflow objects owned by the PyQt main window."""

from __future__ import annotations

import logging
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Callable

from PyQt6.QtWidgets import (
    QApplication,
    QDialog,
    QFileDialog,
    QMessageBox,
    QProgressBar,
    QWidget,
)
from pyqt_reactive.services.window_manager import WindowManager
from pyqt_reactive.widgets.shared.dock_layout import DockPanes

from openhcs.agent.ui_bridge_identities import (
    AboutOpenHCSWindowIdentity,
    ImageBrowserWindowIdentity,
    KnowledgeBaseWindowIdentity,
    LogViewerWindowIdentity,
    PipelineEditorWidgetIdentity,
    PlateManagerWidgetIdentity,
    UiStableWindowIdentityDeclaration,
    ZmqServerManagerWindowIdentity,
)
from openhcs.agent.dto.session import PipelineFileRequest
from openhcs.authoring.session.operations.pipelines import LoadPipelineFile
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.pipeline_import import PipelineImporter
from openhcs.core.progress.projection import ExecutionRuntimeProjection
from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId
from openhcs.pyqt_gui.services.window_config import (
    StartupWindowPresentation,
    WindowSpec,
)

if TYPE_CHECKING:
    from openhcs.pyqt_gui.config import AgentUiBridgeConfig
    from openhcs.pyqt_gui.services.service_adapter import PyQtServiceAdapter
    from openhcs.pyqt_gui.services.ui_bridge_server import UiBridgeControlServer
    from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget
    from openhcs.runtime.zmq_config import OpenHCSZMQConfig

logger = logging.getLogger(__name__)


@dataclass(frozen=True, slots=True)
class MainWindowSpecDefinition:
    """Declarative record for one WindowManager-managed window."""

    identity: type[UiStableWindowIdentityDeclaration]
    window_class: type[QDialog]
    initialize_on_startup: bool = False
    startup_presentation: StartupWindowPresentation = (
        StartupWindowPresentation.KEEP_VISIBLE
    )

    def build(self) -> WindowSpec:
        return WindowSpec(
            window_id=self.identity.require_value(),
            title=self.identity.require_title(),
            window_class=self.window_class,
            initialize_on_startup=self.initialize_on_startup,
            startup_presentation=self.startup_presentation,
        )


def build_main_window_specs() -> dict[str, WindowSpec]:
    """Build all WindowManager-managed window specifications."""

    from openhcs.pyqt_gui.windows.about_window import AboutOpenHCSWindow
    from openhcs.pyqt_gui.windows.help_window import HelpWindow
    from openhcs.pyqt_gui.windows.managed_windows import (
        ImageBrowserWindow,
        LogViewerWindowWrapper,
        PipelineEditorWindow,
        PlateManagerWindow,
        ZMQServerManagerWindow,
    )

    definitions = (
        MainWindowSpecDefinition(
            PlateManagerWidgetIdentity,
            PlateManagerWindow,
            True,
        ),
        MainWindowSpecDefinition(
            PipelineEditorWidgetIdentity,
            PipelineEditorWindow,
        ),
        MainWindowSpecDefinition(
            ImageBrowserWindowIdentity,
            ImageBrowserWindow,
        ),
        MainWindowSpecDefinition(
            LogViewerWindowIdentity,
            LogViewerWindowWrapper,
            True,
            StartupWindowPresentation.HIDE,
        ),
        MainWindowSpecDefinition(
            ZmqServerManagerWindowIdentity,
            ZMQServerManagerWindow,
        ),
        MainWindowSpecDefinition(
            KnowledgeBaseWindowIdentity,
            HelpWindow,
        ),
        MainWindowSpecDefinition(
            AboutOpenHCSWindowIdentity,
            AboutOpenHCSWindow,
        ),
    )
    specs = tuple(definition.build() for definition in definitions)
    return {spec.window_id: spec for spec in specs}


class MainWindowEmbeddedWidgets(DockPanes):
    """The OpenHCS main window's panes, addressed by their window ids."""

    __slots__ = ()

    def require_plate_manager(self) -> QWidget:
        return self.require_pane(OpenHCSUiWindowId.plate_manager).widget

    def require_pipeline_editor(self) -> QWidget:
        return self.require_pane(OpenHCSUiWindowId.pipeline_editor).widget

    def require_zmq_manager(self) -> QWidget:
        return self.require_pane(OpenHCSUiWindowId.zmq_server_manager).widget

    def require_system_monitor(self) -> QWidget:
        return self.require_pane(OpenHCSUiWindowId.system_monitor).widget

    def show_plate_manager(self) -> None:
        self.require_pane(OpenHCSUiWindowId.plate_manager).show()

    def show_pipeline_editor(self) -> None:
        self.require_pane(OpenHCSUiWindowId.pipeline_editor).show()

    def show_zmq_manager(self) -> None:
        self.require_pane(OpenHCSUiWindowId.zmq_server_manager).show()

    def show_system_monitor(self) -> None:
        self.require_pane(OpenHCSUiWindowId.system_monitor).show()


@dataclass(frozen=True, slots=True)
class MainWindowPipelineActions:
    """File-menu actions for the embedded pipeline editor."""

    main_window: QWidget
    pipeline_editor: PipelineEditorWidget

    def new_pipeline(self) -> None:
        session = self.pipeline_editor.session
        if session.current_scope_id:
            session.set_pipeline(session.current_scope_id, [])

    def open_pipeline(self, selected_path: Path | None = None) -> None:
        session = self.pipeline_editor.session
        file_path = selected_path
        if file_path is None:
            selected, _ = QFileDialog.getOpenFileName(
                self.main_window,
                "Open Pipeline",
                "",
                PipelineImporter.file_filter(),
            )
            if not selected:
                return
            file_path = Path(selected)
        result = session.invoke(
            LoadPipelineFile,
            PipelineFileRequest(scope_id=session.current_scope_id, path=str(file_path)),
        )
        if result.errors:
            QMessageBox.critical(
                self.main_window, "Open Pipeline", result.errors[0].message
            )

    def save_pipeline(self, selected_path: Path | None = None) -> None:
        file_path = selected_path
        if file_path is None:
            selected, _ = QFileDialog.getSaveFileName(
                self.main_window,
                "Save Pipeline",
                "pipeline.py",
                "OpenHCS Pipelines (*.py)",
            )
            if not selected:
                return
            file_path = Path(selected).with_suffix(".py")
        try:
            file_path.write_text(
                self.pipeline_editor.code_document_source(clean=True), encoding="utf-8"
            )
        except Exception as error:
            logger.exception("Failed to save pipeline %s", file_path)
            QMessageBox.critical(self.main_window, "Save Pipeline", str(error))


@dataclass(frozen=True, slots=True)
class MainWindowLifecycleWorkflow:
    """Main-window lifecycle behavior that spans multiple child widgets."""

    main_window: QWidget
    embedded_widgets: MainWindowEmbeddedWidgets
    floating_windows: dict[str, QWidget]
    status_progress_bar: QProgressBar
    ui_bridge_lifecycle: "MainWindowUiBridgeLifecycle"
    ui_services: PyQtServiceAdapter

    def propagate_config(self, new_config: GlobalPipelineConfig) -> None:
        self.main_window.session.adopt_global_config(new_config)

    def refresh_progress(self) -> None:
        """Reproject the existing work owners after local initialization changes."""
        self.runtime_progress_changed(self.main_window.session.runtime_projection)

    def runtime_progress_changed(
        self,
        projection: ExecutionRuntimeProjection,
    ) -> None:
        """Render the progress registry's current projection without retaining it."""

        initializing = bool(self.main_window.session.init_pending)
        self.status_progress_bar.setRange(
            0, 100 if projection.has_active_work or not initializing else 0
        )
        self.status_progress_bar.setValue(round(projection.overall_percent))
        self.status_progress_bar.setVisible(projection.has_active_work or initializing)

    def close(self) -> None:
        failures: list[Exception] = []

        def attempt(description: str, operation: Callable[[], object]) -> None:
            try:
                operation()
            except Exception as exc:
                logger.warning("Error %s: %s", description, exc)
                failures.append(exc)

        attempt("stopping UI bridge server", self.ui_bridge_lifecycle.close)
        attempt(
            "stopping system monitor",
            lambda: self.embedded_widgets.require_system_monitor().stop_monitoring(),
        )
        attempt(
            "cleaning up plate manager",
            lambda: self.embedded_widgets.require_plate_manager().cleanup(),
        )
        attempt("closing the session", self.main_window.session.close)
        attempt(
            "cleaning up ZMQ server manager",
            lambda: self.embedded_widgets.require_zmq_manager().cleanup(),
        )

        try:
            open_scopes = WindowManager.get_open_scopes()
        except Exception as exc:
            logger.warning("Error enumerating managed windows: %s", exc)
            failures.append(exc)
            open_scopes = ()
        for scope_id in open_scopes:
            attempt(
                f"closing managed window {scope_id}",
                lambda scope_id=scope_id: WindowManager.close_window(scope_id),
            )

        for window_name, window in list(self.floating_windows.items()):

            def close_floating_window(window=window) -> None:
                try:
                    window.close()
                finally:
                    window.deleteLater()

            attempt(f"cleaning up window {window_name}", close_floating_window)

        self.floating_windows.clear()

        try:
            top_level_widgets = QApplication.topLevelWidgets()
        except Exception as exc:
            logger.warning("Error enumerating top-level widgets: %s", exc)
            failures.append(exc)
            top_level_widgets = ()
        for widget in top_level_widgets:
            if widget is self.main_window:
                continue
            attempt("closing top-level widget", widget.close)

        # Fence shared dispatch only after every UI producer has been retired.
        attempt("closing asynchronous UI services", self.ui_services.close)

        if failures:
            raise ExceptionGroup("Main-window cleanup failed", failures)


@dataclass(slots=True)
class MainWindowUiBridgeLifecycle:
    """Mutable owner for the optional main-window UI bridge server."""

    server: "UiBridgeControlServer | None" = None

    @property
    def bound_port(self) -> int | None:
        if self.server is None or not self.server.is_running:
            return None
        return self.server.binding.connection.port

    def reconcile(
        self,
        *,
        config: "AgentUiBridgeConfig",
        transport_config: "OpenHCSZMQConfig",
        create_server: Callable[
            ["AgentUiBridgeConfig", "OpenHCSZMQConfig"],
            "UiBridgeControlServer",
        ],
    ):
        """Make the running server exactly match the requested configuration.

        A failed replacement rebuilds the previous declaration before
        propagating the error, so configuration Save cannot strand the bridge.
        """

        current = self.server
        if not config.enabled:
            self.close()
            return None
        if current is not None and current.matches_configuration(
            config, transport_config
        ):
            return current.binding

        if current is not None:
            current.stop()
            self.server = None
        candidate = None
        try:
            candidate = create_server(config, transport_config)
            binding = candidate.start()
        except Exception as replacement_error:
            if candidate is not None:
                try:
                    candidate.stop()
                except Exception as cleanup_error:
                    self.server = candidate
                    raise RuntimeError(
                        "UI bridge replacement failed and the candidate bridge "
                        "could not be stopped."
                    ) from ExceptionGroup(
                        "UI bridge replacement and candidate cleanup errors",
                        (replacement_error, cleanup_error),
                    )
            if current is not None:
                try:
                    rollback = create_server(
                        current.config,
                        current.transport_config,
                    )
                    rollback.start()
                except Exception as rollback_error:
                    raise RuntimeError(
                        "UI bridge replacement failed and the previous bridge "
                        "could not be restored."
                    ) from ExceptionGroup(
                        "UI bridge replacement and rollback errors",
                        (replacement_error, rollback_error),
                    )
                else:
                    self.server = rollback
            raise
        self.server = candidate
        return binding

    def close(self) -> None:
        if self.server is None:
            return
        self.server.stop()
        self.server = None
