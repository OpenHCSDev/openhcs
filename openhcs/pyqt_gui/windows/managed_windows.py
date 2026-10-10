"""
Managed window implementations using WindowManager.show_or_focus().

Each window is created by a factory function passed to WindowManager.
"""

from pathlib import Path

from PyQt6.QtWidgets import QDialog, QVBoxLayout

from openhcs.agent.ui_bridge_identities import (
    ImageBrowserWindowIdentity,
    LogViewerWindowIdentity,
    PipelineEditorWidgetIdentity,
    PlateManagerWidgetIdentity,
    ZmqServerManagerWindowIdentity,
)


class _ManagedChildCleanupWindow(QDialog):
    """Close a composed child through its declared cleanup lifecycle."""

    def closeEvent(self, event) -> None:
        self.widget.cleanup()
        super().closeEvent(event)


class PlateManagerWindow(_ManagedChildCleanupWindow):
    """A floating dataset list rendering the main window's session."""

    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle(PlateManagerWidgetIdentity.require_title())
        self.setModal(False)
        self.resize(600, 400)

        from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

        layout = QVBoxLayout(self)
        self.widget = PlateManagerWidget(
            self.service_adapter,
            main_window.session,
            self.service_adapter.get_current_color_scheme(),
            gui_config=self.service_adapter.widget_gui_config,
        )
        layout.addWidget(self.widget)


class PipelineEditorWindow(QDialog):
    """A floating pipeline editor rendering the main window's session."""

    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle(PipelineEditorWidgetIdentity.require_title())
        self.setModal(False)
        self.resize(800, 600)

        from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget

        layout = QVBoxLayout(self)
        self.widget = PipelineEditorWidget(
            self.service_adapter,
            main_window.session,
            self.service_adapter.get_current_color_scheme(),
        )
        layout.addWidget(self.widget)


class ImageBrowserWindow(_ManagedChildCleanupWindow):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle(ImageBrowserWindowIdentity.require_title())
        self.setModal(False)
        self.resize(900, 600)

        from openhcs.pyqt_gui.widgets.image_browser import ImageBrowserWidget

        layout = QVBoxLayout(self)
        self.widget = ImageBrowserWidget(
            orchestrator=None,
            color_scheme=self.service_adapter.get_current_color_scheme(),
            zmq_config=self.main_window.runtime_context.ui_config.zmq,
            progress_config=self.main_window.runtime_context.ui_config.progress,
        )
        self.main_window.ui_config_changed.connect(
            lambda config: self.widget.set_ui_config(
                zmq_config=config.zmq,
                progress_config=config.progress,
            )
        )
        layout.addWidget(self.widget)
        self._setup_connections()

    def _setup_connections(self):
        from pyqt_reactive.services.window_manager import WindowManager

        plate_widgets = [self.main_window.embedded_widgets.require_plate_manager()]

        plate_window = WindowManager._scoped_windows.get(
            PlateManagerWidgetIdentity.require_value()
        )
        if plate_window is not None and plate_window.widget not in plate_widgets:
            plate_widgets.append(plate_window.widget)

        for plate_widget in plate_widgets:
            plate_widget.plate_selected.connect(
                lambda _plate_path=None, plate_widget=plate_widget: (
                    self._update_orchestrator(plate_widget)
                )
            )
            self._update_orchestrator(plate_widget)

    def _update_orchestrator(self, plate_widget):
        orchestrator = plate_widget._get_current_orchestrator()
        if orchestrator:
            self.widget.set_orchestrator(orchestrator)


class LogViewerWindowWrapper(_ManagedChildCleanupWindow):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle(LogViewerWindowIdentity.require_title())
        self.setModal(False)
        self.resize(900, 700)

        from pyqt_reactive.widgets.log_viewer import LogViewerWindow

        layout = QVBoxLayout(self)
        self.widget = LogViewerWindow(
            self.main_window.file_manager, self.service_adapter
        )
        layout.addWidget(self.widget)

    def switch_to_log(self, log_file_path: Path) -> None:
        """Display one server log through the wrapped log-viewer owner."""
        self.widget.switch_to_log(log_file_path)


class ZMQServerManagerWindow(_ManagedChildCleanupWindow):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle(ZmqServerManagerWindowIdentity.require_title())
        self.setModal(False)
        self.resize(600, 400)

        from PyQt6.QtWidgets import QVBoxLayout

        from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
            ZMQServerManagerWidget,
        )

        layout = QVBoxLayout(self)

        self.widget = ZMQServerManagerWidget(
            ports_to_scan=self.main_window.zmq_server_manager_ports_to_scan(),
            title="ZMQ Servers (Execution + UI Bridge + Napari + Fiji)",
            color_scheme=self.service_adapter.get_current_color_scheme(),
            config=self.main_window.runtime_context.ui_config.zmq,
            progress_config=self.main_window.runtime_context.ui_config.progress,
        )
        self.main_window.ui_config_changed.connect(self._apply_ui_config)
        layout.addWidget(self.widget)
        self.widget.log_file_opened.connect(self.main_window._open_log_file_in_viewer)

    def _apply_ui_config(self, config) -> None:
        self.widget.set_zmq_config(
            config.zmq,
            self.main_window.zmq_server_manager_ports_to_scan(),
        )
        self.widget.set_progress_config(config.progress)
