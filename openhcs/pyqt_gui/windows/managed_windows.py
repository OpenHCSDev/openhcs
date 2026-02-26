"""
Managed window implementations using WindowManager.show_or_focus().

Each window is created by a factory function passed to WindowManager.
"""

from PyQt6.QtWidgets import QDialog, QVBoxLayout


class PlateManagerWindow(QDialog):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle("Plate Manager")
        self.setModal(False)
        self.resize(600, 400)

        from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

        layout = QVBoxLayout(self)
        self.widget = PlateManagerWidget(
            self.service_adapter,
            self.service_adapter.get_current_color_scheme(),
        )
        layout.addWidget(self.widget)
        self._setup_connections()

    def _setup_connections(self):
        self.widget.global_config_changed.connect(
            lambda: self.main_window.on_config_changed(
                self.service_adapter.get_global_config()
            )
        )

        if hasattr(self.main_window, "status_bar"):
            self._setup_progress_signals()

        self._connect_to_pipeline_editor()

    def _setup_progress_signals(self):
        from PyQt6.QtWidgets import QProgressBar

        if not hasattr(self.main_window, "_status_progress_bar"):
            self.main_window._status_progress_bar = QProgressBar()
            self.main_window._status_progress_bar.setMaximumWidth(200)
            self.main_window._status_progress_bar.setVisible(False)
            self.main_window.status_bar.addPermanentWidget(
                self.main_window._status_progress_bar
            )

        self.widget.progress_started.connect(
            self.main_window._on_plate_progress_started
        )
        self.widget.progress_updated.connect(
            self.main_window._on_plate_progress_updated
        )
        self.widget.progress_finished.connect(
            self.main_window._on_plate_progress_finished
        )

    def _connect_to_pipeline_editor(self):
        from pyqt_reactive.services.window_manager import WindowManager

        pipeline_window = WindowManager._scoped_windows.get("pipeline_editor")
        if pipeline_window:
            from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget

            pipeline_widget = pipeline_window.widget
            self.widget.plate_selected.connect(pipeline_widget.set_current_plate)
            self.widget.orchestrator_config_changed.connect(
                pipeline_widget.on_orchestrator_config_changed
            )
            self.widget.set_pipeline_editor(pipeline_widget)
            pipeline_widget.plate_manager = self.widget


class PipelineEditorWindow(QDialog):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle("Pipeline Editor")
        self.setModal(False)
        self.resize(800, 600)

        from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget

        layout = QVBoxLayout(self)
        self.widget = PipelineEditorWidget(
            self.service_adapter,
            self.service_adapter.get_current_color_scheme(),
        )
        layout.addWidget(self.widget)
        self._setup_connections()

    def _setup_connections(self):
        from pyqt_reactive.services.window_manager import WindowManager

        plate_window = WindowManager._scoped_windows.get("plate_manager")
        if plate_window:
            plate_widget = plate_window.widget
            plate_widget.plate_selected.connect(self.widget.set_current_plate)
            plate_widget.orchestrator_config_changed.connect(
                self.widget.on_orchestrator_config_changed
            )
            self.widget.plate_manager = plate_widget
            plate_widget.set_pipeline_editor(self.widget)


class ImageBrowserWindow(QDialog):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle("Image Browser")
        self.setModal(False)
        self.resize(900, 600)

        from openhcs.pyqt_gui.widgets.image_browser import ImageBrowserWidget

        layout = QVBoxLayout(self)
        self.widget = ImageBrowserWidget(
            orchestrator=None,
            color_scheme=self.service_adapter.get_current_color_scheme(),
        )
        layout.addWidget(self.widget)
        self._setup_connections()

    def _setup_connections(self):
        from pyqt_reactive.services.window_manager import WindowManager

        plate_window = WindowManager._scoped_windows.get("plate_manager")
        if plate_window and hasattr(plate_window.widget, "plate_selected"):
            plate_widget = plate_window.widget
            plate_widget.plate_selected.connect(
                lambda: self._update_orchestrator(plate_widget)
            )
            self._update_orchestrator(plate_widget)

    def _update_orchestrator(self, plate_widget):
        orchestrator = plate_widget.get_selected_orchestrator()
        if orchestrator:
            self.widget.set_orchestrator(orchestrator)


class LogViewerWindowWrapper(QDialog):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle("Log Viewer")
        self.setModal(False)
        self.resize(900, 700)

        from pyqt_reactive.widgets.log_viewer import LogViewerWindow

        layout = QVBoxLayout(self)
        self.widget = LogViewerWindow(
            self.main_window.file_manager, self.service_adapter
        )
        layout.addWidget(self.widget)


class ZMQServerManagerWindow(QDialog):
    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setWindowTitle("ZMQ Server Manager")
        self.setModal(False)
        self.resize(600, 400)

        from PyQt6.QtWidgets import QVBoxLayout
        from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
            ZMQServerManagerWidget,
        )

        from openhcs.core.config import get_all_streaming_ports

        layout = QVBoxLayout(self)
        ports_to_scan = get_all_streaming_ports(num_ports_per_type=10)

        self.widget = ZMQServerManagerWidget(
            ports_to_scan=ports_to_scan,
            title="ZMQ Servers (Execution + Napari + Fiji)",
            style_generator=self.service_adapter.get_style_generator(),
        )
        layout.addWidget(self.widget)
        self.widget.log_file_opened.connect(self.main_window._open_log_file_in_viewer)
