from types import SimpleNamespace

from PyQt6.QtWidgets import QApplication, QProgressBar

from openhcs.core.progress.projection import (
    ExecutionRuntimeProjection,
    PlateRuntimeIdentity,
    PlateRuntimeProjection,
    PlateRuntimeState,
)
from openhcs.pyqt_gui.services.main_window_workflows import MainWindowLifecycleWorkflow


def test_init_signals_and_completion_preserve_running_progress():
    app = QApplication.instance() or QApplication([])
    projection = ExecutionRuntimeProjection()
    plate = PlateRuntimeProjection(
        identity=PlateRuntimeIdentity(plate_id="/running", execution_id="owned-run"),
        state=PlateRuntimeState.EXECUTING,
        percent=43,
        axis_progress=(),
        latest_timestamp=1,
    )
    projection.add_plate(plate)
    projection.mark_latest(plate.identity)
    projection.recalculate_summary()
    manager = SimpleNamespace(
        runtime_progress_projection=projection, plate_init_pending={"/other"}
    )
    bar = QProgressBar()
    workflow = MainWindowLifecycleWorkflow(
        main_window=None,
        embedded_widgets=SimpleNamespace(require_plate_manager=lambda: manager),
        floating_windows={},
        status_progress_bar=bar,
        ui_bridge_lifecycle=None,
        ui_services=None,
    )
    try:
        workflow.progress_started(1)
        assert not bar.isHidden()
        assert bar.maximum() == 100
        assert bar.value() == round(projection.overall_percent)
        workflow.progress_updated(1)
        manager.plate_init_pending.clear()
        workflow.progress_finished()
        assert not bar.isHidden()
        assert bar.maximum() == 100
        assert bar.value() == round(projection.overall_percent)
        manager.runtime_progress_projection = ExecutionRuntimeProjection()
        manager.plate_init_pending.add("/other")
        workflow.refresh_progress()
        assert not bar.isHidden()
        assert bar.maximum() == 0
        manager.plate_init_pending.clear()
        workflow.progress_finished()
        assert bar.isHidden()
    finally:
        bar.close()
        app.processEvents()
