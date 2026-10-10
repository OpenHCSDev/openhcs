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
    session = SimpleNamespace(runtime_projection=projection, init_pending={"/other"})
    bar = QProgressBar()
    workflow = MainWindowLifecycleWorkflow(
        main_window=SimpleNamespace(session=session),
        embedded_widgets=SimpleNamespace(),
        floating_windows={},
        status_progress_bar=bar,
        ui_bridge_lifecycle=None,
        ui_services=None,
    )
    try:
        # Initialization start, progress and completion each refresh the bar.
        workflow.refresh_progress()
        assert not bar.isHidden()
        assert bar.maximum() == 100
        assert bar.value() == round(projection.overall_percent)
        session.init_pending.clear()
        workflow.refresh_progress()
        assert not bar.isHidden()
        assert bar.maximum() == 100
        assert bar.value() == round(projection.overall_percent)
        session.runtime_projection = ExecutionRuntimeProjection()
        session.init_pending.add("/other")
        workflow.refresh_progress()
        assert not bar.isHidden()
        assert bar.maximum() == 0
        session.init_pending.clear()
        workflow.refresh_progress()
        assert bar.isHidden()
    finally:
        bar.close()
        app.processEvents()
