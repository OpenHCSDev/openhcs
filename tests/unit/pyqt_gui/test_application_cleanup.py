"""Native Qt ownership after the application event loop has stopped."""

import os
from pathlib import Path
import subprocess
import sys

import openhcs


def test_cleanup_destroys_native_window_tree_after_event_loop_exit(tmp_path):
    """Keep Python references alive so GC cannot disguise pending Qt deletion."""
    environment = os.environ.copy()
    environment.update(
        OPENHCS_CPU_ONLY="true",
        QT_QPA_PLATFORM="offscreen",
        XDG_CACHE_HOME=str(tmp_path / "cache"),
        XDG_CONFIG_HOME=str(tmp_path / "config"),
        XDG_DATA_HOME=str(tmp_path / "data"),
    )
    process = subprocess.run(
        [
            sys.executable,
            "-X",
            "faulthandler",
            "-c",
            """
from PyQt6 import sip
from PyQt6.QtCore import QTimer
from PyQt6.QtWidgets import QWidget
from openhcs.core.config import GlobalPipelineConfig
from openhcs.pyqt_gui.app import OpenHCSPyQtApp
from openhcs.pyqt_gui.config import PyQtGuiRuntimeContext, UIConfig

application = OpenHCSPyQtApp(
    ["native-cleanup-regression"],
    runtime_context=PyQtGuiRuntimeContext(
        ui_config=UIConfig(check_for_updates_on_startup=False),
        pipeline_runtime=GlobalPipelineConfig(),
    ),
)
window = QWidget()
child = QWidget(window)
application.main_window = window
QTimer.singleShot(0, application.quit)
assert application.exec() == 0
application.cleanup()
assert application.main_window is None
assert sip.isdeleted(window), "cleanup left the native main window alive"
assert sip.isdeleted(child), "cleanup left native child widgets alive"
application.cleanup()
""",
        ],
        cwd=Path(openhcs.__file__).resolve().parent.parent,
        env=environment,
        capture_output=True,
        text=True,
        timeout=45,
    )
    assert process.returncode == 0, process.stdout + process.stderr
