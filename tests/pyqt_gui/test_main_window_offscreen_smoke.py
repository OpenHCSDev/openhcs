"""Offscreen smoke test: the desktop main window starts, toggles its panes and exits cleanly.

The test launches the real ``OpenHCSPyQtApp`` in a child process with isolated
home, config and cache directories and its own execution port. The child opens
the plate manager and the pipeline editor as their own windows through the pane
float button, closes each back into its dock, then closes the main window. Every process the run starts inherits a marker environment variable; once
the child has exited, no process carrying that marker may remain, so no viewer or
execution server outlives the window.
"""

from __future__ import annotations

import json
import os
import socket
import subprocess
import sys
import time
import uuid
from pathlib import Path

import psutil

PROJECT_ROOT = Path(__file__).resolve().parents[2]
MARKER_VARIABLE = "OPENHCS_OFFSCREEN_SMOKE_MARKER"
STARTUP_TIMEOUT_SECONDS = 240
EXIT_GRACE_SECONDS = 30


def _free_port_pair() -> int:
    while True:
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        if port + 1000 > 65535:
            continue
        with socket.socket() as control:
            try:
                control.bind(("127.0.0.1", port + 1000))
            except OSError:
                continue
        return port


def _processes_with_marker(marker: str) -> list[psutil.Process]:
    found = []
    for process in psutil.process_iter(["pid"]):
        if process.pid == os.getpid():
            continue
        try:
            if process.environ().get(MARKER_VARIABLE) == marker:
                found.append(process)
        except (psutil.AccessDenied, psutil.NoSuchProcess, psutil.ZombieProcess):
            continue
    return found


def _describe(processes: list[psutil.Process]) -> list[str]:
    described = []
    for process in processes:
        try:
            described.append(f"{process.pid}: {' '.join(process.cmdline())}")
        except (psutil.NoSuchProcess, psutil.ZombieProcess):
            continue
    return described


def test_main_window_opens_and_closes_panes_and_leaves_no_process(tmp_path) -> None:
    marker = uuid.uuid4().hex
    home = tmp_path / "home"
    home.mkdir()
    environment = {
        **os.environ,
        MARKER_VARIABLE: marker,
        "QT_QPA_PLATFORM": "offscreen",
        "HOME": str(home),
        "XDG_CONFIG_HOME": str(home / "config"),
        "XDG_CACHE_HOME": str(home / "cache"),
        "XDG_STATE_HOME": str(home / "state"),
        "XDG_DATA_HOME": os.environ.get("XDG_DATA_HOME", str(home / "data")),
        "PYTHONPATH": os.pathsep.join(
            filter(None, (str(PROJECT_ROOT), os.environ.get("PYTHONPATH")))
        ),
    }
    child = subprocess.Popen(
        [sys.executable, __file__, str(_free_port_pair())],
        cwd=PROJECT_ROOT,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        stdout, stderr = child.communicate(timeout=STARTUP_TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        child.kill()
        stdout, stderr = child.communicate()
    try:
        assert child.returncode == 0, stderr[-4000:]
        report = json.loads(stdout.strip().splitlines()[-1])
        assert report == {
            "plate_manager": [False, True, False, True],
            "pipeline_editor": [False, True, False, True],
        }

        deadline = time.monotonic() + EXIT_GRACE_SECONDS
        survivors = _processes_with_marker(marker)
        while survivors and time.monotonic() < deadline:
            time.sleep(0.5)
            survivors = _processes_with_marker(marker)
        assert _describe(survivors) == []
    finally:
        for process in _processes_with_marker(marker):
            try:
                process.kill()
            except psutil.NoSuchProcess:
                pass


def _run_main_window(port: int):
    from dataclasses import replace

    from PyQt6.QtCore import QTimer

    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.pyqt_gui.app import OpenHCSPyQtApp
    from openhcs.pyqt_gui.config import PyQtGuiRuntimeContext, get_default_ui_config
    from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId

    ui_config = get_default_ui_config()
    ui_config = replace(ui_config, zmq=replace(ui_config.zmq, default_port=port))
    app = OpenHCSPyQtApp(
        sys.argv[:1],
        runtime_context=PyQtGuiRuntimeContext(
            ui_config, pipeline_runtime=GlobalPipelineConfig()
        ),
    )
    report: dict[str, list[bool]] = {}
    failures: list[BaseException] = []
    steps = []

    def run_next_step() -> None:
        if failures or not steps:
            app.main_window.close()
            return
        try:
            steps.pop(0)()
        except BaseException as error:  # noqa: BLE001 - reported by exit code
            failures.append(error)
        QTimer.singleShot(300, run_next_step)

    def queue_pane_round_trip(name: str) -> None:
        pane = app.main_window.embedded_widgets.require_pane(
            getattr(OpenHCSUiWindowId, name)
        )

        def record() -> None:
            report.setdefault(name, []).append(
                pane.dock_widget.isFloating() and pane.dock_widget.isVisible()
            )

        # Docked, then opened as its own window, then closed back into the dock.
        steps.extend((record, pane.float_button.click, record))
        steps.extend((pane.float_button.click, record))
        steps.append(lambda: report[name].append(pane.dock_widget.isVisible()))

    def start_round_trips() -> None:
        queue_pane_round_trip("plate_manager")
        queue_pane_round_trip("pipeline_editor")
        run_next_step()

    def startup_failed(error: BaseException) -> None:
        failures.append(error)
        app.main_window.close()

    app.show_main_window(
        on_deferred_initialization_complete=lambda: QTimer.singleShot(
            500, start_round_trips
        ),
        on_deferred_initialization_failed=startup_failed,
    )
    exit_code = app.exec()
    if failures:
        raise failures[0]
    print(json.dumps(report), flush=True)
    return exit_code, app


if __name__ == "__main__":
    exit_code, app = _run_main_window(int(sys.argv[1]))
    # Tearing down the QApplication (PyQt's exit handler and interpreter
    # finalization) intermittently segfaults with no Python frame, before and
    # after U5 alike; recorded in U5-dead-ui-code.md. No exit handler owns a
    # process, so leave without teardown: this test checks the application's own
    # exit status and the processes it leaves behind.
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(exit_code)
