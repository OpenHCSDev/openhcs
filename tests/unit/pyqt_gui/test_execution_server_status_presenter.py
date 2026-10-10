from openhcs.core.progress.projection import (
    ExecutionRuntimeProjection,
    PlateRuntimeIdentity,
    PlateRuntimeProjection,
    PlateRuntimeState,
)
from openhcs.authoring.session.progress import execution_server_status_text


def test_execution_server_status_status_text_returns_ready_when_no_plates():
    projection = ExecutionRuntimeProjection()

    text = execution_server_status_text(projection)

    assert text == "Ready"


def test_execution_server_status_status_text_includes_projection_counts():
    plate_one = PlateRuntimeProjection(
        identity=PlateRuntimeIdentity(execution_id="exec-1", plate_id="/tmp/p1"),
        state=PlateRuntimeState.COMPILING,
        percent=40.0,
        axis_progress=tuple(),
        latest_timestamp=1.0,
    )
    plate_two = PlateRuntimeProjection(
        identity=PlateRuntimeIdentity(execution_id="exec-2", plate_id="/tmp/p2"),
        state=PlateRuntimeState.EXECUTING,
        percent=85.0,
        axis_progress=tuple(),
        latest_timestamp=1.0,
    )
    projection = ExecutionRuntimeProjection(
        by_plate_latest={"/tmp/p1": plate_one, "/tmp/p2": plate_two},
        state_counts={
            PlateRuntimeState.COMPILING: 1,
            PlateRuntimeState.EXECUTING: 1,
        },
        overall_percent=62.5,
    )
    text = execution_server_status_text(projection)

    assert text == "Server: ⏳ 1 compiling, ⚙️ 1 executing | 2 plates | avg 62.5%"


def test_execution_server_status_status_text_includes_failed_projection_count():
    failed_plate = PlateRuntimeProjection(
        identity=PlateRuntimeIdentity(execution_id="exec-3", plate_id="/tmp/p3"),
        state=PlateRuntimeState.FAILED,
        percent=10.0,
        axis_progress=tuple(),
        latest_timestamp=1.0,
    )
    projection = ExecutionRuntimeProjection(
        by_plate_latest={"/tmp/p3": failed_plate},
        state_counts={PlateRuntimeState.FAILED: 1},
        overall_percent=10.0,
    )

    text = execution_server_status_text(projection)

    assert text == "Server: ❌ 1 failed | 1 plates | avg 10.0%"
