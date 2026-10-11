import pytest

from openhcs.core.debug import (
    AfterInvocationDebugBoundary,
    BeforeInvocationDebugBoundary,
    DebugBoundary,
    DebugCursor,
    DebugProgressContext,
    DebugSession,
    DebugSnapshot,
    DebugTerminalSummary,
)
from openhcs.core.progress import ProgressEvent
from openhcs.core.progress.debug_projection import (
    DebugProgressRecord,
    RuntimeProjectionBuilder,
    RuntimeProjectionSource,
)
from openhcs.core.progress.types import (
    PatternGroupProgressPhase,
    StartedProgressStatus,
)


def _event(
    *,
    context=None,
    timestamp: float = 1.0,
) -> ProgressEvent:
    return ProgressEvent(
        execution_id="exec-1",
        subject_id="/tmp/plate",
        axis_id="A01",
        step_name="segment",
        phase=PatternGroupProgressPhase,
        status=StartedProgressStatus,
        percent=50.0,
        completed=1,
        total=2,
        timestamp=timestamp,
        pid=1234,
        context=context,
    )


def _cursor() -> DebugCursor:
    return DebugCursor(
        step_index=1,
        step_scope_id="step-1",
        group_key="default",
        invocation_key="default:0:segment",
    )


def _debug_context(
    *,
    event_type: type[DebugBoundary] = BeforeInvocationDebugBoundary,
) -> dict:
    return DebugProgressContext(
        debug_session_id="debug-1",
        snapshot_id="snapshot-1",
        cursor=_cursor(),
        event_type=event_type,
        snapshot_store_ref="/tmp/debug",
    ).to_context()


def test_debug_progress_record_ignores_normal_progress_context() -> None:
    assert DebugProgressRecord.from_progress_event(_event(context=None)) is None
    assert (
        DebugProgressRecord.from_progress_event(
            _event(context={"live_measurements": {}})
        )
        is None
    )


def test_debug_progress_record_fails_loudly_for_malformed_debug_context() -> None:
    with pytest.raises(ValueError, match="missing required field"):
        DebugProgressRecord.from_progress_event(
            _event(
                context={DebugProgressContext.context_key: {"debug_session_id": "debug-1"}}
            )
        )


def test_runtime_projection_builder_projects_debug_records_from_same_snapshot() -> None:
    event = _event(
        context=_debug_context(event_type=AfterInvocationDebugBoundary),
        timestamp=2.0,
    )
    session = DebugSession(
        debug_session_id="debug-1",
        execution_id="exec-1",
        subject_id="/tmp/plate",
    ).with_cursor(_cursor())

    bundle = RuntimeProjectionBuilder().build(
        RuntimeProjectionSource(
            events_by_execution={"exec-1": [event]},
            session=session,
            snapshots=(
                DebugSnapshot(
                    snapshot_id="snapshot-1",
                    cursor=_cursor(),
                    step_name="snapshot segment",
                    callable_name="segment_callable",
                ),
            ),
        )
    )

    assert bundle.execution.get_subject("/tmp/plate", "exec-1") is not None
    assert len(bundle.debug.records) == 1
    assert bundle.debug.debug_session_id == session.debug_session_id
    assert bundle.debug.current_frame is not None
    assert bundle.debug.current_frame.cursor == _cursor()
    assert bundle.debug.current_frame.snapshot_id == "snapshot-1"
    assert bundle.debug.current_frame.step_name == "snapshot segment"
    assert bundle.debug.current_frame.callable_name == "segment_callable"
    assert bundle.debug.current_frame.event_type is AfterInvocationDebugBoundary


def test_terminal_debug_projection_keeps_last_frame_without_active_frame() -> None:
    event = _event(context=_debug_context(), timestamp=2.0)
    terminal_summary = DebugTerminalSummary(
        debug_session_id="debug-1",
        subject_id="/tmp/plate",
        terminal_status="complete",
        cursor=_cursor(),
    )

    bundle = RuntimeProjectionBuilder().build(
        RuntimeProjectionSource(
            events_by_execution={"exec-1": [event]},
            terminal_summary=terminal_summary,
        )
    )

    assert bundle.debug.current_frame is None
    assert bundle.debug.last_frame is not None
    assert bundle.debug.debug_session_id == "debug-1"
