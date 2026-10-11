from openhcs.core.progress import (
    ProgressEvent,
    ProgressExecutionContext,
    ProgressPhase,
    ProgressStatus,
)
from openhcs.runtime.zmq_progress import ZMQCompilerProgressQueue, ZMQProgressEmitter


def _emitter(emitted: list[ProgressEvent]) -> ZMQProgressEmitter:
    return ZMQProgressEmitter(
        enqueue=emitted.append,
        execution_id="exec-1",
        subject_id="/tmp/plate",
    )


def test_compiler_progress_queue_reports_the_request_subject():
    emitted: list[ProgressEvent] = []
    queue = ZMQCompilerProgressQueue(
        enqueue=emitted.append,
        subject_id="/tmp/plate#openhcs-cppipe=Analysis.cppipe",
    )
    compiler_event = ProgressExecutionContext("exec-1", "/tmp/plate").event(
        axis_id="A01",
        step_name="compilation",
        phase=ProgressPhase.COMPILE,
        status=ProgressStatus.RUNNING,
        percent=50.0,
        completed=1,
        total=2,
    )

    queue.put(compiler_event)

    assert emitted[0].subject_id == "/tmp/plate#openhcs-cppipe=Analysis.cppipe"
    assert compiler_event.subject_id == "/tmp/plate"


def test_compile_failed_emits_failed_compile_events_for_axes():
    emitted: list[ProgressEvent] = []

    _emitter(emitted).compile_failed(axis_ids=["B02", "A01"], error="compile exploded")

    assert [event.axis_id for event in emitted] == ["A01", "B02"]
    assert {event.phase for event in emitted} == {ProgressPhase.COMPILE}
    assert {event.status for event in emitted} == {ProgressStatus.FAILED}
    assert {event.error for event in emitted} == {"compile exploded"}


def test_compile_failed_emits_pipeline_failure_when_axes_are_unknown():
    emitted: list[ProgressEvent] = []

    _emitter(emitted).compile_failed(axis_ids=[], error="early compile exploded")

    assert [event.axis_id for event in emitted] == ["pipeline"]
    assert emitted[0].phase is ProgressPhase.COMPILE
    assert emitted[0].status is ProgressStatus.FAILED
    assert emitted[0].error == "early compile exploded"


def test_compile_heartbeat_emits_running_pipeline_compile_event():
    emitted: list[ProgressEvent] = []

    _emitter(emitted).compile_heartbeat(step_count=18)

    assert len(emitted) == 1
    assert emitted[0].identity == ProgressExecutionContext(
        "exec-1", "/tmp/plate"
    ).event(
        axis_id="",
        step_name="pipeline",
        phase=ProgressPhase.COMPILE,
        status=ProgressStatus.RUNNING,
        percent=0.0,
        completed=0,
        total=18,
    ).identity
    assert emitted[0].phase is ProgressPhase.COMPILE
    assert emitted[0].status is ProgressStatus.RUNNING
    assert emitted[0].total == 18
