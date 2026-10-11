from openhcs.core.progress import ProgressEvent, ProgressPhase, ProgressStatus, registry
from openhcs.core.progress.types import (
    PatternGroupProgressPhase,
    RunningProgressStatus,
    StepCompletedProgressPhase,
    SuccessProgressStatus,
)


def _event(
    *,
    phase: type[ProgressPhase],
    status: type[ProgressStatus],
    percent: float,
    axis_id: str = "A01",
    step_name: str = "pipeline",
    completed: int = 0,
    total: int = 1,
) -> ProgressEvent:
    return ProgressEvent(
        execution_id="exec-1",
        subject_id="/tmp/plate",
        axis_id=axis_id,
        step_name=step_name,
        phase=phase,
        status=status,
        percent=percent,
        completed=completed,
        total=total,
        timestamp=1.0,
        pid=1111,
    )


def test_registry_keeps_pipeline_and_step_channels_separate():
    tracker = registry()
    tracker.clear_all()

    pipeline_event = _event(
        phase=StepCompletedProgressPhase,
        status=SuccessProgressStatus,
        percent=25.0,
        completed=1,
        total=4,
    )
    step_event = _event(
        phase=PatternGroupProgressPhase,
        status=RunningProgressStatus,
        percent=50.0,
        completed=1,
        total=2,
        step_name="max_project",
    )

    tracker.register_event("exec-1", pipeline_event)
    tracker.register_event("exec-1", step_event)

    events = tracker.get_events("exec-1")
    assert len(events) == 2
    phase_set = {event.phase for event in events}
    assert phase_set == {StepCompletedProgressPhase, PatternGroupProgressPhase}

    tracker.clear_all()
