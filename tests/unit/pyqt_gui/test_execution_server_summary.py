from openhcs.core.progress.projection import (
    ExecutionRuntimeProjection,
    SubjectRuntimeIdentity,
    SubjectRuntimeProjection,
    SubjectRuntimeState,
    QueuedSubjectRuntimeState,
    ExecutingSubjectRuntimeState,
    CompleteSubjectRuntimeState,
    FailedSubjectRuntimeState,
)
from openhcs.pyqt_gui.widgets.shared.server_browser.presentation_models import (
    summarize_execution_server,
)


def _projection(*plates: SubjectRuntimeProjection) -> ExecutionRuntimeProjection:
    projection = ExecutionRuntimeProjection()
    for plate in plates:
        projection.add_subject(plate)
        projection.mark_latest(plate.identity)
    projection.recalculate_summary()
    return projection


def _plate(
    subject_id: str,
    state: type[SubjectRuntimeState],
    percent: float,
) -> SubjectRuntimeProjection:
    return SubjectRuntimeProjection(
        identity=SubjectRuntimeIdentity(f"exec-{subject_id}", subject_id),
        state=state,
        percent=percent,
        axis_progress=(),
        latest_timestamp=1.0,
    )


def test_execution_server_summary_handles_empty_projection():
    summary = summarize_execution_server(_projection())
    assert summary.status_text == "✅ Idle"
    assert summary.info_text == ""


def test_execution_server_summary_formats_registered_state_counts_and_average():
    summary = summarize_execution_server(
        _projection(
            _plate("p1", QueuedSubjectRuntimeState, 0.0),
            _plate("p2", ExecutingSubjectRuntimeState, 50.0),
            _plate("p3", CompleteSubjectRuntimeState, 100.0),
        )
    )

    assert "⏳ 1 queued" in summary.status_text
    assert "⚙️ 1 executing" in summary.status_text
    assert "✅ 1 complete" in summary.status_text
    assert summary.info_text == "Avg: 50.0% | 3 plates"


def test_execution_server_summary_includes_failed_count():
    summary = summarize_execution_server(
        _projection(_plate("p1", FailedSubjectRuntimeState, 25.0))
    )

    assert "❌ 1 failed" in summary.status_text
    assert summary.info_text == "Avg: 25.0% | 1 plates"
