"""Compile, run and debug batches through the session, with a stand-in server.

The execution server is replaced at the two functions every compile goes
through (``submit_compile`` and ``wait_for_compile``) and at the session's
client connection, so admission, reservation and terminal bookkeeping are
exercised exactly as a client drives them.
"""

from __future__ import annotations

import asyncio
from pathlib import Path

import pytest

from openhcs.authoring.session import compile_batch as compile_batch_module
from openhcs.authoring.session.compilation import DatasetPipelineRequest
from openhcs.authoring.session.debug_runs import DebugRunRequest
from openhcs.authoring.session.events import (
    CompilationFailed,
    CompiledStateChanged,
    DebugSnapshotAvailable,
    LiveMeasurementAvailable,
    RuntimeArtifactAvailable,
)
from openhcs.authoring.session.execution_batch import ExecutionBatchRuntime
from openhcs.authoring.session.progress import execution_server_status_text
from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.artifacts import MeasurementsArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.debug import (
    DebugCommandType,
    DebugCursor,
    DebugEvent,
    DebugEventType,
    DebugProgressEventRequest,
    DebugReplayMode,
)
from openhcs.core.execution_state import ManagerExecutionState, TerminalExecutionStatus
from openhcs.core.orchestrator.orchestrator import OrchestratorState
from openhcs.core.progress import (
    ProgressEvent,
    ProgressIdentity,
    ProgressPhase,
    ProgressStatus,
)
from openhcs.core.progress.live_measurements import (
    LiveMeasurementProgressPayload,
    LiveMeasurementTablePreview,
)
from openhcs.core.progress.runtime_artifacts import RuntimeArtifactProgressPayload
from openhcs.core.runtime_artifact_values import ArtifactKey
from openhcs.core.runtime_stores import RuntimeArtifactAddress, RuntimeArtifactLocation
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler.dataset_scope import CellProfilerPipelineScope
from openhcs.runtime.zmq_execution_client import ZMQExecutionRequestBuilder
from tests.unit.pyqt_gui.session_harness import add_datasets, caller_session


class StandInServer:
    """Compile submission and completion, answered without a server."""

    def __init__(self, session, monkeypatch, *, failing=(), during_compile=None):
        self.session = session
        self.failing = set(failing)
        self.during_compile = during_compile
        self.submitted: list[str] = []
        self.connections = 0
        monkeypatch.setattr(compile_batch_module, "submit_compile", self.submit)
        monkeypatch.setattr(compile_batch_module, "wait_for_compile", self.wait)
        monkeypatch.setattr(session, "connect_client", self.connect)

    async def connect(self):
        self.connections += 1
        return object()

    async def submit(self, client, request: DatasetPipelineRequest) -> str:
        del client
        self.submitted.append(request.scope_id)
        return f"compile-{Path(request.scope_id).name}"

    async def wait(self, client, *, execution_id: str, scope_id: str):
        del client
        if self.during_compile is not None:
            self.during_compile(scope_id)
        if scope_id in self.failing:
            raise RuntimeError("controlled compile failure")
        return CompiledArtifactInspection(
            compile_artifact_id=execution_id, plate_id=scope_id, steps=()
        )


def _ready(session, *scope_ids: str) -> None:
    for scope_id in scope_ids:
        session.orchestrator(scope_id)._state = OrchestratorState.READY


def _running(session, scope_id: str, execution_id: str) -> None:
    session.batch.begin_batch((scope_id,))
    session.batch.record_execution(scope_id, execution_id)
    session.execution_state = ManagerExecutionState.RUNNING


async def _run(session, scope_id: str, debug: bool) -> None:
    if debug:
        await session.run_debug(scope_id, command_type=DebugCommandType.RUN)
    else:
        await session.run_datasets((scope_id,))


@pytest.mark.parametrize("debug", (False, True))
@pytest.mark.parametrize("pending", ("init_pending", "compile_pending"))
def test_run_and_debug_reject_a_pending_target_before_any_mutation(
    tmp_path, monkeypatch, debug, pending
):
    with caller_session() as session:
        (target,) = add_datasets(session, tmp_path, "target")
        getattr(session, pending).add(target)

        async def must_not_connect():
            pytest.fail("A rejected execution must not connect")

        monkeypatch.setattr(session, "connect_client", must_not_connect)
        with pytest.raises(RuntimeError, match="affected dataset"):
            asyncio.run(_run(session, target, debug))
        assert session.execution_state is ManagerExecutionState.IDLE
        assert not session.batch.active_plates
        assert target not in session.debug_sessions


@pytest.mark.parametrize("debug", (False, True))
def test_run_and_debug_cannot_replace_an_unrelated_active_batch(
    tmp_path, monkeypatch, debug
):
    with caller_session() as session:
        running, target = add_datasets(session, tmp_path, "running", "target")
        _running(session, running, "original-run")

        async def must_not_connect():
            pytest.fail("A rejected execution must not connect")

        monkeypatch.setattr(session, "connect_client", must_not_connect)
        with pytest.raises(RuntimeError, match="already active"):
            asyncio.run(_run(session, target, debug))
        assert session.batch.active_plates == (running,)
        assert session.batch.execution_id(running) == "original-run"
        assert session.execution_state is ManagerExecutionState.RUNNING


@pytest.mark.parametrize("debug", (False, True))
def test_run_and_debug_reserve_before_connect_and_release_on_connection_failure(
    tmp_path, monkeypatch, debug
):
    with caller_session() as session:
        target, unrelated, another = add_datasets(
            session, tmp_path, "target", "unrelated", "another"
        )
        _ready(session, target)
        session.compile_pending.add(unrelated)
        errors = []
        session.subscribe(
            lambda record: errors.append(record.event)
            if type(record.event).__name__ == "ErrorReported"
            else None
        )

        async def connect():
            assert session.execution_state is ManagerExecutionState.RUNNING
            assert session.batch.active_plates == (target,)
            session.require_definition_mutation_allowed(target)
            with pytest.raises(RuntimeError, match="active initialization"):
                session.require_work_allowed(target)
            with pytest.raises(RuntimeError, match="already active"):
                session.require_execution_allowed((another,))
            raise RuntimeError("controlled connection failure")

        monkeypatch.setattr(session, "connect_client", connect)
        asyncio.run(_run(session, target, debug))
        assert session.execution_state is ManagerExecutionState.IDLE
        assert not session.batch.active_plates
        assert session.batch.terminal_status(target) is TerminalExecutionStatus.FAILED
        assert session.compile_pending == {unrelated}
        assert len(errors) == 1


@pytest.mark.parametrize("fails", (False, True))
def test_compiling_another_dataset_keeps_the_active_batch(
    tmp_path, monkeypatch, fails
):
    with caller_session() as session:
        running, other = add_datasets(session, tmp_path, "running", "other")
        _ready(session, running, other)
        _running(session, running, "original-run")

        def during_compile(scope_id):
            assert scope_id == other
            assert session.compile_pending == {other}
            with pytest.raises(RuntimeError, match="affected dataset"):
                session.require_definition_mutation_allowed(other)
            assert session.batch.active_plates == (running,)
            assert session.batch.execution_id(running) == "original-run"
            assert session.batch.execution_id(other) is None

        server = StandInServer(
            session,
            monkeypatch,
            failing={other} if fails else (),
            during_compile=during_compile,
        )
        asyncio.run(session.compile_datasets((other,)))

        assert server.submitted == [other]
        assert not session.compile_pending
        assert session.batch.active_plates == (running,)
        assert session.batch.execution_id(running) == "original-run"
        assert session.execution_state is ManagerExecutionState.RUNNING
        assert (other in session.compiled) is not fails
        assert session.orchestrator(other).state is (
            OrchestratorState.COMPILE_FAILED if fails else OrchestratorState.COMPILED
        )
        session.batch.mark_terminal(running, TerminalExecutionStatus.COMPLETE)
        assert session.batch.all_batch_terminal()
        assert session.batch.terminal_counts() == (1, 0)


def test_compile_connection_failure_releases_only_its_reserved_dataset(
    tmp_path, monkeypatch
):
    with caller_session() as session:
        running, other = add_datasets(session, tmp_path, "running", "other")
        _ready(session, other)
        _running(session, running, "original-run")

        async def connect():
            raise RuntimeError("controlled connection failure")

        monkeypatch.setattr(session, "connect_client", connect)
        with pytest.raises(RuntimeError, match="controlled connection failure"):
            asyncio.run(session.compile_datasets((other,)))
        assert not session.compile_pending
        assert session.batch.execution_id(running) == "original-run"


def test_compile_publishes_its_inspection_and_clears_the_previous_one(
    tmp_path, monkeypatch
):
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        _ready(session, scope_id)
        compiled_states = []
        session.subscribe(
            lambda record: compiled_states.append(record.event.compiled)
            if isinstance(record.event, CompiledStateChanged)
            else None
        )

        def during_compile(_scope_id):
            assert scope_id not in session.compiled

        StandInServer(session, monkeypatch, during_compile=during_compile)
        asyncio.run(session.compile_datasets((scope_id,)))
        first = session.compiled[scope_id]
        asyncio.run(session.compile_datasets((scope_id,)))
        second = session.compiled[scope_id]

        assert first.inspection.compile_artifact_id == "compile-plate"
        assert session.compiled_inspection(scope_id) is second.inspection
        assert compiled_states == [None, first, None, second]


@pytest.mark.parametrize(
    "terminal", (TerminalExecutionStatus.COMPLETE, TerminalExecutionStatus.FAILED)
)
@pytest.mark.parametrize("fails", (False, True))
def test_recompile_supersedes_row_activity_without_erasing_the_batch_outcome(
    tmp_path, monkeypatch, terminal, fails
):
    from openhcs.authoring.session.views import DatasetActivity

    with caller_session() as session:
        active, finished = add_datasets(session, tmp_path, "A", "B")
        _ready(session, active, finished)
        session.execution_state = ManagerExecutionState.RUNNING
        session.batch.begin_batch((active, finished))
        session.batch.record_execution(active, "active-A")
        session.batch.record_execution(finished, "finished-B")
        session.batch.mark_terminal(finished, terminal)
        session.orchestrator(finished)._state = terminal.orchestrator_state
        outcome_before = session.batch.terminal_items()
        activity = DatasetActivity(session, finished)

        def during_compile(_scope_id):
            assert session.batch.terminal_status(finished) is None
            assert session.batch.execution_id(finished) is None
            assert session.batch.terminal_items() == outcome_before
            assert session.batch.active_plates == (active,)
            assert activity.status_prefix == "⏳ Compile"

        StandInServer(
            session,
            monkeypatch,
            failing={finished} if fails else (),
            during_compile=during_compile,
        )
        asyncio.run(session.compile_datasets((finished,)))

        expected = (
            OrchestratorState.COMPILE_FAILED if fails else OrchestratorState.COMPILED
        )
        assert session.orchestrator(finished).state is expected
        assert activity.orchestrator_state is expected
        assert activity.status_prefix == expected.status_prefix
        assert session.batch.terminal_items() == outcome_before
        assert session.batch.execution_id(active) == "active-A"
        assert session.batch.active_plates == (active,)
        session.batch.mark_terminal(active, TerminalExecutionStatus.COMPLETE)
        assert session.batch.terminal_counts() == (
            (2, 0) if terminal is TerminalExecutionStatus.COMPLETE else (1, 1)
        )


def test_failed_compile_reports_the_dataset(tmp_path, monkeypatch):
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        _ready(session, scope_id)
        failures = []
        session.subscribe(
            lambda record: failures.append(record.event)
            if isinstance(record.event, CompilationFailed)
            else None
        )
        StandInServer(session, monkeypatch, failing={scope_id})
        asyncio.run(session.compile_datasets((scope_id,)))
        assert [failure.scope_id for failure in failures] == [scope_id]
        assert scope_id not in session.compiled


def test_an_active_batch_member_cannot_be_superseded():
    batch = ExecutionBatchRuntime()
    batch.begin_batch(("/A",))
    batch.record_execution("/A", "active-A")
    with pytest.raises(RuntimeError, match="active execution"):
        batch.supersede_terminal("/A")
    assert batch.execution_id("/A") == "active-A"
    assert batch.active_plates == ("/A",)


# ---------------------------------------------------------------------------
# Requests sent to the server
# ---------------------------------------------------------------------------


def _request(scope, steps=(), **kwargs) -> DatasetPipelineRequest:
    return DatasetPipelineRequest(
        scope=scope,
        name=scope.display_name,
        execution_root=kwargs.pop("execution_root", str(scope.root)),
        pipeline_path=kwargs.pop("pipeline_path", None),
        steps=list(steps),
        pipeline_config=PipelineConfig(),
        global_config=GlobalPipelineConfig(),
        **kwargs,
    )


def test_submission_names_the_dataset_scope_and_runs_in_the_execution_root():
    scope = CellProfilerPipelineScope.scope_for(
        Path("/tmp/source"), Path("/tmp/source/BBBC022_Analysis_Start.cppipe")
    )
    submission = _request(
        scope,
        execution_root="/tmp/source/.openhcs_cellprofiler/Analysis_Start",
        pipeline_path="/tmp/source/BBBC022_Analysis_Start.cppipe",
    ).submission()

    assert submission.plate_id == scope.scope_id
    assert submission.execution_plate_id == (
        "/tmp/source/.openhcs_cellprofiler/Analysis_Start"
    )
    assert submission.selected_pipeline_path == (
        "/tmp/source/BBBC022_Analysis_Start.cppipe"
    )


def test_compile_and_run_submissions_share_one_request_signature():
    import openhcs.processing.backends.cellprofiler as cellprofiler_backend
    from openhcs.core.dataset_sources.dataset_scopes import DatasetScope

    request = _request(
        DatasetScope.parse("/tmp/plate"),
        [
            FunctionStep(
                func=(cellprofiler_backend.crop, {"crop_shape": "Rectangle"}),
                name="Crop",
            )
        ],
    )
    compile_payload = ZMQExecutionRequestBuilder.from_task(
        request.submission()
    ).request_payload
    run_payload = ZMQExecutionRequestBuilder.from_task(
        request.submission(compile_artifact_id="compile-1")
    ).request_payload

    assert run_payload.pipeline_sha == compile_payload.pipeline_sha
    assert run_payload.request_signature == compile_payload.request_signature


def _debug_request(**overrides) -> DebugRunRequest:
    values = dict(
        debug_session_id="debug-1",
        snapshot_store_ref="/tmp/snapshots/debug-1",
        snapshot_store_backend="local",
        command_type=DebugCommandType.STEP,
        selected_source_group="A01",
        pause_step_indices=(0,),
        replay_mode=DebugReplayMode.PERSISTENT_PAUSED_WORKER,
    )
    values.update(overrides)
    return DebugRunRequest(**values)


def _replay_signature(debug_request: DebugRunRequest) -> str:
    from openhcs.core.dataset_sources.dataset_scopes import DatasetScope

    request = _request(DatasetScope.parse("/tmp/plate")).with_config_params(
        debug_request.compile_config_params
    )
    return ZMQExecutionRequestBuilder.from_task(
        request.submission()
    ).request_payload.debug_replay_signature


def test_debug_compile_reuse_keys_on_the_session_not_the_cursor():
    first = _replay_signature(_debug_request(start_step_index=0))
    moved_cursor = _replay_signature(
        _debug_request(
            command_type=DebugCommandType.RUN_TO_PAUSE,
            start_step_index=4,
            start_after_invocation_key="default:0:color_to_gray",
        )
    )
    new_session = _replay_signature(
        _debug_request(
            debug_session_id="debug-2", snapshot_store_ref="/tmp/snapshots/debug-2"
        )
    )

    assert first == moved_cursor
    assert first != new_session


# ---------------------------------------------------------------------------
# Progress from the server becomes session events
# ---------------------------------------------------------------------------


def _progress_event(**kwargs) -> ProgressEvent:
    return ProgressEvent(
        identity=ProgressIdentity(
            execution_id="exec-1",
            plate_id="plate-1",
            axis_id="A01",
            step_name="Measure",
        ),
        phase=ProgressPhase.STEP_COMPLETED,
        status=ProgressStatus.SUCCESS,
        percent=100.0,
        completed=1,
        total=1,
        timestamp=1.0,
        pid=1234,
        **kwargs,
    )


def _debug_progress_event(*, snapshot_id: str | None, event_type=None):
    event = DebugEvent(
        event_type=event_type or DebugEventType.AFTER_INVOCATION,
        cursor=DebugCursor(
            step_index=1,
            step_scope_id="step-1",
            group_key="default",
            invocation_key="default:0:segment",
        ),
        step_name="IdentifyPrimaryObjects",
        callable_name="IdentifyPrimaryObjects",
        axis_id="A01",
    )
    return event, DebugProgressEventRequest(
        debug_session_id="debug-1",
        debug_event=event,
        execution_id="exec-1",
        plate_id="plate-1",
        **(
            {}
            if snapshot_id is None
            else {"snapshot_id": snapshot_id, "snapshot_store_ref": "/tmp/debug"}
        ),
    ).to_progress_event()


def _events_of(session, kind):
    return [
        record.event
        for record in session.events_after(0)
        if isinstance(record.event, kind)
    ]


def test_debug_progress_with_a_snapshot_publishes_it_and_projects_the_frame():
    with caller_session() as session:
        _event, progress = _debug_progress_event(snapshot_id="snapshot-1")
        session.progress.on_progress(progress.to_dict())
        session.progress.rebuild()

        (available,) = _events_of(session, DebugSnapshotAvailable)
        assert available.notification.debug_context.snapshot_id == "snapshot-1"
        assert available.notification.debug_context.snapshot_store_ref == "/tmp/debug"
        assert session.runtime_projection.get_plate("plate-1", "exec-1") is not None


def test_debug_progress_without_a_snapshot_publishes_nothing():
    with caller_session() as session:
        _event, progress = _debug_progress_event(
            snapshot_id=None, event_type=DebugEventType.BEFORE_INVOCATION
        )
        session.progress.on_progress(progress.to_dict())
        assert _events_of(session, DebugSnapshotAvailable) == []


def test_debug_progress_attaches_the_snapshot_the_server_returns(monkeypatch):
    with caller_session() as session:
        event, progress = _debug_progress_event(snapshot_id="snapshot-1")
        snapshot = event.to_snapshot(snapshot_id="snapshot-1")

        class Client:
            def get_debug_snapshot(self, **_kwargs):
                return snapshot

        client = Client()
        monkeypatch.setattr(
            type(session.client), "zmq_client", property(lambda _self: client)
        )
        session.progress.on_progress(progress.to_dict())
        (available,) = _events_of(session, DebugSnapshotAvailable)
        assert available.notification.snapshot == snapshot


def test_live_measurement_progress_is_tabled_and_published():
    with caller_session() as session:
        payload = LiveMeasurementProgressPayload(
            previews=(
                LiveMeasurementTablePreview(
                    address=RuntimeArtifactAddress(
                        key=ArtifactKey(
                            name="Measure",
                            artifact_type=MeasurementsArtifactType,
                            scope=RuntimeExecutionAxisScope(axis_id="A01"),
                        ),
                        location=RuntimeArtifactLocation(
                            path="/memory/measure.pkl", backend="memory"
                        ),
                    ),
                    columns=("mean",),
                    rows=({"mean": 3.0},),
                    row_count=1,
                    truncated_rows=False,
                    truncated_columns=False,
                ),
            ),
            preview_count=1,
            truncated_previews=False,
        )
        session.progress.on_progress(
            _progress_event(context=payload.to_context()).to_dict()
        )

        (available,) = _events_of(session, LiveMeasurementAvailable)
        assert available.notification.payload.previews[0].rows == ({"mean": 3.0},)
        assert len(session.live_measurements.entries) == 1


def test_runtime_artifact_progress_is_published():
    with caller_session() as session:
        address = RuntimeArtifactAddress(
            key=ArtifactKey(
                name="ResultImage",
                artifact_type=MeasurementsArtifactType,
                scope=RuntimeExecutionAxisScope(axis_id="A01"),
            ),
            location=RuntimeArtifactLocation(path="/memory/result.pkl", backend="memory"),
            value_type="ndarray",
        )
        event = _progress_event(
            context=RuntimeArtifactProgressPayload((address,)).to_context()
        )
        session.progress.on_progress(event.to_dict())

        (available,) = _events_of(session, RuntimeArtifactAvailable)
        assert available.notification.event == event
        assert available.notification.payload.addresses == (address,)


def test_progress_the_registry_rejects_publishes_nothing(monkeypatch):
    with caller_session() as session:
        monkeypatch.setattr(
            session.progress_tracker, "register_event", lambda *_args: False
        )
        address = RuntimeArtifactAddress(
            key=ArtifactKey(
                name="ResultImage",
                artifact_type=MeasurementsArtifactType,
                scope=RuntimeExecutionAxisScope(axis_id="A01"),
            ),
            location=RuntimeArtifactLocation(path="/memory/result.pkl", backend="memory"),
        )
        session.progress.on_progress(
            _progress_event(
                context=RuntimeArtifactProgressPayload((address,)).to_context()
            ).to_dict()
        )
        assert _events_of(session, RuntimeArtifactAvailable) == []


def test_server_queue_snapshot_projects_queued_executions(monkeypatch):
    from types import SimpleNamespace

    from zmqruntime.messages import QueuedExecutionInfo

    from openhcs.core.progress.projection import PlateRuntimeState

    with caller_session() as session:
        monkeypatch.setattr(
            session.progress._server_info_poller,
            "get_snapshot_copy",
            lambda: SimpleNamespace(
                running_execution_entries=(),
                queued_execution_entries=(
                    QueuedExecutionInfo(
                        execution_id="exec-queued",
                        subject_id="plate-queued",
                        queue_position=3,
                    ),
                ),
            ),
        )
        session.progress.rebuild()

        plate = session.runtime_projection.get_plate("plate-queued", "exec-queued")
        assert plate is not None
        assert plate.state is PlateRuntimeState.QUEUED
        assert plate.queue_position == 3
        assert execution_server_status_text(session.runtime_projection).startswith(
            "Server:"
        )


def test_a_standard_run_retires_the_previous_debug_summary(tmp_path, monkeypatch):
    from openhcs.core.debug import DebugTerminalSummary

    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        _ready(session, scope_id)
        session.debug_terminal_summaries[scope_id] = DebugTerminalSummary(
            debug_session_id="debug-1", plate_id=scope_id, terminal_status="failed"
        )
        StandInServer(session, monkeypatch, failing={scope_id})
        monkeypatch.setattr(session.client, "require_client", lambda: object())

        asyncio.run(session.run_datasets((scope_id,)))

        assert scope_id not in session.debug_terminal_summaries
        assert session.batch.terminal_status(scope_id) is TerminalExecutionStatus.FAILED
        assert session.execution_state is ManagerExecutionState.IDLE
