"""Execution progress: register server events, rebuild the runtime projection.

Progress messages arrive on the execution client's thread. Each one marks
the projection dirty; the session's main thread rebuilds it at most once per
``interval_seconds`` and publishes the result as session events.
"""

from __future__ import annotations

import logging
import threading
from typing import TYPE_CHECKING

from pyqt_reactive.services.interval_snapshot_poller import (
    CallbackIntervalSnapshotPollerPolicy,
    IntervalSnapshotPoller,
)
from pyqt_reactive.services.zmq_server_info import (
    BaseServerInfo,
    ExecutionServerInfo,
)
from zmqruntime.progress import EventRegistryMutation

from openhcs.authoring.session.events import (
    LiveMeasurementAvailable,
    RuntimeArtifactAvailable,
    StatusReported,
)
from openhcs.authoring.session.progress_notifications import (
    DebugSnapshotAvailableNotification,
    LiveMeasurementAvailableNotification,
    RuntimeArtifactAvailableNotification,
)
from openhcs.core.progress import ProgressEvent
from openhcs.core.progress.debug_projection import (
    RuntimeProjectionBuilder,
    RuntimeProjectionBundle,
    RuntimeProjectionSource,
)
from openhcs.core.progress.live_measurements import LiveMeasurementPayloadError
from openhcs.core.progress.projection import ExecutionRuntimeProjection
from openhcs.core.progress.runtime_artifacts import RuntimeArtifactPayloadError

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session

logger = logging.getLogger(__name__)


def execution_server_status_text(projection: ExecutionRuntimeProjection) -> str:
    """One status line summarizing the runtime projection."""

    plate_count = len(projection.by_plate_latest)
    if plate_count == 0:
        return "Ready"
    parts = projection.count_status_labels()
    status_text = ", ".join(parts) if parts else "idle"
    return (
        f"Server: {status_text} | "
        f"{plate_count} plates | avg {projection.overall_percent:.1f}%"
    )


class ExecutionProgress:
    """Owns progress registration, the runtime projection and server status."""

    def __init__(self, session: "Session", *, interval_seconds: float) -> None:
        self._session = session
        self._interval_seconds = interval_seconds
        self._builder = RuntimeProjectionBuilder()
        self._dirty = threading.Event()
        self._closed = threading.Event()
        self._registry_subscription = session.progress_tracker.subscribe_mutations(
            self._on_registry_mutation
        )
        self._server_info_poller = IntervalSnapshotPoller[ExecutionServerInfo](
            CallbackIntervalSnapshotPollerPolicy(
                fetch_snapshot_fn=self._fetch_server_info_snapshot,
                clone_snapshot_fn=lambda snapshot: snapshot,
                poll_interval_seconds_value=1.0,
                on_snapshot_changed_fn=lambda _snapshot: self.mark_dirty(),
                on_poll_error_fn=lambda error: logger.debug(
                    "Server info poll failed: %s", error
                ),
            )
        )
        self._thread = threading.Thread(
            target=self._run, name="openhcs-session-progress", daemon=True
        )
        self._thread.start()

    def set_interval(self, interval_seconds: float) -> None:
        self._interval_seconds = interval_seconds

    def close(self) -> None:
        self._closed.set()
        self._dirty.set()
        self._registry_subscription.release()

    def _run(self) -> None:
        while not self._closed.is_set():
            self._closed.wait(self._interval_seconds)
            if self._closed.is_set():
                return
            client_connected = self._session.client.has_client()
            if not (self._dirty.is_set() or client_connected):
                continue
            try:
                self._session.main_thread.post(self._tick)
            except Exception as error:  # dispatcher closed during shutdown
                logger.debug("Progress tick not dispatched: %s", error)
                return

    def _tick(self) -> None:
        if self._session.client.has_client():
            self._server_info_poller.tick()
        if self._dirty.is_set():
            self.rebuild()

    def reset_for_new_batch(self) -> None:
        tracker = self._session.progress_tracker
        for execution_id in list(tracker.get_execution_ids()):
            tracker.clear_execution(execution_id)
        self._session.install_runtime_projection(RuntimeProjectionBundle.empty())
        self._server_info_poller.reset()
        self.mark_dirty()

    def clear_execution(self, execution_id: str) -> None:
        """Remove one execution's progress and rebuild the projection."""

        self._session.progress_tracker.clear_execution(execution_id)
        self.rebuild()

    def rebuild(self) -> None:
        """Rebuild the runtime projection from tracked events and publish it."""

        self._dirty.clear()
        tracker = self._session.progress_tracker
        events_by_execution = {
            execution_id: tracker.get_events(execution_id)
            for execution_id in tracker.get_execution_ids()
        }
        server_info = self._server_info_poller.get_snapshot_copy()
        debug_context = self._session.current_debug_context()
        bundle = self._builder.build(
            RuntimeProjectionSource(
                events_by_execution=events_by_execution,
                running_executions=(
                    () if server_info is None else server_info.running_execution_entries
                ),
                queued_executions=(
                    () if server_info is None else server_info.queued_execution_entries
                ),
                session=None if debug_context is None else debug_context.active_session,
                terminal_summary=(
                    None if debug_context is None else debug_context.terminal_summary
                ),
                snapshots=() if debug_context is None else debug_context.snapshots,
            )
        )
        self._session.install_runtime_projection(bundle)
        self._session.publish(
            StatusReported(execution_server_status_text(bundle.execution))
        )

    def on_progress(self, message: dict) -> None:
        session = self._session
        try:
            event = ProgressEvent.from_dict(message)
            if not session.progress_tracker.register_event(event.execution_id, event):
                return
            debug_notification = DebugSnapshotAvailableNotification.from_progress_event(
                event,
                zmq_client=session.client.zmq_client,
            )
            if debug_notification is not None:
                session.main_thread.post(
                    lambda: session.record_debug_snapshot(debug_notification)
                )
            try:
                live = LiveMeasurementAvailableNotification.from_progress_event(event)
            except LiveMeasurementPayloadError as error:
                logger.warning(
                    "Malformed live measurement progress context for "
                    "execution_id=%s axis_id=%s step_name=%s: %s",
                    event.execution_id,
                    event.axis_id,
                    event.step_name,
                    error,
                )
            else:
                if live is not None:
                    session.live_measurements.add_notification(live)
                    session.publish(LiveMeasurementAvailable(live))
            try:
                artifact = RuntimeArtifactAvailableNotification.from_progress_event(event)
            except RuntimeArtifactPayloadError as error:
                logger.warning(
                    "Malformed runtime artifact progress context for "
                    "execution_id=%s axis_id=%s step_name=%s: %s",
                    event.execution_id,
                    event.axis_id,
                    event.step_name,
                    error,
                )
            else:
                if artifact is not None:
                    session.publish(RuntimeArtifactAvailable(artifact))
        except Exception as error:
            logger.warning("Failed to parse/register progress event: %s", error)

    def _on_registry_mutation(
        self,
        _mutation: EventRegistryMutation[ProgressEvent],
    ) -> None:
        self.mark_dirty()

    def mark_dirty(self) -> None:
        self._dirty.set()

    def server_info_snapshot(self) -> ExecutionServerInfo | None:
        return self._server_info_poller.get_snapshot_copy()

    def _fetch_server_info_snapshot(self) -> ExecutionServerInfo:
        pong = self._session.client.require_client().get_server_info_snapshot()
        parsed = BaseServerInfo.from_response(pong)
        if not isinstance(parsed, ExecutionServerInfo):
            raise ValueError(
                f"Expected ExecutionServerInfo, got {type(parsed).__name__}"
            )
        return parsed

