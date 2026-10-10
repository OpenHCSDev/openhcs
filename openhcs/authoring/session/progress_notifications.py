"""Typed notifications carried by execution progress events."""

from __future__ import annotations

import logging
from dataclasses import dataclass

from openhcs.core.debug import DebugProgressContext, DebugSnapshot
from openhcs.core.progress import ProgressEvent
from openhcs.core.progress.debug_projection import DebugProgressRecord
from openhcs.core.progress.live_measurements import LiveMeasurementProgressPayload
from openhcs.core.progress.runtime_artifacts import RuntimeArtifactProgressPayload

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class DebugSnapshotAvailableNotification:
    """One debug snapshot can be read."""

    progress_event: ProgressEvent
    debug_context: DebugProgressContext
    snapshot: DebugSnapshot | None = None

    @classmethod
    def from_progress_event(
        cls,
        event: ProgressEvent,
        *,
        zmq_client,
    ) -> "DebugSnapshotAvailableNotification | None":
        record = DebugProgressRecord.from_progress_event(event)
        if record is None or record.snapshot_id is None:
            return None
        return cls(
            progress_event=event,
            debug_context=record.context,
            snapshot=_read_debug_snapshot(record.context, zmq_client=zmq_client),
        )


def _read_debug_snapshot(
    debug_context: DebugProgressContext,
    *,
    zmq_client,
) -> DebugSnapshot | None:
    if (
        debug_context.snapshot_store_ref is None
        or debug_context.snapshot_id is None
        or zmq_client is None
    ):
        return None
    try:
        return zmq_client.get_debug_snapshot(
            debug_session_id=debug_context.debug_session_id,
            snapshot_id=debug_context.snapshot_id,
            snapshot_store_ref=debug_context.snapshot_store_ref,
            snapshot_store_backend=debug_context.snapshot_store_backend,
        )
    except Exception as error:
        logger.debug("Server debug snapshot readback failed: %s", error)
        return None


@dataclass(frozen=True, slots=True)
class LiveMeasurementAvailableNotification:
    """Live measurement previews carried by one progress event."""

    event: ProgressEvent
    payload: LiveMeasurementProgressPayload

    @classmethod
    def from_progress_event(
        cls,
        event: ProgressEvent,
    ) -> "LiveMeasurementAvailableNotification | None":
        payload = LiveMeasurementProgressPayload.from_context(event.context)
        return None if payload is None else cls(event=event, payload=payload)


@dataclass(frozen=True, slots=True)
class RuntimeArtifactAvailableNotification:
    """Runtime artifact addresses carried by one progress event."""

    event: ProgressEvent
    payload: RuntimeArtifactProgressPayload

    @classmethod
    def from_progress_event(
        cls,
        event: ProgressEvent,
    ) -> "RuntimeArtifactAvailableNotification | None":
        payload = RuntimeArtifactProgressPayload.from_context(event.context)
        return None if payload is None else cls(event=event, payload=payload)
