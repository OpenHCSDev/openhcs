"""Live measurement previews retained by the session for its current batch."""

from __future__ import annotations

from dataclasses import astuple, dataclass
from typing import Any

from openhcs.authoring.session.progress_notifications import (
    LiveMeasurementAvailableNotification,
)
from openhcs.core.progress.live_measurements import LiveMeasurementTablePreview


@dataclass(frozen=True, slots=True)
class LiveMeasurementTableEntry:
    """One live measurement preview."""

    sequence_id: int
    execution_id: str
    plate_id: str
    axis_id: str
    step_name: str
    preview: LiveMeasurementTablePreview
    truncated_preview_group: bool

    @property
    def label(self) -> str:
        address = self.preview.address
        scope_text = address.key.scope.coordinate_label
        object_text = (
            f" [{self.preview.object_name}]" if self.preview.object_name else ""
        )
        return f"{self.step_name}: {address.key.name}{object_text} ({scope_text})"

    @property
    def semantic_sort_key(self) -> tuple:
        address = self.preview.address
        return (
            _semantic_sort_atom(self.plate_id),
            *(_semantic_sort_atom(part) for part in astuple(address.key.scope)),
            _semantic_sort_atom(self.step_name),
            _semantic_sort_atom(address.key.artifact_type.value),
            _semantic_sort_atom(address.key.name),
            _semantic_sort_atom(self.preview.object_name),
            self.sequence_id,
        )


class LiveMeasurementTable:
    """Live measurement previews retained for the current execution batch."""

    def __init__(self, *, max_entries: int = 500) -> None:
        self._max_entries = max_entries
        self._entries: list[LiveMeasurementTableEntry] = []
        self._next_sequence_id = 0

    def clear(self) -> None:
        self._entries.clear()
        self._next_sequence_id = 0

    def add_notification(
        self,
        notification: LiveMeasurementAvailableNotification,
    ) -> None:
        event = notification.event
        for preview in notification.payload.previews:
            self._entries.append(
                LiveMeasurementTableEntry(
                    sequence_id=self._next_sequence_id,
                    execution_id=event.execution_id,
                    plate_id=event.plate_id,
                    axis_id=event.axis_id,
                    step_name=event.step_name,
                    preview=preview,
                    truncated_preview_group=notification.payload.truncated_previews,
                )
            )
            self._next_sequence_id += 1
        if len(self._entries) > self._max_entries:
            del self._entries[: len(self._entries) - self._max_entries]

    @property
    def entries(self) -> tuple[LiveMeasurementTableEntry, ...]:
        return tuple(self._entries)

    def latest_sequence_id(self) -> int | None:
        if not self._entries:
            return None
        return self._entries[-1].sequence_id

    def entry_by_sequence_id(
        self,
        sequence_id: int | None,
    ) -> LiveMeasurementTableEntry | None:
        if sequence_id is None:
            return None
        for entry in self._entries:
            if entry.sequence_id == sequence_id:
                return entry
        return None

    def semantic_entries(self) -> tuple[LiveMeasurementTableEntry, ...]:
        return tuple(sorted(self._entries, key=lambda entry: entry.semantic_sort_key))


def _semantic_sort_atom(value: Any) -> tuple[int, int | str]:
    if value in (None, ""):
        return (0, "")
    text = str(value)
    if text.isdecimal():
        return (1, int(text))
    return (2, text.casefold())
