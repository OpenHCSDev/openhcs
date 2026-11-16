from __future__ import annotations

from abc import ABC
from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from typing import Annotated, ClassVar, Self

from annotated_types import Ge
from pydantic import StrictBool, StrictInt
from python_introspect.validation import validate_annotated_dataclass

from metaclass_registry import AutoRegisterMeta
from zmqruntime.messages import WireView
from zmqruntime.viewer_protocol import ViewerControlResponseField, ViewerProtocolStatus


class ViewerSettlePhase(ABC, metaclass=AutoRegisterMeta):
    """Where one viewer's incremental settlement stands.

    Each phase is a subclass; ``name`` is its wire spelling.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[ViewerSettlePhase]]] = {}

    name: ClassVar[str | None] = None
    running: ClassVar[bool] = False
    """Display work is still queued or active."""
    settled: ClassVar[bool] = False
    """Every queued update is displayed."""
    failed: ClassVar[bool] = False
    """Display work failed; settlement will not complete."""
    idle_completion_percent: ClassVar[float] = 0.0
    """Completion reported when there were no updates to settle."""

    @classmethod
    def validate(cls, progress: ViewerSettleProgress) -> None:
        """Reject progress this phase cannot report."""


class SettlementComplete(ViewerSettlePhase):
    name = "complete"
    settled = True
    idle_completion_percent = 100.0

    @classmethod
    def validate(cls, progress: ViewerSettleProgress) -> None:
        if progress.intake_item_active:
            raise ValueError("Completed settlement cannot have active intake.")
        if (
            progress.completed_update_count != progress.total_update_count
            or progress.routing
        ):
            raise ValueError(
                "Completed viewer settlement must have no active route and all "
                "updates completed."
            )


class ViewerPersistenceMode(Enum):
    """Viewer lifecycle ownership mode derived from streaming persistence."""

    PERSISTENT = ("persistent", False)
    NON_PERSISTENT = ("non-persistent", True)

    def __new__(
        cls,
        value: str,
        execution_session_owns_process: bool,
    ) -> Self:
        member = object.__new__(cls)
        member._value_ = value
        member.execution_session_owns_process = execution_session_owns_process
        return member

    @classmethod
    def from_flag(cls, persistent: bool) -> Self:
        if persistent:
            return cls.PERSISTENT
        return cls.NON_PERSISTENT


@dataclass(frozen=True, slots=True)
class ViewerControlResponse:
    """Typed view of a viewer control-message response."""

    payload: Mapping[str, object]

    @property
    def status(self) -> ViewerProtocolStatus:
        status_value = self.payload.get(ViewerControlResponseField.STATUS.value)
        if status_value is None:
            raise ValueError("Viewer control response is missing a status field.")
        return ViewerProtocolStatus(str(status_value))

    def succeeded(self) -> bool:
        return self.status is ViewerProtocolStatus.SUCCESS


@dataclass(frozen=True, slots=True)
class ViewerSettleProgress(WireView):
    """Typed progress for one viewer's incremental settlement cycle.

    It travels as declared fields beside the control reply's header.
    """

    phase: type[ViewerSettlePhase]
    completed_update_count: Annotated[StrictInt, Ge(0)]
    total_update_count: Annotated[StrictInt, Ge(0)]
    active_route: str | None = None
    active_route_work_unit_count: Annotated[StrictInt, Ge(0)] = 0
    active_route_work_unit_active: StrictBool = False
    processed_intake_item_count: Annotated[StrictInt, Ge(0)] = 0
    intake_item_active: StrictBool = False

    @property
    def routing(self) -> bool:
        """An update is being routed to a layer."""
        return self.active_route is not None

    def __post_init__(self) -> None:
        validate_annotated_dataclass(self)
        if self.completed_update_count > self.total_update_count:
            raise ValueError(
                "Viewer settle progress counts must satisfy 0 <= completed <= total."
            )
        if self.active_route is None and self.active_route_work_unit_count:
            raise ValueError(
                "Viewer settle work-unit progress requires an active route."
            )
        if self.active_route is None and self.active_route_work_unit_active:
            raise ValueError(
                "Viewer settle active work-unit state requires an active route."
            )
        self.phase.validate(self)

    @classmethod
    def complete(cls, total_update_count: int = 0) -> ViewerSettleProgress:
        """Return terminal successful settlement progress."""

        return cls(
            phase=SettlementComplete,
            completed_update_count=total_update_count,
            total_update_count=total_update_count,
        )

    @property
    def progress_marker(self) -> tuple[int, int, int]:
        return (
            self.processed_intake_item_count,
            self.completed_update_count,
            self.active_route_work_unit_count,
        )

    @property
    def work_unit_active(self) -> bool:
        return self.intake_item_active or self.active_route_work_unit_active

    def heartbeat_due(self, elapsed_seconds: float, interval_seconds: float) -> bool:
        """An unchanged observation is re-published only while work is running."""
        return self.work_unit_active and elapsed_seconds >= interval_seconds

    @property
    def completion_percent(self) -> float:
        if self.total_update_count:
            return 100.0 * self.completed_update_count / self.total_update_count
        return self.phase.idle_completion_percent
