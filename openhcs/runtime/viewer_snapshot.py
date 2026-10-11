"""Managed viewer reply hooks on the original Qt snapshot capture algorithm."""

from __future__ import annotations

from dataclasses import dataclass, fields

from pyqt_reactive.services.window_snapshot import (
    QtWindowSnapshot,
    QtWindowSnapshotService,
    WindowSnapshotObservationFailure,
    WindowVisualObservation,
)
from zmqruntime.messages import ControlErrorResponse

from openhcs.agent.dto.common import AgentResourceRef
from openhcs.agent.dto.viewer import ViewerWindowDescriptor
from python_introspect import to_jsonable


@dataclass(frozen=True, kw_only=True)
class ViewerWindowSnapshotFailureReply(ControlErrorResponse):
    """Native observation evidence on the existing control error."""

    observation: WindowVisualObservation

    @classmethod
    def from_control_error(
        cls,
        error: ControlErrorResponse,
        failure: WindowSnapshotObservationFailure,
    ) -> ViewerWindowSnapshotFailureReply:
        return cls(
            **{
                declared.name: getattr(error, declared.name)
                for declared in fields(ControlErrorResponse)
            },
            observation=failure.observation,
        )

    def to_dict(self) -> dict[str, object]:
        """The control error's wire mapping, carrying the native observation as is."""

        error = ControlErrorResponse(
            **{
                declared.name: getattr(self, declared.name)
                for declared in fields(ControlErrorResponse)
            }
        )
        return {**error.to_dict(), "observation": self.observation}


class ViewerWindowSnapshotService(QtWindowSnapshotService):
    """Managed reply projection; deadline/render/capture stay on the Qt ancestor.

    A viewer supplies the already-owned window, native renderer, descriptor and
    identity. No viewer taxonomy, discovery roster or second observation loop.
    """

    @staticmethod
    def snapshot_reply(descriptor, snapshot: QtWindowSnapshot) -> dict[str, object]:
        return {
            "type": "screenshot_ack",
            "status": "success",
            "viewer": {
                "type": descriptor.viewer_type.value,
                "title": descriptor.title,
            },
            "resource": to_jsonable(
                AgentResourceRef(
                    uri=snapshot.uri,
                    title=snapshot.title,
                    mime_type=snapshot.mime_type,
                    path=snapshot.path,
                    size_bytes=snapshot.size_bytes,
                    sha256=snapshot.sha256,
                )
            ),
            "width": snapshot.width,
            "height": snapshot.height,
            "snapshot": snapshot.capture,
            "observation": snapshot.observation,
        }
