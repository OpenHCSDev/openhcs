"""One control-action family for every viewer server.

Each viewer declares a family root (``ViewerControlAction`` subclass with
``family_root=True``). The root gets its own registry keyed by the control
message wire type, and inherits every lifecycle action declared once here:
the metaclass composes each :class:`LifecycleControlAction` mixin with the
root, so a viewer cannot forget shutdown, clear-state, process-launch or
settle. Messages no leaf registers answer ERROR through one shared
:class:`UnknownControlAction`. Pong capabilities derive from the registry.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import replace
from typing import TYPE_CHECKING, ClassVar

from zmqruntime.messages import (
    ControlMessageType,
    EndpointControlCapability,
    ResponseType,
)
from zmqruntime.viewer_protocol import (
    ViewerControlMessageType,
    ViewerControlReplyHeader,
    ViewerControlReplyPayload,
    ViewerControlResponseField,
    ViewerProtocolStatus,
)

from openhcs.runtime.viewer_protocol import (
    OpenHCSViewerControlMessageType,
    ViewerControlField,
    ViewerSettlePhase,
    ViewerSettleProgress,
)

if TYPE_CHECKING:
    from openhcs.core.streaming_config_factory import ViewerProcessLaunchConfig

ControlReply = dict[str, object]


class ViewerServerPort(ABC):
    """What the shared lifecycle actions need from a viewer server."""

    control_actions: ClassVar[type["ViewerControlAction"]]
    viewer_display_name: ClassVar[str]
    process_launch: "ViewerProcessLaunchConfig"

    def _create_pong_response(self):
        """Advertise the lifecycle actions this viewer's registry handles."""

        return replace(
            super()._create_pong_response(),
            control_capabilities=self.control_actions.control_capabilities(),
        )

    @abstractmethod
    def shut_down_after_reply(self) -> None:
        """Stop the server once the shutdown acknowledgement is sent."""

    @abstractmethod
    def clear_stream_state(self) -> None:
        """Forget accumulated stream state without shutting down."""

    @abstractmethod
    def settle_progress(self) -> ViewerSettleProgress:
        """Queued and active display-work progress."""

    @abstractmethod
    def settle_failure_message(self) -> str | None:
        """The terminal display failure, if one happened."""

    def settle_unavailable_message(self) -> str | None:
        """Why settlement cannot be observed at all, if it cannot."""

        return None

    def settle_progress_on_transport_thread(self) -> ViewerSettleProgress:
        """Settlement progress readable without the viewer's UI thread."""

        return self.settle_progress()

    def handle_control_message(self, message: Mapping[str, object]) -> ControlReply:
        """Answer one control message through this viewer's action registry."""

        return self.control_actions.for_message(message).handle(self, message)


def control_reply(
    status: ViewerProtocolStatus,
    *,
    response_type: str | None = None,
    message: str | None = None,
    fields: Mapping[str, object] | None = None,
    payload: object | None = None,
) -> ControlReply:
    """Spell one viewer control reply on the wire."""

    return ViewerControlReplyPayload(
        ViewerControlReplyHeader(status, response_type=response_type, message=message),
        fields=dict(fields or {}),
        payload=payload,
    ).to_wire_mapping()


class ViewerControlAction(ABC):
    """Behaviour for one control message type on one viewer."""

    message_type: ClassVar[str | None] = None
    _registry: ClassVar[dict[str, type["ViewerControlAction"]]]
    _unknown: ClassVar[type["ViewerControlAction"]]

    def __init_subclass__(cls, *, family_root: bool = False, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if family_root:
            cls._registry = {}
            for lifecycle in LifecycleControlAction.declared():
                type(
                    f"{cls.__name__.removesuffix('ControlAction')}{lifecycle.__name__}",
                    (lifecycle, cls),
                    {"__module__": cls.__module__, "message_type": lifecycle.message_type},
                )
            cls._unknown = type(
                f"{cls.__name__.removesuffix('ControlAction')}UnknownControlAction",
                (UnknownControlAction, cls),
                {"__module__": cls.__module__, "message_type": None},
            )
            return
        message_type = cls.__dict__.get("message_type")
        if message_type is None:
            return
        existing = cls._registry.get(message_type)
        if existing is not None and not issubclass(cls, existing):
            raise TypeError(
                f"{cls.__qualname__} and {existing.__qualname__} both handle "
                f"control message {message_type!r}."
            )
        cls._registry[message_type] = cls

    @classmethod
    def registered_message_types(cls) -> frozenset[str]:
        return frozenset(cls._registry)

    @classmethod
    def for_message_type(cls, message_type: object) -> "ViewerControlAction":
        if isinstance(message_type, str) and message_type in cls._registry:
            return cls._registry[message_type]()
        return cls._unknown()

    @classmethod
    def for_message(cls, message: Mapping[str, object]) -> "ViewerControlAction":
        return cls.for_message_type(message.get(ViewerControlResponseField.TYPE.value))

    @classmethod
    def control_capabilities(cls) -> frozenset[EndpointControlCapability]:
        """Lifecycle capabilities advertised on pong, derived from the registry."""

        return frozenset(
            capability
            for capability in EndpointControlCapability
            if capability is EndpointControlCapability.PING
            or capability.value in cls._registry
        )

    @property
    def response_type(self) -> str:
        return f"{self.message_type}_ack"

    @abstractmethod
    def handle(self, server: ViewerServerPort, message: Mapping[str, object]) -> ControlReply:
        """Answer one control message."""

    def transport_thread_response(
        self, server: ViewerServerPort, message: Mapping[str, object]
    ) -> ControlReply | None:
        """Answer without the viewer's UI thread, or ``None`` to defer to it."""

        del server, message
        return None


class LifecycleControlAction(ABC):
    """A control action every viewer family inherits."""

    message_type: ClassVar[str]
    _declared: ClassVar[list[type["LifecycleControlAction"]]] = []

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if LifecycleControlAction in cls.__bases__ and "message_type" in cls.__dict__:
            LifecycleControlAction._declared.append(cls)

    @staticmethod
    def declared() -> tuple[type["LifecycleControlAction"], ...]:
        return tuple(LifecycleControlAction._declared)


class ShutdownControlAction(LifecycleControlAction):
    message_type = ControlMessageType.SHUTDOWN.value

    @property
    def response_type(self) -> str:
        return ResponseType.SHUTDOWN_ACK.value

    def handle(self, server: ViewerServerPort, message: Mapping[str, object]) -> ControlReply:
        del message
        server.shut_down_after_reply()
        return control_reply(
            ViewerProtocolStatus.SUCCESS,
            response_type=self.response_type,
            message=f"{server.viewer_display_name} viewer shutting down",
        )


class ForceShutdownControlAction(ShutdownControlAction, LifecycleControlAction):
    message_type = ControlMessageType.FORCE_SHUTDOWN.value


class ClearStateControlAction(LifecycleControlAction):
    message_type = ViewerControlMessageType.CLEAR_STATE.value

    def handle(self, server: ViewerServerPort, message: Mapping[str, object]) -> ControlReply:
        del message
        server.clear_stream_state()
        return control_reply(
            ViewerProtocolStatus.SUCCESS,
            response_type=self.response_type,
            message=f"{server.viewer_display_name} stream state cleared",
        )


class ProcessLaunchControlAction(LifecycleControlAction):
    message_type = OpenHCSViewerControlMessageType.PROCESS_LAUNCH.value

    def handle(self, server: ViewerServerPort, message: Mapping[str, object]) -> ControlReply:
        del message
        return control_reply(
            ViewerProtocolStatus.SUCCESS,
            response_type=self.response_type,
            fields={
                ViewerControlField.PROCESS_LAUNCH.value: (
                    server.process_launch.to_wire_mapping()
                )
            },
        )

    def transport_thread_response(
        self, server: ViewerServerPort, message: Mapping[str, object]
    ) -> ControlReply:
        return self.handle(server, message)


class SettleControlAction(LifecycleControlAction):
    message_type = ViewerControlMessageType.SETTLE.value

    def handle(self, server: ViewerServerPort, message: Mapping[str, object]) -> ControlReply:
        del message
        return self.reply(server, server.settle_progress)

    def transport_thread_response(
        self, server: ViewerServerPort, message: Mapping[str, object]
    ) -> ControlReply:
        """Observe settlement without waiting for the UI thread to render."""

        del message
        return self.reply(server, server.settle_progress_on_transport_thread)

    def reply(self, server: ViewerServerPort, progress_of) -> ControlReply:
        unavailable = server.settle_unavailable_message()
        if unavailable is not None:
            return control_reply(
                ViewerProtocolStatus.ERROR,
                response_type=self.response_type,
                message=unavailable,
            )
        progress = progress_of()
        failed = progress.phase is ViewerSettlePhase.FAILED
        name = server.viewer_display_name
        return control_reply(
            ViewerProtocolStatus.ERROR if failed else ViewerProtocolStatus.SUCCESS,
            response_type=self.response_type,
            message=(
                f"{name} viewer settlement failed: {server.settle_failure_message()}"
                if failed
                else (
                    f"{name} viewer settlement progress: "
                    f"{progress.completed_update_count}/{progress.total_update_count}."
                )
            ),
            fields=progress.to_wire_mapping(),
        )


class UnknownControlAction:
    """Shared answer for a message type no leaf of the family handles."""

    @property
    def response_type(self) -> str:
        return ResponseType.ERROR.value

    def handle(self, server: ViewerServerPort, message: Mapping[str, object]) -> ControlReply:
        requested = message.get(ViewerControlResponseField.TYPE.value)
        return control_reply(
            ViewerProtocolStatus.ERROR,
            response_type=self.response_type,
            message=(
                f"Unsupported {server.viewer_display_name} control message: "
                f"{requested!r}."
            ),
        )

    def transport_thread_response(
        self, server: ViewerServerPort, message: Mapping[str, object]
    ) -> ControlReply:
        return self.handle(server, message)

