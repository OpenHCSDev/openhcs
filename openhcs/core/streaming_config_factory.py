"""Shared behavior and utilities for concrete streaming configuration classes."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field, fields
from typing import TYPE_CHECKING, ClassVar

from objectstate import DataclassFieldAccess, get_base_config_type
from python_introspect.validation import overlay_non_none_dataclass
from polystore.filemanager import FileManager
from polystore.streaming.viewer_transport import (
    ExplicitViewerTransportConfig,
    ViewerStreamBackendKwargs,
    ViewerStreamMessageContext,
    ViewerStreamProducer,
    ViewerStreamRequest,
    ViewerStreamSource,
    ViewerStreamSourceIdentity,
    ViewerStreamSourceMetadata,
    ViewerDisplayConfigABC,
)
from zmqruntime.config import TransportMode, ZMQConfig
from zmqruntime.messages import WireMessage
from zmqruntime.viewer_protocol import ViewerTransportEndpoint

from openhcs.core.streaming_config_declarations import ViewerFamily
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

if TYPE_CHECKING:
    from openhcs.core.config import StreamingConfig
    from openhcs.core.context.processing_context import ExecutingContext


@dataclass(frozen=True, slots=True)
class StreamingViewerSurface:
    """Viewer runtime, display, and source surface for one OpenHCS stream."""

    runtime_config: "StreamingViewerRuntimeConfig"
    display_config: "StreamingConfig"
    source: ViewerStreamSourceIdentity

    def viewer_stream_request(
        self,
        *,
        producer: ViewerStreamProducer,
        source_metadata: ViewerStreamSourceMetadata,
        message_context: ViewerStreamMessageContext,
    ) -> ViewerStreamRequest:
        return ViewerStreamRequest.from_message_context(
            message_context=message_context,
            viewer_transport=self.runtime_config.transport_endpoint,
            display_config=self.display_config,
            source=ViewerStreamSource(
                identity=self.source,
                metadata=source_metadata,
            ),
            producer=producer,
            transport_config=ExplicitViewerTransportConfig(
                self.runtime_config.transport_config
            ),
        )

    def viewer_backend_kwargs(
        self,
        *,
        producer: ViewerStreamProducer,
        source_metadata: ViewerStreamSourceMetadata,
        message_context: ViewerStreamMessageContext,
    ) -> ViewerStreamBackendKwargs:
        return ViewerStreamBackendKwargs(
            self.viewer_stream_request(
                producer=producer,
                source_metadata=source_metadata,
                message_context=message_context,
            )
        )


@dataclass(frozen=True, slots=True)
class ViewerProcessLaunchConfig(WireMessage):
    """Process-global settings that must exist before viewer construction.

    Its declared fields are its wire spelling on the viewer control boundary.
    """

    qt_font_dpi: int | None = None
    listen_host: str = "127.0.0.1"

    def __post_init__(self) -> None:
        if not isinstance(self.listen_host, str):
            raise TypeError("Viewer listen host must be a string.")
        if not self.listen_host.strip():
            raise ValueError("Viewer listen host must not be blank.")
        if isinstance(self.qt_font_dpi, bool) or not isinstance(
            self.qt_font_dpi, int | None
        ):
            raise TypeError("Viewer Qt font DPI must be an integer or None.")
        if self.qt_font_dpi is not None and self.qt_font_dpi <= 0:
            raise ValueError("Viewer Qt font DPI must be positive when provided.")

    def matches_existing_viewer(
        self,
        active: "ViewerProcessLaunchConfig",
        *,
        owns_process: bool,
    ) -> bool:
        """Require local bind policy only for a process this lifecycle owns.

        An externally owned viewer's listen interface is not a client launch
        setting: accepting its connection must not request a rebind/restart.
        """

        return self.qt_font_dpi == active.qt_font_dpi and (
            not owns_process or self.listen_host == active.listen_host
        )

    @classmethod
    def from_wire_mapping(
        cls,
        payload: Mapping[str, object],
    ) -> "ViewerProcessLaunchConfig":
        """Rehydrate an exact launch declaration: every declared field is required."""

        missing = tuple(name.name for name in fields(cls) if name.name not in payload)
        if missing:
            raise KeyError(f"Viewer process-launch declaration is missing {missing!r}.")
        return cls.from_dict(payload)


@dataclass(frozen=True, slots=True)
class StreamingViewerRuntimeConfig:
    """Concrete runtime objects shared by viewer lifecycle and backend dispatch."""

    transport_endpoint: ViewerTransportEndpoint
    persistent: bool
    viewer_family: type[ViewerFamily]
    transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG
    display_enabled: bool = True
    scope_accent_color: str | None = None
    process_launch: ViewerProcessLaunchConfig = field(
        default_factory=ViewerProcessLaunchConfig
    )


class StreamingConfigBehaviorMixin:
    """Shared implementation for concrete viewer streaming configs."""

    viewer_family: ClassVar[type[ViewerFamily]]
    transport_mode: TransportMode

    def with_display_config(self, display: ViewerDisplayConfigABC | None):
        """Overlay the original display declaration on its matching viewer config."""
        if display is None:
            return self
        if not isinstance(self, type(display)):
            raise TypeError("Display config must belong to the selected viewer config.")
        return overlay_non_none_dataclass(self, display)

    @classmethod
    def port_from_config(cls, config) -> int | None:
        streaming_config = DataclassFieldAccess.raw_value(
            config,
            cls.viewer_family.config_key,
        )
        if streaming_config is None:
            return None
        return streaming_config.port

    def viewer_runtime_config(
        self,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
    ) -> StreamingViewerRuntimeConfig:
        return StreamingViewerRuntimeConfig(
            transport_endpoint=ViewerTransportEndpoint(
                port=self.port,
                host=self.host,
                transport_mode=self.transport_mode,
            ),
            transport_config=transport_config,
            persistent=self.persistent,
            display_enabled=self.enabled,
            viewer_family=self.viewer_family,
            scope_accent_color=self.scope_accent_color,
            process_launch=self.viewer_process_launch_config(),
        )

    def viewer_process_launch_config(self) -> ViewerProcessLaunchConfig:
        """Return process-launch settings owned by this viewer declaration."""

        return ViewerProcessLaunchConfig(listen_host=self.listen_host)

    def viewer_surface(
        self,
        source: ViewerStreamSourceIdentity,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
    ) -> StreamingViewerSurface:
        return StreamingViewerSurface(
            runtime_config=self.viewer_runtime_config(transport_config),
            display_config=self,
            source=source,
        )

    def streaming_viewer_surface(
        self,
        context: "ExecutingContext | None",
    ) -> StreamingViewerSurface:
        if context is None:
            raise ValueError("Streaming viewer surface requires a ExecutingContext.")
        source = ViewerStreamSourceIdentity(
            microscope_handler=context.microscope_handler,
            plate_path=context.dataset_root,
        )
        return self.viewer_surface(source, context.transport_config)

    def create_visualizer(
        self,
        filemanager: FileManager,
        visualizer_config=None,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
    ):
        return self.viewer_family.create_visualizer(
            filemanager=filemanager,
            runtime_config=self.viewer_runtime_config(transport_config),
        )


def get_all_streaming_ports(
    config=None,
    num_ports_per_type: int = 10,
) -> list[int]:
    """Get all configured streaming ports for all registered streaming config types."""

    from objectstate import get_live_global_config

    from openhcs.core.config import StreamingConfig

    ports: list[int] = []
    base_config_type = get_base_config_type()

    if config is None:
        config = get_live_global_config(base_config_type)
        if config is None:
            return ports

    global_config = get_live_global_config(base_config_type)

    for streaming_config_type in tuple(StreamingConfig.__registry__.values()):
        port = streaming_config_type.port_from_config(config)
        if port is None and global_config is not None:
            port = streaming_config_type.port_from_config(global_config)
        if port is None:
            continue
        ports.extend(port + i for i in range(num_ports_per_type))

    return ports
