"""Shared behavior and utilities for concrete streaming configuration classes."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING, ClassVar

from objectstate import DataclassFieldAccess, get_base_config_type
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
)
from zmqruntime.config import TransportMode, ZMQConfig
from zmqruntime.viewer_protocol import ViewerTransportEndpoint

from openhcs.constants.constants import Backend
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

if TYPE_CHECKING:
    from openhcs.core.config import StreamingConfig
    from openhcs.core.context.processing_context import ProcessingContext


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


class ViewerProcessLaunchField(str, Enum):
    """Wire fields projected from the viewer process-launch declaration."""

    QT_FONT_DPI = "qt_font_dpi"


@dataclass(frozen=True, slots=True)
class ViewerProcessLaunchConfig:
    """Process-global settings that must exist before viewer construction."""

    qt_font_dpi: int | None = None

    def __post_init__(self) -> None:
        if self.qt_font_dpi is not None and self.qt_font_dpi <= 0:
            raise ValueError("Viewer Qt font DPI must be positive when provided.")

    def to_wire_mapping(self) -> dict[str, int | None]:
        """Project the launch declaration onto the viewer control boundary."""

        return {
            ViewerProcessLaunchField.QT_FONT_DPI.value: self.qt_font_dpi,
        }

    @classmethod
    def from_wire_mapping(
        cls,
        payload: Mapping[str, object],
    ) -> "ViewerProcessLaunchConfig":
        """Rehydrate an exact launch declaration from viewer state."""

        value = payload[ViewerProcessLaunchField.QT_FONT_DPI.value]
        if value is not None and (
            not isinstance(value, int) or isinstance(value, bool)
        ):
            raise TypeError("Viewer Qt font DPI must be an integer or None.")
        return cls(qt_font_dpi=value)


@dataclass(frozen=True, slots=True)
class StreamingViewerRuntimeConfig:
    """Concrete runtime objects shared by viewer lifecycle and backend dispatch."""

    transport_endpoint: ViewerTransportEndpoint
    persistent: bool
    viewer_type: ViewerType
    transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG
    display_enabled: bool = True
    scope_accent_color: str | None = None
    process_launch: ViewerProcessLaunchConfig = field(
        default_factory=ViewerProcessLaunchConfig
    )


class StreamingConfigBehaviorMixin:
    """Shared implementation for concrete viewer streaming configs."""

    viewer_type_declaration: ClassVar[ViewerType]
    transport_mode: TransportMode

    @classmethod
    def port_from_config(cls, config) -> int | None:
        streaming_config = DataclassFieldAccess.raw_value(
            config,
            cls.viewer_type_declaration.config_key,
        )
        if streaming_config is None:
            return None
        return streaming_config.port

    @property
    def backend(self) -> Backend:
        return self.viewer_type.backend

    @property
    def viewer_type(self) -> ViewerType:
        return type(self).viewer_type_declaration

    @property
    def streaming_config_key(self) -> str:
        return self.viewer_type.config_key

    @property
    def display_name(self) -> str:
        return self.viewer_type.display_name

    @property
    def step_plan_output_key(self) -> str:
        return self.viewer_type.step_plan_output_key

    @property
    def viewer_title(self) -> str:
        return self.viewer_type.title

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
            viewer_type=self.viewer_type,
            scope_accent_color=self.scope_accent_color,
            process_launch=self.viewer_process_launch_config(),
        )

    def viewer_process_launch_config(self) -> ViewerProcessLaunchConfig:
        """Return process-launch settings owned by this viewer declaration."""

        return ViewerProcessLaunchConfig()

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
        context: "ProcessingContext | None",
    ) -> StreamingViewerSurface:
        if context is None:
            raise ValueError("Streaming viewer surface requires a ProcessingContext.")
        source = ViewerStreamSourceIdentity(
            microscope_handler=context.microscope_handler,
            plate_path=context.plate_path,
        )
        return self.viewer_surface(source, context.transport_config)

    def create_visualizer(
        self,
        filemanager: FileManager,
        visualizer_config=None,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
    ):
        return self.viewer_type.create_visualizer(
            filemanager=filemanager,
            runtime_config=self.viewer_runtime_config(transport_config),
        )


def get_all_streaming_ports(
    config=None,
    num_ports_per_type: int = 10,
) -> list[int]:
    """Get all configured streaming ports for all registered streaming config types."""

    from objectstate.global_config import get_current_global_config

    from openhcs.core.config import StreamingConfig

    ports: list[int] = []
    base_config_type = get_base_config_type()

    if config is None:
        config = get_current_global_config(base_config_type)
        if config is None:
            return ports

    global_config = get_current_global_config(base_config_type)

    for streaming_config_type in tuple(StreamingConfig.__registry__.values()):
        port = streaming_config_type.port_from_config(config)
        if port is None and global_config is not None:
            port = streaming_config_type.port_from_config(global_config)
        if port is None:
            continue
        ports.extend(port + i for i in range(num_ports_per_type))

    return ports
