"""Viewer endpoint discovery across the local IPC directory.

Detached viewer processes outlive the desktop application that spawned them,
and the desktop's in-process viewer registry starts empty on every launch, so
live unowned viewers are invisible to both the app and agents. This authority
sweeps the OpenHCS IPC directory for viewer data sockets, probes each control
endpoint, and classifies every live viewer as owned or foreign so callers can
report or close them explicitly.
"""

from __future__ import annotations

import re
import socket
from dataclasses import dataclass
from pathlib import Path
from typing import Any


from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

_VIEWER_SOCKET_PATTERN = re.compile(r"^openhcs-zmq-(\d+)\.sock$")
_DISCOVERY_TIMEOUT_MS = 750


@dataclass(frozen=True, slots=True)
class ViewerEndpointRecord:
    """One discovered live viewer endpoint and its classification."""

    port: int
    control_port: int
    socket_path: str
    viewer_type: str
    title: str | None
    layer_count: int | None
    owned: bool
    detail: str | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "port": self.port,
            "control_port": self.control_port,
            "socket_path": self.socket_path,
            "viewer_type": self.viewer_type,
            "title": self.title,
            "layer_count": self.layer_count,
            "owned": self.owned,
            "detail": self.detail,
        }


def viewer_ipc_directory() -> Path:
    """Return the OpenHCS IPC socket directory for the configured transport."""

    return (
        Path.home()
        / f".{OPENHCS_ZMQ_CONFIG.app_name}"
        / OPENHCS_ZMQ_CONFIG.ipc_socket_dir
    )


def candidate_viewer_ports() -> tuple[int, ...]:
    """Return data ports whose declared control partner socket also exists.

    Every OpenHCS endpoint binds a data socket plus its control socket
    (data port + control offset). A socket file whose control partner is
    absent is itself a control socket, not a data endpoint, so the sweep
    probes data/control pairs instead of every socket in the directory.
    """

    offset = OPENHCS_ZMQ_CONFIG.control_port_offset
    ports = set(_declared_socket_ports())
    data_ports = []
    for port in sorted(ports):
        if (port - offset) in ports:
            continue
        if (port + offset) in ports:
            data_ports.append(port)
    return tuple(data_ports)


def _declared_socket_ports() -> tuple[int, ...]:
    directory = viewer_ipc_directory()
    try:
        socket_names = list(directory.iterdir())
    except OSError:
        return ()
    ports = []
    for entry in socket_names:
        match = _VIEWER_SOCKET_PATTERN.fullmatch(entry.name)
        if match is None:
            continue
        ports.append(int(match.group(1)))
    return tuple(sorted(set(ports)))


def _probe_control_endpoint(port: int) -> dict[str, Any]:
    """Read one viewer's state through the viewer-window gateway authority.

    The gateway owns the control-message framing; the sweep reuses it instead
    of re-implementing the protocol so discovery and control stay on one
    declaration.
    """

    from openhcs.agent.dto.execution import ExecutionConnectionSpec
    from openhcs.agent.dto.viewer import ViewerWindowStateRequest
    from openhcs.agent.services.viewer_window_service import ZMQViewerWindowGateway

    request = ViewerWindowStateRequest.from_fields(
        connection=ExecutionConnectionSpec(
            "localhost",
            port,
            OPENHCS_ZMQ_CONFIG.transport_mode,
            True,
        ),
        timeout_ms=_DISCOVERY_TIMEOUT_MS,
        include_component_values=False,
        include_payload_summaries=False,
    )
    return ZMQViewerWindowGateway().window_state(request)


def _socket_is_bound(socket_path: Path) -> bool:
    """Return whether a listener accepts connections on this unix socket.

    The IPC directory accumulates sockets left by servers that exited without
    cleanup; connecting over AF_UNIX rejects them immediately, which keeps the
    sweep proportional to live endpoints instead of the directory's history.
    """

    probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    probe.settimeout(0.25)
    try:
        probe.connect(str(socket_path))
        return True
    except OSError:
        return False
    finally:
        probe.close()


def _owned_viewer_state(port: int) -> bool:
    from zmqruntime.viewer_state import ViewerStateManager

    manager = ViewerStateManager.get_instance()
    for viewer_type in ("napari",):
        if manager.get_viewer_state(viewer_type, port) is not None:
            return True
    return False


def _projection_from_response(
    response: Any,
) -> tuple[str | None, int | None]:
    """Project the viewer title and layer count from one state response."""

    if not isinstance(response, dict):
        return None, None, None
    viewer = response.get("viewer")
    if not isinstance(viewer, dict):
        return None, None, None
    title = viewer.get("title")
    viewer_type = viewer.get("type")
    layer_count = response.get("layer_count")
    if layer_count is None and isinstance(response.get("layers"), (list, tuple)):
        layer_count = len(response["layers"])
    return (
        str(viewer_type) if viewer_type is not None else None,
        str(title) if title is not None else None,
        int(layer_count) if isinstance(layer_count, int) else None,
    )


def discover_viewer_endpoints() -> tuple[ViewerEndpointRecord, ...]:
    """Sweep the IPC directory and classify every live viewer endpoint."""

    records: list[ViewerEndpointRecord] = []
    for port in candidate_viewer_ports():
        socket_path = viewer_ipc_directory() / f"openhcs-zmq-{port}.sock"
        if not _socket_is_bound(socket_path):
            continue
        try:
            response = _probe_control_endpoint(port)
        except Exception:
            # An endpoint that pairs but does not answer a viewer-state read
            # with a viewer identity is another server kind (execution, UI
            # bridge); the existing server panels own those.
            continue
        viewer_type, title, layer_count = _projection_from_response(response)
        if viewer_type is None:
            continue
        records.append(
            ViewerEndpointRecord(
                port=port,
                control_port=port + OPENHCS_ZMQ_CONFIG.control_port_offset,
                socket_path=str(socket_path),
                viewer_type=viewer_type,
                title=title,
                layer_count=layer_count,
                owned=_owned_viewer_state(port),
            )
        )
    return tuple(records)


def unowned_viewer_endpoints() -> tuple[ViewerEndpointRecord, ...]:
    """Return live viewer endpoints this process does not own."""

    return tuple(record for record in discover_viewer_endpoints() if not record.owned)


class ViewerEndpointDiscoveryService:
    """Sweep authority for live viewer endpoints in the local IPC directory."""

    def sweep(self) -> "ViewerEndpointDiscoveryResult":
        from openhcs.agent.dto.viewer import ViewerEndpointDiscoveryResult
        from openhcs.serialization.json import to_jsonable

        endpoints = tuple(record.as_dict() for record in discover_viewer_endpoints())
        return ViewerEndpointDiscoveryResult(
            schema_version=SCHEMA_VERSION,
            endpoints=tuple(to_jsonable(endpoint) for endpoint in endpoints),
        )
