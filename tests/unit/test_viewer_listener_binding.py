"""Exercise real data/control socket binding without constructing a GUI/JVM."""

from pathlib import Path

import pytest
import zmq
from zmqruntime.config import TransportMode
from zmqruntime.transport import DataControlPortPairAuthority

from openhcs.core.config import StreamingConfig
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.streaming_config_factory import ViewerProcessLaunchConfig
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG


def napari_server(port, mode, listen_host):
    from openhcs.runtime.napari_viewer_server import NapariViewerServer
    from openhcs.runtime.viewer_protocol import NapariViewerServerRequest

    return NapariViewerServer(
        NapariViewerServerRequest(
            port=port,
            viewer_title="Listener binding test",
            transport_mode=mode,
            process_launch=ViewerProcessLaunchConfig(listen_host=listen_host),
        )
    )


def fiji_server(port, mode, listen_host):
    from openhcs.runtime.fiji_viewer_server import (
        FijiViewerServer,
        FijiViewerServerLaunchConfig,
    )

    return FijiViewerServer(
        FijiViewerServerLaunchConfig(
            port=port,
            fiji_viewer_title="Listener binding test",
            fiji_display_config=None,
            transport_mode=mode,
            process_launch=ViewerProcessLaunchConfig(listen_host=listen_host),
        )
    )


@pytest.mark.parametrize("server_factory", (napari_server, fiji_server))
@pytest.mark.parametrize(
    "mode,listen_host,expected_prefix",
    (
        (TransportMode.TCP, "127.0.0.1", "tcp://127.0.0.1:"),
        (TransportMode.TCP, "*", "tcp://0.0.0.0:"),
        (TransportMode.IPC, "remote.example", "ipc://"),
    ),
)
def test_server_binds_both_real_sockets_to_declared_interface(
    server_factory, mode, listen_host, expected_prefix
):
    pair = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
        transport_mode=mode,
    )
    server = server_factory(pair.data_port, mode, listen_host)
    context = zmq.Context()
    sockets = []
    try:
        sockets.append(server.bind_data_socket(context))
        sockets.append(server.bind_control_socket(context))
        for socket in sockets:
            endpoint = socket.getsockopt_string(zmq.LAST_ENDPOINT)
            assert endpoint.startswith(expected_prefix), endpoint
    finally:
        for socket in sockets:
            socket.close(linger=0)
        context.term()
        if server.ack_socket is not None:
            server.ack_socket.close(linger=0)
        server.endpoint.cleanup(server.config)


@pytest.mark.parametrize("viewer_type", tuple(ViewerType))
def test_detached_launch_projects_listener_from_process_declaration(viewer_type):
    config = StreamingConfig.config_type_for_viewer(viewer_type)(
        host="remote.example",
        listen_host="192.0.2.1",
        transport_mode=TransportMode.TCP,
    )
    visualizer = viewer_type.declaration.visualizer_type()(
        filemanager=object(),
        runtime_config=config.viewer_runtime_config(),
    )
    arguments = visualizer.detached_server_arguments(log_file=Path("viewer.log"))
    assert visualizer.runtime_endpoint.host == "remote.example"
    assert arguments.expressions[-1].source == "'192.0.2.1'"
