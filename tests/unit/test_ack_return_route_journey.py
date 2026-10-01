"""Continuous synthetic save/REP/copy/deferred-ACK journey, with no GUI or JVM."""

import sys
from subprocess import Popen, TimeoutExpired
from multiprocessing import Pipe
from multiprocessing.connection import Connection
from multiprocessing.shared_memory import SharedMemory
from threading import Event

import numpy as np
import pytest

from polystore.napari_stream import NapariStreamingBackend
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming.viewer_transport import (
    BatchViewerStreamSourceMetadata,
    ViewerMicroscopeHandlerABC,
    ViewerStreamProducer,
    ViewerStreamRequest,
    ViewerStreamSource,
    ViewerStreamSourceIdentity,
)
from zmqruntime.ack_listener import GlobalAckListener
from zmqruntime.config import TransportMode, ZMQConfig
from zmqruntime.queue_tracker import GlobalQueueTrackerRegistry
from zmqruntime.transport import DataControlPortPairAuthority, TransportEndpoint

from openhcs.core.config import NapariDisplayConfig
from openhcs.runtime.napari_viewer_server import NapariViewerServer
from openhcs.runtime.viewer_protocol import NapariViewerServerRequest


class SyntheticMicroscope(ViewerMicroscopeHandlerABC):
    pass


def stream_producer(pipe, port, mode, config):
    backend = NapariStreamingBackend(transport_config=config)
    listener = GlobalAckListener()
    completed = Event()
    listener.register_callback(lambda ack: completed.set())
    request = ViewerStreamRequest(
        viewer_transport=TransportEndpoint("127.0.0.1", port, mode),
        display_config=NapariDisplayConfig(),
        source=ViewerStreamSource(
            identity=ViewerStreamSourceIdentity(SyntheticMicroscope(), None),
            metadata=BatchViewerStreamSourceMetadata({"well": "synthetic"}),
        ),
        producer=ViewerStreamProducer.from_identity(StreamProducerIdentity.pipeline_output(
            output_kind="main", output_key="main", projection_key="main",
            step_name="SyntheticTransport", pipeline_position=0,
        )),
    )
    try:
        for _ in range(2):
            assert pipe.poll(6), "No controlled send command"
            command = pipe.recv()
            if command == "close":
                break
            assert command == "send"
            completed.clear()
            backend.save_batch([np.arange(12, dtype=np.uint16).reshape(3, 4)],
                               ["synthetic.tif"], stream_request=request)
            tracker = GlobalQueueTrackerRegistry().get_tracker(port)
            pipe.send((listener.return_route, tracker.get_progress(), len(backend._shared_memory_blocks)))
            assert pipe.poll(6), "No controlled ACK check"
            command = pipe.recv()
            if command == "close":
                break
            assert command == "wait"
            pipe.send((completed.wait(2), tracker.get_progress()))
    finally:
        backend.cleanup()
        listener.stop(timeout_ms=2000)
        pipe.close()


def receive(pipe):
    assert pipe.poll(6), "Owned source process did not answer within the test bound"
    return pipe.recv()


@pytest.mark.parametrize("mode", [TransportMode.TCP, TransportMode.IPC])
def test_two_native_stream_producers_keep_deferred_ack_ownership(mode, tmp_path_factory):
    directory = tmp_path_factory.mktemp("ack")
    config = ZMQConfig(default_port=48000, ipc_socket_dir=str(directory))
    pair = DataControlPortPairAuthority.acquire(config, transport_mode=mode)
    server = NapariViewerServer(NapariViewerServerRequest(
        port=pair.data_port, viewer_title="synthetic ACK transport", transport_mode=mode,
    ))
    server.config = config
    server._running = True
    owners = []
    server.data_transport_pump.start()
    try:
        for _ in range(2):
            parent, child = Pipe()
            # Separate native interpreters, like the application: multiprocessing
            # siblings would share one resource-tracker and invalidate this proof.
            process = Popen([sys.executable, __file__, str(child.fileno()),
                             str(pair.data_port), mode.value, str(directory)],
                            pass_fds=(child.fileno(),))
            child.close()
            owners.append((process, parent))
        routes = []
        for index, (process, pipe) in enumerate(owners):
            pipe.send("send")
            route, progress, remaining_memory = receive(pipe)
            routes.append(route)
            assert progress == (0, 1)  # Transfer REP is not the display ACK.
            assert remaining_memory == 0
            accepted = server.accepted_stream_batches.get(timeout=3)
            item = accepted.items[0]
            assert item.payload.transfer.return_route == route
            np.testing.assert_array_equal(item.data, np.arange(12, dtype=np.uint16).reshape(3, 4))
            with pytest.raises(FileNotFoundError):
                SharedMemory(name=item.payload.shm_name)
            assert server.send_ack(item.payload.transfer)
            pipe.send("wait")
            assert receive(pipe) == (True, (1, 1))
            if index == 0:
                pipe.send("send")
                route_again, progress, remaining_memory = receive(pipe)
                assert route_again == route  # One warm process owner, not a port per batch.
                assert progress == (1, 2)
                second = server.accepted_stream_batches.get(timeout=3).items[0]
                assert server.send_ack(second.payload.transfer)
                pipe.send("wait")
                assert receive(pipe) == (True, (2, 2))
            else:
                pipe.send("close")
            assert process.wait(timeout=3) == 0
        assert routes[0] != routes[1]
        assert server.data_transport_pump._thread.is_alive()
        assert server.transport_failure is None
    finally:
        for process, pipe in owners:
            if process.poll() is None:
                try:
                    pipe.send("close")
                except BrokenPipeError:
                    pass
                try:
                    process.wait(timeout=3)
                except TimeoutExpired:
                    process.terminate()
                    process.wait(timeout=2)
            pipe.close()
            assert process.poll() is not None
        server._running = False
        server.data_transport_pump.stop()
        mode.declaration.cleanup_endpoint(pair.data_port, config)
        assert not any(directory.glob("*.sock"))


if __name__ == "__main__":
    stream_producer(Connection(int(sys.argv[1])), int(sys.argv[2]),
                    TransportMode(sys.argv[3]), ZMQConfig(ipc_socket_dir=sys.argv[4]))
