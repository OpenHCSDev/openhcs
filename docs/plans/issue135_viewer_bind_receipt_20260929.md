# #135: Managed viewer listen address

**Plan status:** provisional design, not a fix. **Source:** `OpenHCSDev/openhcs` `main` `0c7b898f852a8bedc0e1bc38b93f36088d301808`; external/ZMQRuntime gitlink `1d3b32f4fcead23d5d2079c975eb2ae7646a1478`. **Issue contract:** a localhost-requested managed TCP viewer must not expose its control endpoint on every network interface; a remotely addressable viewer remains a separate supported capability when explicitly chosen.

## Determining facts and consumers

- `openhcs/core/config.py:982–1010` calls `StreamingDefaults.host` the **viewer host** for client connection and permits remote TCP. `openhcs/core/streaming_config_factory.py:118–125,168–187` projects it into `ViewerTransportEndpoint` and runtime config.
- `openhcs/runtime/viewer_protocol.py:671–699` defines launch requests without a listen address; `:1289–1330` builds the client-facing runtime endpoint. `openhcs/runtime/napari_stream_visualizer.py:83–97` constructs detached arguments without a host.
- `openhcs/runtime/napari_viewer_server.py:5890–5926` constructs the server request; `:5540–5565` unconditionally gives the ZMQ parent `host="*"`. The reported `ss` observation in #135 is consistent with this source. The inherited parent binds data and control sockets; check both at the pinned dependency implementation before applying.
- `openhcs/runtime/fiji_viewer_server.py:1972` also passes `"*"`. This is a separate viewer family and a potential same-policy crossing, not automatically a regression covered by the Napari report. `openhcs/runtime/zmq_config.py:24–47` already distinguishes execution-server `client_host` and `server_host`; do not copy execution settings into viewer policy without evidence.

## Required answers and provisional relation

For a **locally launched** viewer, what address may the two TCP sockets bind, and what address do clients use? Candidate `R*`: the authorized listen-interface declaration must determine both the data and control bind addresses; the existing viewer transport endpoint determines connection/routing. These are different questions even if both are `127.0.0.1`. For IPC, bind-host selection must not change the local socket contract. For an **externally owned** remote viewer, OpenHCS may connect without launching or rebinding it; verify lifecycle behavior before deciding that a remote host is invalid at local launch. Unknown/OPEN: how the launch manager distinguishes local versus external ownership, exact ZMQRuntime bind propagation, Fiji parity, existing-viewer reuse, IPv6, and Windows TCP behavior. No missing class or inheritance edge is claimed.

## Candidate owner and falsifiers

Prefer an explicit viewer launch/bind policy carried through the existing `StreamingViewerRuntimeConfig` → managed lifecycle → detached server request, while retaining client `ViewerTransportEndpoint.host` for connection. **Do not silently reinterpret `host` as a bind interface**; remote connections and old configurations would answer different questions. Check whether the existing ZMQRuntime endpoint can carry this distinction before creating any new wrapper. The new-case test is a viewer reachable by an explicit remote host: connection host can vary without accidentally opening an all-interfaces listener when the viewer is started locally. A second falsifier is reused externally managed viewer state, which should not be killed/rebound just to honor a local setting.

## Implementation and proof gates before promotion from draft

1. Trace the pinned ZMQRuntime `StreamingVisualizerServer` bind and control-port policy, launcher argument serialization, Napari and Fiji lifecycles, and all other `host="*"` viewer sites. Obtain a complete contextual NRA scan and source class census if prescribing a broader owner move; log scan mode, coverage and raw record exclusions. The completed *runtime-subpackage* census/overlay is not that scan.
2. Choose/document default listen policy and explicit opt-in for remote binding with the owner if current configuration does not establish it. External ZMQ/OS socket semantics are authoritative contracts; no blanket compatibility ban may remove remote support.
3. On a real, fresh TCP viewer, assert both data and control listeners are loopback-bound for a loopback request; test an explicit remote-bind route and connection/reporting consistency. Exercise IPC, external-viewer reuse and failure cleanup. A mock asserting only constructor arguments is insufficient.
4. Gate completion on observed socket listeners and behavioral tests at the pushed SHA; review crossings with drafts #153/#154 and any Fiji equivalent. No code migration or CLI behavior is certified by this planning PR.
