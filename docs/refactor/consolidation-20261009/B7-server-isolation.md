# B7: an execution client reaches only a server it may use

**Head audited:** `openhcs` `main` at `625150118` (#1207); `zmqruntime` `main` at `dc327e6` (0.6.1). **Rules:** [00-RULES.md](00-RULES.md). **Origin:** both (the attach rule is zmqruntime's; the shared namespace and the launch are OpenHCS's).
**Shared abstractions.** *Builds:* `zmqruntime.EndpointLaunch` (where a server's code is, which process started it, who may use it) and the `EndpointAudience` family. *Uses:* `AutoRegisterMeta`, `WireMessage`, `ProcessIdentity`, `OpenHCSRuntimeImportAuthority`.

## What is wrong

**Nothing relates a client to the server it uses: a client attaches to whatever answers at an address, every OpenHCS process of one user shares one address namespace, and nothing ever stops a server whose starter is gone.**

How a client picks a server today:

- **One namespace per user.** `OPENHCS_ZMQ_CONFIG` is a module singleton, the default of 30 parameters. Its endpoint is data port 7777 and control port 8777. On Linux and macOS the transport is IPC, and `IpcTransportDeclaration.socket_path` (`zmqruntime/transport_modes.py:383`) maps a port to `~/.openhcs/ipc/openhcs-zmq-<port>.sock`. Every checkout, worktree and installed copy run by one user resolves the same file for the same port. On Windows the transport is TCP and the namespace is the machine's loopback ports.
- **Attach to whatever answers.** `ZMQClient._connect_locked` (`zmqruntime/client.py:1060`) takes the startup lock, and if the socket file exists it pings the control socket. Any reply with `ready=True` makes it an `AttachedEndpointConnection`. The reply already carries `process_identity` and `application`; neither is read. `connect_existing` does the same.
- **The only identity check is somewhere else and compares too little.** `EndpointApplication` is `(identifier, version)`. `ZMQClientService` (GUI and session) and the function-catalog client compare it after connecting. A plain `ZMQExecutionClient.connect()` (scripts, the benchmark harness, `ExecutionConnectionSpec.execution_client` for MCP) never compares it. Two worktrees have the same identifier and version, so the check passes between them anyway.
- **"A free port" is not reserved.** `DataControlPortPairAuthority.acquire` returns the first pair from 7777 up whose socket files are absent. It reserves nothing. Three harness sites and 9 test files call it and then build a client on that port.
- **Discovery scan.** `ZMQClient.scan_servers` pings a port range (`ports_per_server_type` = 10 per role) in the same namespace and returns every reply. The GUI server browser and `RuntimeServerService.scan` list them; `ZMQServerScanService` is what `test_zmq_browser_scan_service_discovers_ui_bridge_default_transport` exercises, against a `UiBridgeControlServer` bound in the user's real `~/.openhcs/ipc`.
- **UI-bridge descriptors.** The running GUI writes `ui_bridge_*.json` into one per-user runtime directory (`UiBridgeDescriptorDirectoryAuthority`), and `UiBridgeProcessAdvertisedDescriptorCatalog` also reads `/proc/*/environ` of every process for `OPENHCS_UI_BRIDGE_DESCRIPTOR_FILE`. An MCP client with no explicit descriptor takes the only live one, from any checkout. Requests carry `(identifier, version)` and an auth token. This is a client driving a GUI, not choosing an execution server; it is U4's and is recorded under Reassigned.

The three observed failures are one sequence:

- The parity test picks one port with `acquire` and keeps it for all 30 workflows (`tests/integration/test_cellprofiler_official30_zmq.py:201`).
- Each workflow builds `ZMQExecutionClient(port=port, persistent=False)`, which starts a server and terminates it at the end of the workflow. Between workflows the socket file is absent.
- A second process (another parity run, or any OpenHCS process on the default port, because `acquire` starts at 7777) sees the port free and starts its own server there.
- The first run's next workflow finds the socket, gets a ready reply and attaches. It now runs on code imported from the other worktree.
- When the other process ends, its server stops under the first run. `benchmark/openhcs_measured_run.py:297` reports "client entered without a connected endpoint" for the same collision seen from the other side.

`require_owned_server` exists in the harness (`openhcs_measured_run.py:305`) and would have refused; the parity path does not pass it. It stays: a measured run may still be given a port, and then needs a server it started.

Why a server lived 31 hours:

- `ExecutionTransportConfig.persistent` defaults to `True`. `ExecutionRuntimeLaunchPlan.spawn` launches a persistent server with `start_new_session=True` (its own session and process group), and `OwnedEndpointConnection.close_client(persistent=True)` does nothing.
- The server holds no reference to the process that started it. `serve_forever` loops until a shutdown request or a signal. There is no idle limit and no check on the starter.
- A non-persistent server is stopped only by its client's `disconnect()`. A client that is killed (a pytest timeout, an agent stopped mid-run) never calls it.
- The code is in memory, so deleting the worktree changes nothing. No stale group is running at this head to inspect; the cause is read from the code.

## Target

**The relation, declared once.** A server states its launch, and `ZMQClient` checks that statement at the one place a connection is established.

```python
class EndpointAudience(ABC, metaclass=AutoRegisterMeta):   # who may use a server
    def admits(owner, client) -> bool
    def orphan_stops(unfinished_work) -> bool
class OwnerOnlyAudience(EndpointAudience): ...    # a non-persistent server
class AnySessionAudience(EndpointAudience): ...   # a persistent server

@dataclass(frozen=True)
class EndpointLaunch(WireMessage):
    code_root: str            # directory the server's top-level package is imported from
    owner: ProcessIdentity    # the process that started it
    audience: str             # wire name, derived from the family registry
```

- `ZMQServer` holds its `EndpointLaunch` and reports it in every heartbeat (`PongResponse.launch`).
- `code_root()` is a classmethod on clients and servers. Its default is the directory the class's top-level package is imported from. OpenHCS overrides it on both with `OpenHCSRuntimeImportAuthority.current().import_root`, the root its child processes are already launched from, so a client subclass defined in a script or a test is still this checkout's client.
- **A client that starts a server** hands it the launch (`owner` = the client process, audience from `persistent`) and connects only if the server that becomes ready reports exactly that launch.
- **A client that attaches** (an occupied endpoint in `connect`, or `connect_existing`) is refused with `EndpointLaunchMismatchError` unless the server reports a launch, its `code_root` equals the client's, and its audience admits the client process. The error names both code roots and the owner.
- The check applies to endpoints on this host. A remote TCP host is an endpoint the user named; its paths and process ids mean nothing here.
- **Namespace.** `ZMQConfig.socket_root()` owns where socket and lock files live. `OpenHCSZMQConfig` derives it from the import root: `~/.openhcs/<first 8 hex digits of sha256(import root)>/`. Two checkouts no longer share addresses, so the refusal is the second line, not the normal case. `OPENHCS_SOCKET_ROOT` replaces the root for one process tree; it is read at each call, and child processes inherit it. An absolute `ipc_socket_dir` still selects an explicit directory.
- **Orphans.** The server checks `launch.owner` once a second in its message loop. When the owner is gone, an owner-only server cancels its work and stops; an any-session server stops once it has no running or queued execution.
- **Tests and harness.** `tests/conftest.py` sets `OPENHCS_SOCKET_ROOT` to a short private directory (one per pytest process, so per xdist worker). The harness uses `ZMQExecutionClient.with_private_server`, which takes its address from `TransportDeclaration.private_endpoint` (a new socket directory for IPC, the first unbound pair for TCP) and raises if the server does not start. `benchmark.openhcs_measured_run.measured_execution_client` is the one place the harness builds a client: private with no port, the named port otherwise.

Identity that must match: code location and owning process (through the audience). Version stays where it is: `EndpointApplication`, compared by `ZMQClientService`. A server edited after it started has the same root and version and is not detected; a source digest would be needed and no surface owns that.

Deleted (all **derived**: `private_endpoint` and `socket_root` now own the fact):

- the three `DataControlPortPairAuthority.acquire` + `ZMQExecutionClient(port=...)` pairs in the harness;
- the execution port the three official30 tests chose (`_free_zmq_port_pair` stays for viewer ports);
- the hand-built `Path.home() / ".openhcs" / "ipc"` in `viewer_endpoint_discovery.py`.

Behaviour removed: a measured run with no port and without `require_owned_server` no longer uses the shared default port 7777; it starts a private server (**contract**: this surface's ownership rule).

## Persisted state

Runtime only. Socket and lock files move from `~/.openhcs/ipc` and `~/.openhcs/tcp` to `~/.openhcs/<digest>/`; servers started before the upgrade are not found and are not reused. The saved `OpenHCSZMQConfig` preference keeps every field.

## Guards

`tests/unit/test_b7_server_isolation_guards.py`:

- Every `ZMQClient` method that assigns a connection calls a launch check (AST).
- No ZMQ endpoint code (`zmqruntime.transport_modes`, `zmqruntime.client`, `openhcs/{runtime,agent,core,pyqt_gui}`) builds a socket path from `Path.home()`.
- No module in `benchmark/` names `DataControlPortPairAuthority`.
- Client and server state the import root as their code root, including a subclass defined elsewhere.
- Each checkout has its own socket root, and the test run's root is private.

## Tests

- zmqruntime `tests/test_endpoint_launch.py`, with real server processes: two servers from two code roots, each client reaches only its own, and a client aimed at the other's address is refused with both roots in the message; an owner-only server refuses another process and a persistent one admits it; a server that reports no launch is refused; a server exits after its owner is killed (both audiences); a persistent orphan finishes its work first.
- OpenHCS `tests/integration/test_execution_server_isolation.py`, with the real launcher: the started server reports the launch its client handed it; a client of another checkout and a client of another process are refused at the same address and the server is unharmed; the server and its children exit after the owner is killed.
- Both orphan tests and the two-root test were run against the code with the check removed and fail there.

## New-case experiments

A new kind of server (a viewer, a bridge) that must not be shared across checkouts: today it would need its own check after connecting. After: it subclasses `ZMQServer` and its clients subclass `ZMQClient`; nothing else.

## Done when

- A client cannot hold a connection to a local server whose launch it did not verify.
- A server whose owner is gone exits without a request.
- The parity check passes 30/30 with no port chosen by the test.
- The guards pass; the structural ratchet and nra-r1 show no regression.

## Reassigned

| Item | Evidence | Belongs to |
|---|---|---|
| UI-bridge descriptor discovery takes the only live descriptor from any checkout | `ui_bridge_service.py:1563-1585`, `/proc` environment scan at `:1599` | U4 |
| The MCP resident-server socket restates the checkout digest and `~/.openhcs/ipc` | `openhcs/mcp/socket.py:48,61`; it should read `OPENHCS_ZMQ_CONFIG.socket_root()` | U4 |
| `connect` kills the listener of an unresponsive TCP address before starting its own server | `zmqruntime/client.py` `_kill_processes_on_port`; the process may be another session's | zmqruntime (L3) |
| The application version is compared after connecting, and only by `ZMQClientService` and the catalog client | `authoring/session/execution_client.py:202`; a plain client attaches to a same-root server of another version | U1 |
| `viewer_endpoint_discovery.py:212` names an undefined `ViewerEndpointDiscoveryResult` | ruff F821 at this head | U4 |
