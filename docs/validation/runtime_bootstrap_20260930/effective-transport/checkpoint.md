# PR256 effective execution transport correction

Parent original defect witness: source943898, platform-default IPC differs from
injected TCP client; observe also pings IPC. Original parent RST/script and all
native attempts remain unchanged. Mainc50f42c normally integrated before edits.

The existing OpenHCSZMQConfig.client_endpoint owns override/default resolution.
The connection projects through that owner with the supplied config; client
construction uses the same projection. Bootstrap resolves its public connection,
checks locality on the actual client endpoint before planning/writing/spawning,
and retains that explicit mode in its existing typed handle. Observation and
close derive from that connection. The catalog route passes its injected config.

No copied default, hidden mode cache, extra endpoint record, transport switch,
new lifecycle/launcher, installed edit or native allocation.
The raw no-config endpoint comparison cannot infer a subsequently supplied
nondefault config from an immutable spec; it must supply that config or use the
resolved connection. No global default is changed to make that check green.

## Exact source and tests

Production/test commit `3b78eb1fd56894a56573ed5130bf95b213a07cda`, normally
integrated main `c50f42c46fcee71c88bc5883850b1001bc00f212`. Paired ZMQ9 remains
`28d9ed6a0121ebb524ae37fd97de5355308bda7f`; metaclass remains448cdf07.

Source imports of openhcs, zmqruntime, polystore, metaclass_registry and
python_introspect verified under this worktree. Existing Python3.12 executable
`/home/ts/code/projects/openhcs/.venv/bin/python`, `-B`, explicit PYTHONPATH to
this root and all eight recorded child src directories, CPU-only/thread1,
existing shared Fiji cache/downloadfalse. No source override of installed tree.

Executed within a30s shell bound, with plugin autoload disabled:

```sh
python -B -m pytest --noconftest -o addopts= -q \
 tests/unit/agent/test_owned_runtime_bootstrap.py \
 tests/unit/agent/test_agent_services.py::test_execution_connection_spec_owns_zmq_endpoint_projection \
 --basetemp=docs/validation/runtime_bootstrap_20260930/effective-transport/pytest-b \
 --junitxml=docs/validation/runtime_bootstrap_20260930/effective-transport/source-tests-b.xml
```

**48 passed, 0 skips/deselections,4.05s; process4.65s,255392KiB peak RSS,
exit0**. Two warnings are disabled asyncio plugin configuration. Initial
46-case result3.48s/exit0 in `source-tests.xml` retained separately before URL
projection closure. The passing48-case result uses `source-tests-b.xml`.
Scoped Ruff undefined-name checks and git diff --check pass.

Six actual native-client endpoint comparisons cover configured TCP/IPC crossed
with omitted/TCP/IPC requests. Six start->observe->close source journeys use
the REAL canonical startup lock/reservation logic with fixture-local paths;
only spawn, availability/network probes and final shutdown are intercepted.
Every produced handle round-trips through the original nested dataclass decoder,
retains its explicit effective mode, and derives the SAME endpoint after the
observer configuration default changes. Guard tests reject effective locality
before plan resolution, any write or spawn; real TCP nonlocal rejection cannot
borrow platform IPC locality. Six catalog projection controls consume the
injected config exactly once without constructing a network client/preparation.
URL/control-pair projection shares the same endpoint owner, preserving existing
explicit-port errors; its new omitted-TCP test refuses all platform fallback.

## Parent original witness, not relabelled

Ran the UNMODIFIED parent `check_bootstrap_effective_transport.py` with the same
existing interpreter and15s shell bound.3 checks/0.004s, process2.55s,
223300KiB RSS, **exit1**: actual observe heartbeat route PASS; explicit IPC
override PASS; no-config raw comparison still FAIL. Capture in
`parent-witness.txt`. Original parent script/RST/receipts were not edited.

That last assertion projects `connection.transport_endpoint()` with canonical
default execution configuration, then compares with a client constructed using
a DIFFERENT nondefault configuration never supplied to the projection. An
immutable spec cannot infer that future argument. Correct comparisons are:

```python
connection.transport_endpoint(config) == connection.execution_client(config).endpoint
connection.resolved(config).transport_endpoint() == connection.execution_client(config).endpoint
```

The expected native endpoint is not changed in either comparison. Both API
forms are exercised for all six mode cases, and real service observation from
the original parent witness now pings its injected TCP route. New bootstrap
handles contain the resolved connection, so default-free later projections and
different observer defaults cannot silently select another mode. No ambient
config mutation, hidden instance cache or compatibility route makes the old
under-specified assertion green. Parent owns any adjustment of that diagnostic
call site; the source-live/installed workflow still requires separate proof.

## Current pattern review and limits

- IMPL-12/TIME-7: delete the client's copied host/port/mode default selection;
  the original OpenHCSZMQConfig.client_endpoint is the single builder. The
  connection and URL methods project that declaration. New default-policy or
  override behavior changes one owner, not an independent endpoint resolver.
- BOUND-2: no raw transport/schema map. Omitted mode is resolved at the injected
  config boundary, not request construction; the original nominal connection
  and handle fields carry it onward. No second record, registry or stored config.
- IDEN-8/IMPL-13: canonical reservation, process identity, spawn/close and
  uncertainty ownership remain unchanged. Locality admits the actual client
  endpoint, not a separately chosen platform route. No startup/shutdown replay.
- IMPL-4/AGENT-6: new public helpers have exact types and work through existing
  nominal owners. No NotImplemented leaf, getattr/type/string routing, mixin or
  extraction to evade size. Existing transport declarations supply behavior.

Original packaged GodClassExcess.snapshot/align, authenticated byte-for-byte
against pinned ratchet3b03785 and scoped ONLY to the two owner modules: native
client excess189 versus main181 (**+8**); service15 versus main0 (**+15**).
This is NOT a full structural ratchet, R1/all-detector NRA or clean-architecture
claim. Prior +32/+15 and subsequent +9/+15 checkpoints remain historical evidence.

Guard observed critical swap16.4GiB, RAM17.6GiB, /home25.4GiB; no waiver and
no native/heavy allocation or serial-slot claim. Only bounded provider-free
source checks ran. No sockets, JVM, GUI, provider, downloads or installation.
Attempts01/02/03 and their exact known/uncertain dispositions remain unchanged;
BLOCKED S1 is not resumed. Parent/Dirac ACK/viewer files and native config are
untouched. Changed config is OpenHCS runtime/zmq_config.py, not the shared ZMQ
config.py or core/config.py viewer declaration. Remaining full valid3D and
installed acceptance await noncritical resources and a distinct authorized run.
