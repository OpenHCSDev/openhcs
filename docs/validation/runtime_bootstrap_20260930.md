# Issue251 source bootstrap checkpoint

Implementation owner: Lovelace. Integration/installation/live owner: parent.
Reused clean PR250 tree on `feat/owned-runtime-bootstrap-20260930`, normally
integrated `openhcsdev/main` at `33ec405e1ec3ca1a11e285f821754715a90b5290`.
PR250's committed receipts remain preserved. Frozen installed233/86 tree,
managed skill, and blind native owners were not changed or contacted.

## Working source

- `RuntimeBootstrapStartRequest` requires an explicit port and the existing
  bounded control budget. `StartOwnedRuntimeCapability` generates ordinary MCP
  and `runtime-start-owned` CLI exposure through existing declarations.
- `RuntimeServerService` admits every projected native launch write through its
  injected `AgentPathPolicy` before canonical native startup. The normal context
  now passes its existing policy into this service too.
- `ZMQExecutionClient.runtime_launch_plan` owns native log/status filenames and
  projects data/store/cache/transport destinations from their original owners.
  `_spawn_server_process` consumes the same plan, not a second launcher.
- Paired ZMQRuntime adds exclusive startup to its existing client/lifecycle lock.
  It never calls attach, kill, replacement, readiness warming, or source dispatch.
  Its existing startup lock carries a PID+creation-time pre-bind reservation;
  no extra future or process registry. Existing process adapters capture native
  identity before their existing child reaper can release a PID.
- Paired metaclass-registry adds `create=False` to its existing cache path owner.
  No copied XDG/default/path registry. Existing creating callers are unchanged.
- Returned handle contains the exact child, connection, and launch artifacts.
  Observation checks native identity and `PongResponse.ready`, never ping alone.
  Failed reservation publication after spawn returns the child handle with
  `runtime_bootstrap_uncertain`, not absence or an automatic replay.
- First-use/pipeline guidance references capability declaration names and the
  canonical custom-function procedure. Bundled guidance explains explicit
  bootstrap before preparation and retains the pre-/post-dispatch distinctions.

## Executed evidence and boundaries

Source imports were verified inside this tree and its recorded local children
using `/home/ts/code/projects/openhcs/.venv/bin/python` with explicit PYTHONPATH.
No package/environment installation or download; Fiji existing shared root and
downloads false, CPU-only and thread limits1. Source shard:

```
python -B -m pytest --noconftest -o addopts= -q \
 tests/unit/agent/test_owned_runtime_bootstrap.py \
 external/zmqruntime/tests/test_owned_startup.py \
 external/metaclass-registry/tests/test_cache_path_projection.py \
 tests/unit/agent/test_progressive_authoring_context.py \
 tests/unit/agent/test_image_analysis_qa.py \
 external/zmqruntime/tests/test_startup.py \
 -k 'not actual_mcp_onboarding' --basetemp=<owned persistent scratch>/pytest
```

Checkpoint: **62 passed, 2 deselected, 12.02s**, process12.75s, peak279704KiB,
exit0. The two existing actual
MCP construction cases are explicitly deferred, not context-bound exceptions.
Mocks intercept spawn and endpoint probes; this is source-only, not a native,
installed, performance, or scientific readiness claim. Two pytest warnings
refer to disabled asyncio-plugin configuration. Initial collection mistakes
and one read-only fixture-property assignment were corrected; no native call
was dispatched by these failed tests.

Durable captures: `runtime_bootstrap_20260930/source-tests.txt` and
`source-test-resources.txt`. Owned scratch:
`/home/ts/.cache/agent-scratch/runtime-bootstrap-20260930`, small fixture-only
paths, no biological/UNKNOWN material. Initial guard /home20.6GiB RAM13.4GiB,
historical swap-only warning13.2GiB. No shared live validation slot acquired.

## Pattern review, scoped not global proof

- **IMPL-7 / MEMB-2:** startup and observation are distinct request declarations,
  not an action bag or a second tool inventory. New-case witness: capability
  contracts and CLI projection are discovered from the declared leaf.
- **IMPL-12 / IMPL-13:** native spawn stays in the existing ZMQExecutionClient
  owner; the service uses its launch plan and canonical transport/client startup
  authority. No copied subprocess launcher or alternative preparation future.
- **BOUND-1 / BOUND-2 / TIME-7:** generic dataclass decoding round-trips the real
  nested handle. Owner-derived path admission and symlink sentinel witnesses
  reject before spawn. Cache/XDG/default resolution stays with existing owners.
- **IDEN-8:** exact ProcessIdentity is captured from the native handle, retained
  through pending observations, and compared against the heartbeat. A different
  creation time cannot become readiness or trigger takeover.
- **IMPL-4:** nominal EndpointProcess implementations and existing source test
  doubles supply the new identity contract; no default NotImplemented leaf.

Review covers changed startup/service/declaration/path/guidance source and
focused tests, not a complete NRA scan or a global no-debt claim. No scientific
recipe, biological default, or QA gate changed. Parent issue254's callable
artifact documentation/test remains untouched.

## Remaining acceptance

Parent releases the serial slot after blind freeze. Then run an actual bounded
native/MCP synthetic startup -> observe exact readiness -> catalogue preparation
READY -> single registration -> original compile/execute -> existing supported
owned cleanup. Prove denied/occupied/foreign routes before dispatch, endpoint
pair races and timeout/uncertainty disposition, ordinary <=10s observations,
and actual generated MCP/CLI entrypoints. Installed acceptance follows parent
review, paired dependency integration and offline installation. No Closes251
claim from this source checkpoint. Existing startup does not optimise cold
catalogue preparation; the retained110.5s predecessor remains a limitation.

## Source hardening checkpoint

Normally merged current main `32d070c261d9bcfeb2354b70203f79a71d15ce40`
after initial draft publication. No production/doc/test edits to parent254's
owned files. Paired drafts: [ZMQRuntime9](https://github.com/OpenHCSDev/ZMQRuntime/pull/9)
and [metaclass-registry1](https://github.com/OpenHCSDev/metaclass-registry/pull/1),
the latter pinned448cdf07e0a0b513a9c9a8f67e896f601da11771.

The existing native startup locks now reserve both data/control addresses in
stable order. A pre-bind second launch whose data address overlaps the first
child's control address rejects before spawn. Reservation first transfers from
the invoking process to the exact child; a publication failure retains an
active reservation and uncertainty handle instead of inviting a replay.
Deadline expiry rejects before spawn. Canonical child launch uses Python `-B`
so it does not introduce unadmitted source bytecode writes.

Source-only real CLI parser -> typed request -> tool-call projection passes
using the existing positional port contract; no call is sent. Existing authoring
and core surfaces include startup/observation from the leaf's FUNCTION_AUTHORING
metadata, not a profile roster edit. The same readiness facet now reaches the
custom-function context too, without another guide or changed QA/bounds.

Final focused shard **66 passed, 2 actual MCP cases deselected, 11.85s**,
process12.55s, peak280400KiB, exit0. Durable receipts:
`runtime_bootstrap_20260930/source-hardening.txt` and
`source-hardening-resources.txt`. Scoped undefined-name checks and diff-check
pass. The existing gateway's missing DebugPausedWorkerStatus annotation import
was closed in its own module, not bypassed in reflection.
Latest actual guard /home20.4GiB RAM11.0GiB; historical swap13.3GiB is the only
warning. No native/MCP validation or installed mutation. Remaining live gates
above still apply; source pair-reservation tests are not cross-process live proof.

## Focused structural census

Executed current skill `debt_census.py` on the committed OpenHCS production diff
from current main32d070c26 tobe47d9f63, and the paired ZMQ production diff from
0f9e840a9 tob7f6f5d22. Zero growth in string/type dispatch and arms, codec
subclasses, raw string-key subscripts, getattr/default probes, and foreign
absence probes in both scoped diffs. This is a candidate screen, not a global
NRA ownership proof. Native diff adds one JSON decode at the existing transport
startup-lock boundary, one broad catch that preserves the exact spawned child
as uncertainty (never absence/kill/retry), and one long canonical exclusive
startup method. Those are inspected owner decisions, not silently reported as
zero debt. OpenHCS adds231 code lines, native114; ordinary optional-plan/socket/
heartbeat checks add three None predicates in each scope, no string dispatch.
Captures: `source-census.{txt,json}`, `dependency-census.{txt,json}`.

Frozen dependency pins for parent review:
ZMQRuntime `b7f6f5d22f44a24878314192d4d32963b8423c04` (draft9),
metaclass-registry `448cdf07e0a0b513a9c9a8f67e896f601da11771` (draft1).
Parent can release the finite native journey after blind freeze. No live worker
handle was started; all source-test commands are terminal. Owned fixture scratch
was1.8MiB and is disposable after retaining these receipts.
