Strict generated MCP arguments: issue484
=======================================

Owner and source boundary
-------------------------
Planck owns implementation in PR485. Parent retains integration. Dewey's
H004/PTY483 and Root394 source/runtime plumbing are untouched.

Reused finished checkout: /home/ts/wt/openhcs-basicpy-readiness-20260929.
Previous branch217 was merged, tracked source was clean and the bounded
open-file borrower check found none before reuse. Mainb4405ff3541add6b91004002b7d6f389f1208636
was merged normally into original PR485 head36fb9fc55e3223164d6b257c3c33721b4b4f307c;
prepatch checkpointbc174beedc79e8e2e1fbb5475d417f03af772d04.
Pre-existing external gitlink/worktree differences were reviewed and retained,
not updated or staged. No new worktree, environment or dependency download.

Ownership decision
------------------
The FastMCP-generated Pydantic argument class remains the one argument owner.
Its fields come from the existing polymorphic capability/request declaration
and function signature. Its original model validator now rejects extra keys.
The existing Tool.parameters view is regenerated from that same model.
No new registry, parser, model copy, key whitelist, connection alias, dispatch
guard, retry or version-compatibility change was introduced.

Eight production lines at the one build_server.openhcs_tool registration seam
configure the existing model before it can serve calls. Public registration
is retained, including a supplied FastMCP transport factory. The SDK's
declared ToolManager.get_tool retrieves its original model; we do not patch
ArgModelBase globally or alter unrelated SDK users. The dependency remains
MCPv1 as declared by this project's existing pin.

Applicable catalog: BOUND-1, BOUND-3 (strict decode through the declared model,
not a hand-maintained exact key set); TIME-9 (no alternate nested wire form).
No authored codemod-body equivalence or complete NRA detector scan is claimed.
This is a scoped exact patch supported by existing audit tooling and the live
installed path, not a new scanning/refactoring framework.

Complete consumer-family evidence
---------------------------------
Existing refactor-audit Package.load/ParsedModule covered703 OpenHCS production
modules and19 actual paired FastMCP modules; zero parse omissions. The original
AST report contains144 named declaration/consumer/owner-access sites and is
retained as H002-484-AST-BEFORE.json under the parent issue-batch root.
Dynamic callback resolution was read semantically; AST is not behavioral proof.

All nine MCP binding families converge on this one registration seam:
no-argument, UI-connection, UI-request, scalar, UI-scalar, config-patch,
from-fields, dataclass-request and viewer-request. Both explicit subclasses
and declaration-generated bindings use it. Registry-resource projections use
their original resource protocol, not a second tool-argument decoder.

Determining SDK consumers are Tool.from_function -> FuncMetadata.arg_model,
ToolManager.call_tool -> Tool.run -> call_fn_with_arg_validation ->
arg_model.model_validate -> model_dump_one_level. SDK list_tools reads the
existing Tool.parameters. Both runtime rejection and advertised schema derive
from the SAME model; only input models change, not output models or arbitrary
dictionary-valued arguments. Adding a capability/parameter requires only its
original declaration, with no extra membership or strictness roster edit.

Installed acceptance before focused tests
----------------------------------------
Ordinary offline wheel: openhcs-0.8.7-cp311-abi3-linux_x86_64.whl.
Private target: parent issue-batch/engineering484/installed. Installed server.py
byte-compares equal to changed source. No frozen463/465 installation was edited.
Original stdio entrypoint: paired Python -B -m openhcs.mcp, source verified by
public health. Actual engineering serverPID874584; no native/viewer launched.

The installed journey passed: all84 exposed tools advertise
additionalProperties=false. Valid flat host127.0.0.1/port6014/TCP/persistenttrue
is stored and retrieved unchanged in session-1. A nested undeclared connection
isError/extra_forbidden before parsing its deliberate failure source, and no
session-2 exists afterward. A sibling no-argument tool rejects an extra key.
Intentional omitted routing retains the original declared defaults and next
valid creation is session-2, proving invalid input did not create a session.

Original strace of the entire helper plus installed child contains ZERO connect
syscalls. No foreign peer/control runtime was contacted. No compile or science
tool was sent. SDK EOF closed the engineering child; its PID is absent and exact
live03 scope inactive. Each build/install/live scope had1GiB MemoryMax,
MemorySwapMax0, one CPU. No broader fleet or desktop mutation occurred.

Two earlier observer/fixture failures are retained honestly: the observer used
the wrong health-field name; then an explicitly None PipelineConfig fixture
was correctly rejected. Neither sent compile/science. A source-checkout test
attempt stopped at old external zmqruntime import before collection; those
submodules were not changed. The corrected focused batch runs the byte-equal
ordinary installed wheel with the original test/conftest files in importlib
mode, preserving installed dependency ownership.

Initial focused batch:5 passed,294 deselected,10.77s. It verifies every registered
argument model rejects unknown parameters before invocation, flat/default
source routing, configured transport factory and both progress thread policies.
Full299-test module/hostedCI is not claimed or used as an integration hold.

Retained original acceptance files under parent issue-batch/engineering484:
INSTALLED-JOURNEY-journey03-RESULT.json
 SHA2562c173d21ab9766721ace0efc49b35cd0aa7fa6677c194a4dd3cdf8d10df92a41
installed-public-journey03.jsonl
 SHA256b8983ff15eb1aaf830ddd1edfea7c5fccaf86a30b13e40c0e33482a0dd087dc1
endpoint-syscalls03.strace
 SHA25626872ce55cd4df3dc6eb3fb261e0cb36b56143022199bb363fecdcaf930e60df

Biological/scientific acceptance is outside this repair. Original H002 failure
and old5690/retinal viewer custody remain unchanged; no scientific hints were
sent. Parent may qualify/install/merge this exact working checkpoint without
waiting for hostedCI, then independently authorize any new development attempt.
