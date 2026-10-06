# Custom-function admission and responsive preparation (#230)

Implementation owner: Lovelace. Integration/install owner: coordinator.
Draft PR233: https://github.com/OpenHCSDev/openhcs/pull/233
Source: /home/ts/wt/openhcs-custom-function-admission-20260929.
This checkpoint normally integrates main240/3032958ac at d33128916, following
main238 integration f5dbebb27 (main01d1a8c55c). Recorded PolyStore1209068 is
unchanged. No installed tree is edited.

Latest source follow-up after4c6fbac0a: destination proof and source dispatch
now use existing connect_existing, never attach-or-start/replacement. Each
reuses the existing operation/control deadline for attachment and the one
control exchange. Eight absent/unresponsive endpoint cases exercise the actual
attach-only method and assert zero start, kill and source/control sends;
two expired-deadline cases reject before attachment. Current focused shard:
**57 passed,25 deselected,7.22s**, process8.04s,peak309668KiB,exit0.
Receipt: tests/runtime_diagnostics/registration_attach_only_20260929/.
Full startup-lock contention boundedness is not claimed: the recorded dependency's
attach-only method has no operation_deadline parameter for that existing lock.
The control/send deadline still prevents delayed lock acquisition from later
dispatching source after budget expiry. No duplicate lock/lifecycle was added.

## Working source

Registration requires an explicit reflected ExecutionConnectionSpec port, also
for ephemeral source. Persistence requires the deliberately authored function_name
and caller-intended absolute storage_dir. Existing AgentPathPolicy admits the
directory and Manager.source_path_for_name before client creation. A read-only
native destination request verifies that endpoint's actual Manager-owned store,
exact file, and ProcessIdentity (PID plus creation time), without evaluating source
or starting catalogue preparation. Unsupported or mismatched destinations reject
before source dispatch. The native service repeats caller/native write admission
before evaluation and atomic persistence. Post-write receipt checks are not admission.

Cold catalogue/kernel warming belongs to the existing native FunctionCatalogPreparation
future, cancellation and supervised child from #238. New typed start/status/cancel
requests and nominal control strategies project that same owner promptly. They add
no process launcher, future store, cache roster or warmup registry. The handle is the
explicit connection plus native process incarnation; stale owners reject. Cancellation
signals that owner without joining inline; status observes terminal cleanup.

Registration performs one bounded destination/readiness observation under the existing
control deadline. NOT_STARTED, PENDING, CANCELLING, FAILED or CANCELLED rejects before
any source-bearing registration RPC. The native mutation handler likewise refuses
cold source without initiating warming. Only READY permits one _send_control_request.
The previous mutation resend loop and inline catalogue polling were removed in place.
After source dispatch, timeout/error/malformed receipt stays uncertain; no replay,
fallback or timeout inflation. Pending preparation cannot write later on behalf of
a registration call whose observation expired.

EndpointFunctionCatalogServiceABC composes the catalogue contract with these three
typed preparation operations; ZMQFunctionCatalogService implements it. Capabilities
use the context's typed endpoint_function_catalog dependency, not undeclared methods
on FunctionCatalogServiceABC. Normal factory and raw local MCP contexts share one
endpoint service for catalogue and preparation. Explicit endpoint injection is
supported. Hosted contexts retain explicitly injected native FunctionCatalogService;
compiler/server native catalogues acquire no second future. No NotImplemented stub,
getattr cast, isinstance dispatch, or second function registry was added.

The canonical custom-function-authoring how-to now explains explicit routing,
controlled-launch Manager destination lookup, start/status/cancel handle fields,
READY-only mutation and precise postdispatch uncertainty. The knowledge manifest
summary/tags track this; document digests remain derived, not duplicated.

Bundled SKILL.md and first_use/pipeline now point to that same existing responsive
preparation procedure before first cold function search. One nominal context
section shares the existing first-use/pipeline facets; capability names derive
from declarations. No duplicated guide, inventory or biological hints. Actual
default-context/generated MCP read-only calls reach the full canonical guide and
typed preparation capability without any endpoint-client creation. Ten source
checks pass8.20s, peak308356KiB; skill validator passes. Two existing whole-context
bound checks remain failing on unchanged image_analysis_workflow (17387chars),
also17387 with this section excluded; they are explicitly excluded from the
focused passing shard. This is not all-context readiness or installed proof.
Receipt: tests/runtime_diagnostics/registration_onboarding_20260929/.

## Actual evidence (source, not installed acceptance)

After normal main240 integration,16 focused attach-only/deadline, real context
composition and single-send cases pass5.53s (process6.41s,peak293380KiB,exit0).
Both existing abi3 extensions built through setup.py build_ext --inplace
--parallel1 with owned temporary objects/lib:2.55s,peak146140KiB,exit0.
Imports prove source _granularity_reconstruct (45440bytes) and _tabular_native
(210808bytes), plus reviewed OpenHCS/PolyStore paths. No installation/dependency
download/JVM. Durable receipts:
tests/runtime_diagnostics/registration_main240_tests_20260929/ and
tests/runtime_diagnostics/registration_main240_build_20260929/.

Current focused provider-free shard: **47 passed, 25 deselected, 7.32 seconds**;
process elapsed8.13s, peak305992KiB, exit0. Existing shared Python, explicit reviewed
worktree plus eight submodule src paths, pinned shared bundle/downloadfalse,
threads1, plugins/conftest disabled, nonblocking validation lock.
OpenHCS and PolyStore imports resolve in this tree. Two warnings are disabled
async-plugin configuration options, not failed tests.
Receipt: tests/runtime_diagnostics/registration_readiness_20260929/.

This shard covers all registration/admission cases, five Manager filename-owner
interceptions, generated MCP controls, real default/raw/explicit context construction,
responsive pending start/status/cancel with a controlled future, stale incarnation
rejection, failed preflight zero mutation, native cold-registration rejection, one
source-bearing client RPC on ready/pending/timeout, and #238 readiness/error propagation.
The controlled pending unit future is not the actual 53-second cold kernel job.

Historical source checkpoints: 94 cases passed10.41s/323352KiB before newer merges;
23 cases passed6.18s/287876KiB after234; five filename cases passed3.02s/183520KiB at
c10bb3f85. These do not substitute for current live or full-suite evidence.

The standard existing source abi3 extension was built with setup.py build_ext
--inplace --parallel1 and named owned build-temp/build-lib: **1.48s,93004KiB,exit0**.
Import receipt verifies the source binary45440bytes and source/binary hashes:
tests/runtime_diagnostics/registration_native_build_20260929/.
No install, build-dependency download, CellProfiler skip or replacement registry.
Installed225 already contains its own compiled extension; the previous absence
was in this source-only test tree, not a proved installed dependency defect.

## Preserved failed live predecessor

At exact81e636ad4, attempt01 used ordinary stdio MCP and three owned headless
synthetic endpoints. Health/context, missing-route, outside/file/ancestor symlink,
foreign store and unsupported-proof checks passed; protected sentinel was unchanged,
foreign/unsupported audits had zero source-bearing registration RPCs. Positive
call11 expired at10.011s and remained uncertain. Native audit showed automatic
mutation resends while cold preparation was pending. Same-handle read-only observation
exposed the unbuilt source extension. Compilation/execution and delayed acceptance
were not reached. This is **failed source-live evidence**, not acceptance.
tests/runtime_diagnostics/registration_live_20260929_attempt01/ retains original
arguments, failure, native control journals, stderr and close-owned disposition.
MCP and all three native handles are terminal; each server returned0, identities
were verified and the lock released. Original H002033 and foreign saved side effect
are preserved and never replayed. No science, shared7777 contact, GUI or JVM.

Attempt02 at exact4c6fbac0a is also preserved as accepted=false. Ordinary MCP
start returned0.020s;91 preparation-control observations stayed below0.027s.
Stale cancellation rejected; pre-ready native source-bearing register count
was exactly0. The diagnostic's redundant100s preparation sub-budget expired
while the future was pending; this was not a tool timeout or hung MCP.
Same-handle read-only observation subsequently returned READY: native progress
timestamps1790725945.1608434 to1790726055.660598 (~110.50s). The supervised
child was absent; MCP and all three native endpoints were closed by verified
owner identity, returncodes0, runtime_terminal=true, lock released. Source and
all original calls stayed frozen until closure. No mutation, compile or execution
occurred. Slow real cold warming remains a limitation, not an optimisation claim;
parent owns additional warmup diagnosis.
Receipt: tests/runtime_diagnostics/registration_live_20260929_attempt02/.
The next fresh journey removes redundant100s preparation/45s job subcaps,
retaining the existing single240s total journey gate and unchanged10s per-call
observation cap. Cold, compile and execution stage costs are recorded separately.

## Focused architectural audit

Scope: changed production declarations, callers and source tests; no full NRA scan
or global proof. Actual catalog witnesses:

- IMPL-4: endpoint preparation contract now owns all three methods. Default/raw/
  explicit MCP construction cases execute the generated controls; native compiler/
  hosted catalogues remain their own complete family, with no dummy method bodies.
- IMPL-13: start/status/cancel extends the one native future/cancellation/child.
  Repeated start coalesces the exact future/thread; failed readiness sends zero
  register RPCs. Mutation no longer borrows the discovery retry mechanism.
  Registration and destination proof now consume the existing attach-only
  lifecycle, not a caller-side replacement implementation. Eight absent/
  unresponsive cases and two expired-budget cases guard the route closure.
- IMPL-12: Manager.source_path_for_name owns save/admission, named reads/deletes/
  updates, require_source and rename destinations. Five interception cases prove
  those operations cannot bypass it. Directory enumeration reads real files and
  remains enumeration, not a companion filename roster.
- MEMB-2/MEMB-3: control/capability membership derives from existing declarations;
  each new request leaf owns its operation/strategy. A new case extends that family,
  not an action switch or hand-maintained catalogue.
  The shared onboarding section similarly uses existing nominal context facets;
  first-use/pipeline reachability tests exercise registry-derived rendering and
  typed capability discovery, not duplicated string-kind membership.
- IDEN-8: one handle and destination token reuse ProcessIdentity; changing creation
  time while retaining PID rejects before cancellation/evaluation.
- BOUND-1/BOUND-2/BOUND-6: existing typed request/response codecs decode at control/
  MCP boundaries; native Manager and AgentPathPolicy remain path/write authorities.
  No second destination resolver or source-code name parser.
- TIME-1/TIME-5: replaced registration polling was deleted in place. Existing
  catalogue polling remains read-only discovery, not a legacy mutation path.
  Delayed/unsupported fault injection lives only in the diagnostic driver.

## Remaining live gates and resource bounds

The diagnostic now freezes the reviewed source SHA and submodule pins, starts three
headless fixture endpoints with native threads1, limits each observation to10s and
the journey to240s, acquires nonblocking validation.lock, and rechecks actual RAM/
disk plus scratch<80MiB before dispatch. It asserts **zero source-bearing register
RPCs before READY and exactly two total** (initial positive plus controlled delayed),
not merely one persistence marker. The complete journey is registration/discovery/
compile/execution of an8x8 plus-three synthetic function, escaping-path sentinels,
foreign/unsupported predispatch denials and same-handle uncertain receipt reconciliation.
It also sends one stale-incarnation cancellation request while observing the
owned preparation, then retains that same valid handle until READY. Pending
valid cancellation/terminal cleanup is covered by the controlled source future
test; it is not claimed live from a cancellation attempted after readiness.

--installed-entrypoint mode requires PYTHONPATH unset, cwd outside SOURCE, actual
OpenHCS/PolyStore imports matching the reviewed installed source, and the ordinary
McpDevServerSpec. It is implemented but not live-proved. Source mode is explicitly
labelled source_live_not_installed. Parent owns final merge/install and installed
acceptance; no frozen installation changes are authorised here.

Latest actual guard /home19.8GiB,RAM13.1GiB warns about disk plus historical swap.
No new native journey starts while that non-swap warning remains. Attempt02,
the57-case source follow-up, main240 build/shard and onboarding source checks are
terminal and released the lock. Next is the authorised finite cold source-live
journey after a fresh passing non-swap guard/nonblocking lock, then parent review/merge and
installation of this same frozen tree (no extra checkout). No optional hosted
CI wait or installed readiness claim.

Owned disposable build objects136KiB, filename-test fixtures40KiB and current
source-test fixtures328KiB were removed after retaining receipts. They are reproducible
from the tests/build command; the source in-place extension remains for acceptance.
Original attempt01 synthetic scratch remains identified separately from receipts/UNKNOWN input.

This draft references #230, #238, #233 and does not claim Closes acceptance yet.
Broad #206/PolyStore16 scope and its26 combined-suite failures remain in their separate
trees/PRs; no ROI profile or preservation pass is invented. Ordinary write admission
is not a Python sandbox or proof against hostile remote servers/filesystem races.
