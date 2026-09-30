# Memory/session issue batch: #131 and #169

Implementation owner: Linnaeus. Integration and installed/live validation owner:
the OpenHCS coordinator. Worktree: `/home/ts/wt/openhcs-memory-session-20260929`.
No saved H001 files, Euler inputs/results, installed source, or shared main were
opened or modified. No GUI, JVM, GPU workload, provider or execution server was
started by this worker.

## #169: declaration and runtime ownership

An unpublished NumPy-decorated function reproduces `TypeError: cannot pickle
'_thread._local' object` in both `dill.dumps(function)` and a real ObjectState
history export. Its `__globals__` belongs to `arraybridge.decorators`, while its
declaration module belongs to the source execution namespace. Dill therefore
serializes decorator globals by value, including `_thread_gpu_contexts`.
Published importable functions and plain current global/UI/pipeline configuration
history do not reproduce the failure. This is a reproduction of the reported
failure mode, not reconstruction of the disposed H001 in-memory graph.

The existing ArrayBridge `ThreadGPUContext` now owns its thread-local storage.
Decorator globals carry the importable runtime owner, not its runtime handle.
There is no history filtering, alternate registry, permissive pickle handler,
legacy reader, or change to ObjectState's durable document format. The obsolete
global storage and forwarding function are deleted. GPU invocation uses the
same context/stream behavior through `ThreadGPUContext.current()`.

Regression coverage includes unpublished CPU/GPU-decorated callable persistence,
stable isolated per-thread contexts, and a continuous native document/history
save, fresh-registry load, historical undo and return to current declarations.
The retained runtime context is populated with an unpickleable thread-local
handle and must remain alive and identical. The native history test uses real
pipeline document, scope and ObjectState owners; it is not desktop live proof.

The minimal repaired callable round trip executed successfully (14,424-byte
payload); its restored NumPy result was `[0, 1]` for thresholding `[1, 4]` at 3.
The paired upstream's three focused decorator/context tests passed (0.15s),
and changed-source Ruff/diff checks passed. OpenHCS source validation passed:

- 12 tests (15.61s): the native durability regression, memory diagnostic tests
  and existing `test_pipeline_history_occurrence_restart_regression.py`.
- 6 tests (3.16s), after the ownership revision: five diagnostic regressions
  and `test_durable_decorated_history.py`.

The first native test assertion omitted normalized processor default kwargs;
it now compares the complete declaration captured before persistence against
the restored declaration. Snapshot identities and historical execution remain
asserted. The real desktop journey is still pending. Paired upstream
draft: https://github.com/OpenHCSDev/ArrayBridge/pull/1.
H001 was already closed by explicit owner disposition;
there is no request or authorization to recover its lost history.

## #131: bounded retention diagnostic

`openhcs/mcp/memory_diagnostic.py` constructs the real full-surface OpenHCS MCP
server and reserves the actual stdio transport. One harness-only tool samples
that disposable process, optionally after `gc.collect()`. It does not replace
the UI, application, capability services or protocol path with mocks, and does
not add a diagnostic capability to production MCP.

The receipt records PID, monotonic time, RSS, PSS, private clean/dirty, swap,
threads, imports/native libraries/frameworks, catalog/custom declarations and
ObjectState snapshots before/after every operation and after full GC. Repeated
read-only health/authoring/capability queries are measured after a separate
warm-up round. Optional `--sequence-json` decodes 1..16 requests through the
existing `McpDevToolCall` owner and admits only `AgentCapabilitySpec.read_only`;
it does not introduce a second capability registry. The JSON report retains the
exact request sequence and typed sample events (`events[].receipt`).
Per-round slopes describe this sequence only. Flat measurements
cannot prove catalog/compile/custom-source/execution/GPU/JVM paths leak-free;
positive slopes alone cannot establish causation or a leak.

Run only with the validation slot and at least 8 GiB available RAM:

```sh
flock -n /home/ts/wt/openhcs-issue-batch-20260929/validation.lock \
  /home/ts/code/projects/openhcs/.venv/bin/python -m openhcs.mcp.memory_diagnostic \
  --rounds 4 \
  --scratch-root /home/ts/.cache/agent-scratch/openhcs-issue-memory-session-20260929 \
  --output docs/validation/mcp-memory-receipt-20260929.json
```

Set `PYTHONPATH` to this worktree and its recorded submodule `src` directories,
and verify imported paths before running. The diagnostic owns temporary XDG
data/cache/config and stderr under
`/home/ts/.cache/agent-scratch/openhcs-issue-memory-session-20260929/mcp-*`.
Each run removes that disposable directory on success or failure, retaining the
JSON receipt and bounded stderr tail at the requested output path. The harness
enforces an 8 GiB available-RAM floor, 2 GiB server RSS budget and 180-second
overall timeout.
The diagnostic has no access to another server's process lifecycle; transport
teardown affects only its own fresh subprocess. No services or tmpfs data are
removed to influence results.

No real MCP measurement has run yet. There is no leak or no-leak finding at this
checkpoint, and the source tests do not substitute for that run.

## Catalog-pattern review and new-case ownership check

The comparison baseline is OpenHCS checkpoint `7a76b57d3`; review covers the
changed diagnostic, native history regression and paired ArrayBridge change.
This is focused source/AST/catalog review, not a full NRA proof or repository
audit. The current archived refactor-audit catalog supplies the pattern IDs.

- **BOUND-2 / BOUND-1:** baseline `diagnose.sample` returns a raw mapping even
  though `ProcessMemoryReceipt` already declares its exact shape. Health reads
  also bypass `McpServerHealthResult`. `MemoryDiagnosticMcpClient.sample()` now
  decodes once with the existing `python_introspect.dataclass_from_mapping`
  mechanism into `ProcessMemoryReceipt`; health uses its existing DTO. Samples,
  events and reports stay typed. Linux `/proc` field parsing and the inherited
  child environment remain legitimate external boundaries, not violations.
- **BOUND-2:** baseline `call()` separately classifies wire `isError` and payload
  `.get("status")`, alongside `McpDevToolResult.has_errors()`. Source review of
  that owner confirms it already owns transport and structured agent errors.
  The diagnostic now calls only that owner; it does not restate a status roster
  or add another failure contract.
- **MEMB-2:** baseline slope selection spells a tuple of four field names and
  `retained_slope_kib(Sequence[dict], field)` reads each by string. Eligibility
  and projection now live in `RetentionMetric` metadata on receipt fields;
  `ProcessMemoryReceipt.retention_slopes()` derives selection from those
  declarations. The standalone string-dispatched slope helper is deleted.
- **MEMB-1:** the hand-written framework roster mixed array frameworks with
  SciPy/JVM packages and omitted an existing ArrayBridge member. Array-framework
  observations now derive from `MemoryType` and its `loaded_module()` behavior,
  without importing an optional framework. All native library paths and total
  module counts remain recorded; this is not comprehensive JVM/GPU attribution.
- **Runtime versus durable owner:** paired ArrayBridge code moves the handle
  onto the existing importable `ThreadGPUContext`, deleting the module-global
  thread-local and forwarding function. No second store, pickle fallback or
  history exclusion is added. The native regression exercises retained callable
  history while an unpickleable runtime handle remains alive.

`scripts/check_mcp_memory_ownership.py` is a bounded AST regression guard, not a
general detector. Against `7a76b57d3` it reports five literal mapping reads plus
one duplicate status classification (six findings); against the revision it
passes. The baseline's variable-key slope helper was additionally reviewed
directly, not counted by this guard.

The new-case test adds slope eligibility to the previously unmarked
`private_clean_kib` field on a receipt subclass. It decodes the same JSON shape
and obtains the new slope without changing the MCP client, metric selection,
report or a registry. Only the field declaration changes. Separate tests reject
unknown fields, boolean-as-integer input and mutating request sequences.

Lightweight repeatable audit commands:

```sh
/home/ts/code/projects/openhcs/.venv/bin/python scripts/check_mcp_memory_ownership.py
git show 7a76b57d3:benchmark/mcp_memory_diagnostic.py | \
  /home/ts/code/projects/openhcs/.venv/bin/python scripts/check_mcp_memory_ownership.py --stdin
```

The second command intentionally exits 1 and reports the original violations.

## Independent review correction: admission and source authority

Review: https://github.com/OpenHCSDev/openhcs/pull/208#issuecomment-5897134270,
against `dd5f177f0c381ebac1d470f9a05f8423c2c40dfb`. Latest main
`283b21275553c54261cf9aeedb7374c113d07f2b` (including #212) was fetched and
merged normally as `32decce9af2b7b4f51aa3dc8de39b4e0e58c5694` before correction.

- **BOUND-2:** diagnostic admission now queries `capability.read_only`, not
  either of its component fields. The new-case test changes only an existing
  typed capability declaration to `mutating=True, side_effects=()` and proves
  rejection without a consumer edit or registry. Integrated artifact-plan
  inspection is also rejected using its actual current declaration from #212.
- **IMPL-13 / BOUND-2:** `DiagnosticServerSpec` inherits the exact-root launch
  projection from `McpDevServerSpec.process_args()`, which already delegates to
  `OpenHCSRuntimeImportAuthority`. It adds only the instrumentation flag and
  owned XDG isolation. Bare `-m` child launch and ambient PYTHONPATH copying are
  deleted. The entrypoint moved under the supported OpenHCS module namespace;
  the old benchmark module is deleted, with no alias or second launcher.
- Observed diagnostic/OpenHCS paths are one `DiagnosticSourceIdentity` in every
  typed memory receipt. The MCP client checks both against its parent authority,
  independently of the existing health PID/staleness checks. This receipt records
  observations, not a second import-root authority or source registry.
- `--source-identity` reports those same source observations and exits before
  importing the application client or constructing a server. Client launch
  declarations live in `memory_diagnostic_launch.py`, so lightweight provenance
  inspection does not import that client/scientific dependency graph. A new
  diagnostic subclass extends the existing module/argument/environment hooks,
  not a copied import bootstrap or a changed shared launch owner.

Focused regression command, using the existing Python 3.12.3 venv with explicit
worktree/recorded-submodule source paths verified first:

```sh
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 OPENHCS_CPU_ONLY=true OPENHCS_HEADLESS=true \
  /home/ts/code/projects/openhcs/.venv/bin/python -m pytest \
  --noconftest -c /dev/null -p no:cacheprovider \
  --basetemp=/home/ts/wt/openhcs-memory-session-20260929/.validation/review-5897134270 \
  tests/unit/test_mcp_memory_diagnostic.py tests/unit/test_runtime_import_authority.py -q
```

Result: **15 passed in 4.34s**. This excludes application cleanup/Qt fixtures and
plugin startup; it does not replace full application acceptance. Two tests launch
the actual diagnostic entrypoint with normal server-spec arguments plus
provenance-only mode, from a competing checkout cwd: first with PYTHONPATH absent,
then with a hostile competing PYTHONPATH. Both diagnostic and OpenHCS paths must
equal this selected source tree. Separate tests reject either foreign receipt
path. Existing import-authority tests also pass. The focused AST guard now catches
all three returned old mechanisms at `dd5f177f` and passes both current modules;
changed-source Ruff correctness and diff checks pass.

Real source CLI check, from the selected worktree with no PYTHONPATH:

```sh
env -u PYTHONPATH OPENHCS_CPU_ONLY=true OPENHCS_HEADLESS=true \
  PYTHONDONTWRITEBYTECODE=1 /home/ts/code/projects/openhcs/.venv/bin/python \
  -m openhcs.mcp.memory_diagnostic --source-identity
```

It reports this worktree's `openhcs/mcp/memory_diagnostic.py` and
`openhcs/__init__.py`; `/usr/bin/time -v` records 0.16s, 53,500 KiB peak RSS,
zero swaps and exit 0. No MCP, JVM, GUI or fitting/execution workload started.
The preliminary client-import path check loaded NumPy/CuPy modules (232,720 KiB
RSS) but did not execute GPU work; the provenance entrypoint's application-client
import was subsequently removed via the explicit launch-module boundary above.

Before validation the guard reported 11.8 GiB available RAM and a warning for
11.9 GiB historical swap (exit 2); no heavy validation was started. Confucius owns
the shared live slot and frozen installed harness. Owned generated sequence and
competing-package fixtures under `.validation/review-5897134270` were 164 KiB;
they are disposable and removed after retaining this receipt. No installed
package, skill, authoring process or scientific input/output was changed.

These checks close the returned **source/launch defects**, not #131's real MCP
retention measurement or #169's installed continuous desktop/history journey.
Both implementation PRs remain draft pending those serialized live gates.

## Boundaries and remaining scope

- Source review/AST coverage is focused on history serialization and the new
  diagnostic. No full NRA scan or global architecture-clean claim is made.
- ArrayBridge source-path verification and the minimal reproducer/repair ran in
  the existing environment. Initial combined test collection exposed duplicate
  `tests.conftest` package names across repositories; run the two repositories
  separately. No test assertion was weakened.
- The focused runs above used the shared nonblocking validation lock and have
  finished; no heavy worker run or runtime handle is being restarted. The older
  Euler resource receipt is historical; current restrictions and the latest
  resource snapshot are recorded above. Confucius owns the live slot and frozen
  installation; no new MCP/JVM/GUI/heavy run starts here. No unrelated cleanup occurs.
- Owned disposable pytest artifacts were under this worktree's
  `.validation/typed-native-check-2` (60 KiB of generated declarations/history
  and sequence fixtures, not user sessions). They were removed after recording
  the result; tests regenerate them. The diagnostic has not yet created a
  scratch process directory. No large output is retained.
- Coordinator must serialize a new desktop capture/restore and verify the paired
  installed entrypoint after review/integration. No worker merge/install and no
  extra display use are authorized. Neither issue is marked Closes at checkpoint.
