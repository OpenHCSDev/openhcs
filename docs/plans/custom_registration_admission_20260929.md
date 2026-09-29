# Custom-function admission (#230)

Implementation owner: Lovelace; integration/live scheduling owner: coordinator.
Source tree: `/home/ts/wt/openhcs-custom-function-admission-20260929`.
Base: current `openhcsdev/main` 6c2bc4671, integrated normally.

## Verified boundary and checkpoint

The preserved H002 receipt033 timed out, but the shared execution log records
saving `/home/ts/.local/share/openhcs/custom_functions/detect_h002_centres.py` at
22:00:08 UTC. The missing cache selector selected shared7777. Documentation
already requires the selector; additional prose does not enforce admission.
No original request is replayed, no saved side effect is removed, and no assay
source, pixels or output is used in the regression fixtures.

Registration now requires an explicit `ExecutionConnectionSpec` port. Persisted
registration also requires the intended native store and public function name.
`AgentPathPolicy` admits that store and its exact owner-derived source path
before even creating an execution client. A read-only control request asks the
selected server's existing `CustomFunctionManager` owner for its actual store
without source evaluation, catalog preparation or directory creation. A
different or unsupported server fails before executable source is dispatched.
The destination carries existing `ProcessIdentity` (PID plus creation time).
That exact token is required by the native service before source evaluation and
returned with the typed connection in the mutation receipt. A changed owner or
malformed mutation receipt is not silently accepted. The server repeats both
its own and the caller's admission before evaluation and persistence; caller
roots and the selected token are internal transport state, not public MCP
parameters. The real generated tool signature verifies their exclusion.

Successful admission selects the existing catalog connection for subsequent
discovery/reference operations. Post-dispatch transport failure is reported as
`custom_function_registration_uncertain`; it does not retry or select a fallback
endpoint. Existing control timeout limits are unchanged.

## Focused evidence and resource bounds

Explicit shared-venv Python with this worktree and all eight recorded submodule
`src` paths: OpenHCS, ObjectState, metaclass_registry and PolyStore import paths
were verified in this source tree. Ten provider-free tests pass in 2.41 seconds,
with 181760 KiB peak RSS; available RAM after the check was 14.26 GiB. The resource
guard warned about historical swap; no heavy runtime was started. The tests
cover missing-route denial, ordinary/ancestor/file-symlink denial before client
creation, native-store mismatch before mutation, exact selected route,
single-dispatch uncertainty, read-only destination lookup and public-authority
field exclusion. `git diff --check` and new-test Ruff checks pass. Whole touched
source Ruff is not claimed clean: existing unrelated findings remain.

Follow-up evidence: **94 tests passed, two plugin-disabled configuration warnings,
10.17 seconds, peak RSS 322984 KiB**. This runs the new admission file, existing
custom-function lifecycle and function-catalog ZMQ suites, and three affected
MCP/CLI regressions. It adds native ordinary/ancestor/file-symlink denial with
unchanged registry membership and sentinel bytes, PID-incarnation rejection,
independent native-server policy, exact destination/receipt validation, and
actual manager persistence plus lazy package reopen/invocation on a synthetic
2x2 array. Read-only destination routing is tested with unfinished catalog
preparation and asserts it is never started. The current CLI adapter derives
connection options/defaults from `ExecutionConnectionSpec` and the public
request factory. Its real `python -m openhcs.mcp.dev_client
register-custom-function --help` entrypoint succeeds and exposes those fields;
missing port is rejected before launching a client.

One attempted extension of that shard could not collect
`test_function_step_transport.py::test_persisted_custom_function_is_importable_from_package`:
the module imports the unbuilt CellProfiler `_granularity_reconstruct` extension.
No tests ran in that failed invocation (exit4, 7.16 seconds, peak373668 KiB).
Its mocked XDG helper is updated to accept the new non-creating projection;
that module is **not claimed passed**. No extension build/install or collection
workaround is performed during the freeze. Subsequent isolated shard result is
the 94-test evidence above, not a claim that this missing dependency disappeared.

Available RAM stayed above 8 GiB (latest13.4 GiB); guard still warns about
historical11.1 GiB swap. No heavy runtime or validation-lock holder was created.

Owned disposable fixtures:
`/home/ts/.cache/agent-scratch/openhcs-registration-230-20260929/pytest`.
No MCP/JVM/GUI handle was started. Tests are source evidence, not installed or
live acceptance, and the frozen installed 17/228 tree remains untouched.

## Actual pattern review (focused source, not a full NRA proof)

- BOUND-2/BOUND-6: existing `AgentPathPolicy` owns write permission;
  `CustomFunctionManager` and XDG helpers own paths. A different native storage
  declaration changes that owner, not a new endpoint-to-filename registry.
- IMPL-12: replaced the manager's repeated name-to-file construction with its
  `source_path_for_name`, consumed by admission and actual save. New public names
  take the same helper, not a second source parser.
- MEMB-2/MEMB-3: the new control action declares its message on the existing
  request/strategy family. Existing registration/discovery registries remain
  derived; no companion roster, new runner or duplicate custom registry.
- IMPL-13: admission extends the existing DTO, endpoint service, typed control
  protocol and atomic manager persistence, rather than forking registration.
- IDEN-8: destination admission and the mutation receipt reuse existing
  `ProcessIdentity` (PID plus creation time), not bare PID/new UUID state. The
  new-case witness changes creation time while retaining PID: native registration
  rejects before manager evaluation. This is not authentication of hostile
  servers or a proof that a remote filesystem is shared with the MCP process.
- BOUND-1/IMPL-13: the existing CLI's public factory/typed connection projects
  the new route fields; no internal admission authority is generated as an
  option and no alternate registration implementation is added.

## Remaining acceptance (not closed)

After verified closure of the frozen author's owned MCP/viewer and release of
the technical slot, run controlled owned-vs-shared endpoint, escaping-path and
delayed-response checks, plus register/discover/compile/execute on a tiny
synthetic function through the actual installed MCP path. The integration owner
controls review, installation and slot handoff; no scientific execution, JVM,
installation or foreign namespace cleanup is authorized to this source worker.
This PR remains draft and references #230 without claiming closure.

Ordinary persistence admission is not a sandbox for arbitrary authorized Python;
filesystem races and hostile remote servers are not claimed globally solved.
Broad #206/#16 preparation/ROI scope and its 26 combined-suite failures remain
in their separate trees/PRs. No ROI profile or preservation pass is invented.
