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
The server repeats admission before evaluation and persistence; caller roots
are internal transport state, not a generated public MCP parameter.

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
- IDEN-8: endpoint process-token binding remains the immediate next change;
  reuse existing `ProcessIdentity` (PID plus creation time), not a bare-PID or
  new UUID authority. This checkpoint does not claim race-proof route identity.

## Remaining acceptance (not closed)

Bind destination admission to the existing process-identity token and verify
the same owner before server evaluation. Exercise the real generated MCP
signature and native manager/registry preservation. After release of the
technical slot, run controlled owned-vs-shared endpoint, escaping-path and
delayed-response checks, plus register/discover/compile/execute on a tiny
synthetic function through the actual installed MCP path. No scientific
execution, JVM, installation or foreign namespace cleanup is authorized here.

Ordinary persistence admission is not a sandbox for arbitrary authorized Python;
filesystem races and hostile remote servers are not claimed globally solved.
Broad #206/#16 preparation/ROI scope and its 26 combined-suite failures remain
in their separate trees/PRs. No ROI profile or preservation pass is invented.
