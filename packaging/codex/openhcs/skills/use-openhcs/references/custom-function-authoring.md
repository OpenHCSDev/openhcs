# Add a missing analysis operation as a typed custom function

Use this route when registry search and reflected contracts show that the
required operation is missing or lacks the required semantic outputs. Reuse an
existing compatible function first. A custom function is an ordinary callable
inside a `FunctionStep`; scientific execution still belongs to OpenHCS.

## Establish the missing contract

Request the live `custom_function` authoring context. Retrieve its relevant
custom-function, lifecycle and artifact-contract knowledge targets. For labels
plus object measurements, or a custom consumer of an existing artifact, retrieve
`openhcs_callable_artifact_authoring`. Its **Consume a nominal artifact input**
section shows the input annotation/binding and earliest compile-error repair;
its executable synthetic examples demonstrate the ABI, not an assay algorithm.
For a plate-wide summary, use its **Summarize declared measurements once per
plate** example: exact `PLATE` decorators, keyword-only `RuntimeArtifactBatch`,
nominal record traversal, typed output and ordinary registration/pipeline use.
Record the missing operation and expected input axes, dtype, units, memory
backend, outputs and empty-input behaviour before writing source.
For centre detection, specify what defines a centre, coordinate order/origin,
label identity and whether a count covers one plane or the whole volume.

Before writing source, verify the intended imports, decorators, helper types
and enum members against the actual public declarations for the installed
version. Use the exposed reflected schemas and source-backed knowledge; inspect
curated architecture symbols only when that capability is exposed. A symbol's
signature or source location alone does not prove an enum member or helper API.
Retain the declaration/source identity and retrieve untruncated relevant content.
If the required declaration is not available through the authorised routes,
use a verified contract-compatible alternative if available; otherwise record
that exact contract gap. Do not invent a member or submit source as a discovery
probe. Keep definitions with their existing owners, not a copied enum catalogue
in the callable or this guide.

Implement only that operation. Keep channel selection, filename interpretation,
grouping and output destinations in the pipeline declarations. Do not read
scientific files or close over live GUI/viewer state inside the callable.
Keep assay-specific shape guards and parameters scoped to that assay; extract
a general implementation only after testing its broader input contract.

## Declare outputs on their semantic owners

Use the memory decorator and `ProcessingContract` appropriate to the operation.
The step's `variable_components` selects the stack axis; `PURE_3D` alone does
not establish that the input is ZYX. Verify the compiled grouping and coverage.

Declare typed artifacts and return payloads in their exact declared order:
complete integer labels for `ObjectLabelsArtifactType`, schema-bearing
`ColumnarRows` and a nominal feature owner for `MeasurementsArtifactType`, or
one authoritative `SpatialGraph` for path topology. Preserve an untouched raw
route when returning a processed image or diagnostic checkpoints. Let existing
materialisation declarations project CSVs, ROIs and graphs from those values;
an archive or a painted overlay is not a substitute for a typed output.

Use exact declaration references for lineage, object subjects and group scope.
If compilation reports an undeclared input or ambiguous artifact binding,
inspect that relation and its owning contract. Repair the earliest declaration
boundary, retaining before/after source identities; do not remove validation
or substitute guessed names, copied metadata or a second registry.

## Register on the intended process owner

Discover the registration capability and inspect its reflected request. Review
the source and intended storage target within the existing mutation authority.
Retain exact source bytes and hash, MCP process identity, execution endpoint,
registration receipt, returned function ID, import path and persisted paths.

Registration requires an explicit `port`, including for `persist=false`; the
UI cache is not mutation-route authority. Inspect the reflected connection
fields (`host`, `transport_mode`, `persistent`) and supply the intended owned
execution endpoint. For `persist=true`, also supply `function_name` (the public
identifier you deliberately authored) and an absolute `storage_dir`. Do not
infer the name by parsing source or omit the route to use a default server.

Derive the caller-intended store through its native owner in the **exact launch
environment of the owned execution server**, before starting either process:

```python
from openhcs.processing.custom_functions.manager import CustomFunctionManager
intended_store = CustomFunctionManager.default_storage_directory()
```

This is a non-creating lookup, not a new filename resolver. In a controlled
isolated launch, pin `XDG_DATA_HOME` in that environment and carry it into every
consumer needing stable imports. Retain the returned absolute path and owned
endpoint from the launcher. If the native launch environment is unknown, stop
and obtain that owner contract; do not guess a default path or submit source
to discover where it gets saved. No public MCP destination-discovery tool is
currently exposed for an arbitrary existing server.

For example, the controlled synthetic acceptance driver supplies the native
owner's path and deliberately authored name, not a receipt-derived permission:

```python
arguments = {
    "source_code": reviewed_source,
    "function_name": "registration_live_probe",
    "storage_dir": str(intended_store),
    "port": owned_port,
    "host": "127.0.0.1",
    "transport_mode": "tcp",
    "persist": True,
}
```

The existing MCP path policy admits the intended directory and owner-derived
file **before any endpoint dispatch**. The service then queries the native
read-only destination owner, verifies its actual store/file and process
incarnation, and binds that proof to the one registration request. Unsupported
destination proof, a different store, or a changed process rejects without
evaluating the source. The execution service independently admits the native
write before evaluation and persistence. Receipt checks after writing verify
the outcome; they are not write admission or a Python sandbox.

Prepare the catalogue on the intended endpoint **before submitting source**:

If that isolated endpoint does not exist, first discover "owned runtime" with
the capability-search tool and inspect the reflected startup request. Use
`openhcs_start_owned_runtime` with an explicit local port/connection. Its native
launch plan resolves data/log/store/registry-cache and transport-write paths in
the MCP launch environment; all must be admitted before spawn. Output-only
roots require those launch destinations to be under the authorised roots too.
It returns the exact child incarnation and launch artifacts, not catalogue
readiness. Retain the complete handle and use `openhcs_observe_owned_runtime`
until `ready=true`, then follow the preparation procedure below. The returned
`launch_plan.storage_dir` is the native caller-intended store for registration.
Occupied or reserved endpoints reject without attach, kill, or replacement.
If startup observation expires, preserve its original inputs and any returned
handle; observe that same owner, never replay startup or assume no process.
Bootstrap does not authorise source registration or scientific execution.

To dispose of a runtime you bootstrapped, discover the reflected
`openhcs_close_owned_runtime` request and pass that original complete `handle`.
`mode="force"` requests endpoint termination once, then uses the canonical
PID-plus-creation-time process owner to close within the existing control
budget. Both native startup reservations must still prove that child; a
caller-supplied PID alone is not permission to close another runtime.
`mode="graceful"` clears workers but deliberately keeps the server alive.
Retain `outcome.request_attempted` and `outcome.acknowledged` separately from
`outcome.endpoint_terminated` and `outcome.process_exited`: lost listeners or
an acknowledgement do not prove process exit. FORCE cleanup is complete only
when the exact child has `process_exited=true`. For an unresolved close or a
missing receipt, preserve original inputs and observe the same handle through
`openhcs_observe_owned_runtime`; do not replay shutdown or bootstrap. If the
reservation or incarnation proof is unavailable, report that boundary for
operator disposition rather than guessing a process or killing port owners.

1. Call `openhcs_start_function_catalog_preparation` with the same explicit
   `port`, `host`, `transport_mode` and `persistent` connection fields. It starts
   or coalesces the endpoint's existing catalogue/kernel preparation future,
   including its supervised preparation child and declared kernel-cache writes.
   It returns promptly, not after the cold preparation finishes.
2. Retain the returned `handle` exactly: its `connection` and
   `server_identity` (PID plus creation time) identify that native owner.
   Pass those two fields to `openhcs_get_function_catalog_preparation_status`.
   Observe `outcome` and `progress`; do not infer readiness from elapsed time or
   a progress message. Only `outcome="ready"` admits registration. Pending
   observations do not start another future or submit custom source.
3. If preparation fails or is cancelled, retain the error and handle. Do not
   submit source or replace the runtime implicitly. To cancel your pending
   operation, pass the same fields to `openhcs_cancel_function_catalog_preparation`;
   it signals the existing owner promptly. Continue observing that handle until
   terminal, preserving the supervised child's cleanup rather than restarting it.
4. Once ready, complete catalogue discovery on the selected endpoint, then
   send registration once. Registration independently observes readiness once
   within the existing control deadline. `function_catalog_not_ready` means no
   source-bearing registration RPC was sent by this service; the native handler
   also refuses cold registration without initiating preparation. It does not
   poll a cold catalogue and write later after the caller's observation expires.

The service never polls/resends a source-bearing request, including on pending,
error or missing receipt. A start/status observation timeout is not proof that
preparation did not start or finish: preserve its input/handle and reconcile
the same owner. It does not authorise a new source mutation or runtime fallback.

For isolated sessions, also pin `OPENHCS_UI_CONFIG_CACHE_FILE` before MCP
startup and verify the selected catalog. That launch-time selector still owns
initial discovery; passing a later GUI connection does not redirect it.
An admitted registration selects its explicit endpoint for subsequent catalog
reads, including uncertainty reconciliation. The cache does not select the
local source directory. Changing environment variables does not update an
already running process. Verify the receipt's endpoint, process incarnation,
function ID, stable import and source bytes on each actual consuming process.
Do not copy into default storage to mask a mismatch.

Use `openhcs_register_custom_function`, which delegates validation, persistence
and registry publication to `CustomFunctionManager`. An ephemeral registration
does not prove importability in another process. After mutation dispatch, a
timeout or invalid receipt returns `custom_function_registration_uncertain`:
it preserves the explicit endpoint, intended store/name and process identity,
and performs no fallback or automatic registration retry. Keep the same MCP
handle and original input. Read-only discovery on that endpoint and inspection
of the admitted source may reconcile publication; a failed observation is not
proof of no mutation. Obtain explicit disposition before any new mutation.
Creating an existing name is
not a persistence upgrade; use an exposed lifecycle update route or record the
missing capability rather than overwriting its file or mutating private state.
If a lifecycle update is unavailable, a deliberately versioned new callable
may be registered within the authorised scope after verifying name absence;
preserve the predecessor and distinguish both identities in the pipeline log.

## Prove pipeline use before judging the biology

Search and describe the returned function ID to verify its reflected contract.
Validate a complete declarative `PipelineDocument` using the stable import.
Do not hide registration, filesystem reads or an `if/hasattr` import fallback
inside that document. Confirm importability on the actual consuming process,
then obtain a current compile and inspect axes, artifact identities and planned
materialisation paths before a bounded authorised run.

Inspect real completion and actual durable outputs. Where resources permit,
read back saved artifacts through the supported route rather than equating
planned paths with persisted bytes. Follow [matched viewer QA](viewer-qa.md)
for raw-only, result-only and combined evidence; review 3-D centres at separated
Z planes and orthogonal views rather than trusting a projection or count.
Check coordinate order/origin, units, object IDs and table/label linkage.

## Retain the capability, not an unvalidated recipe

Keep registration, fresh-process import, compilation, execution and biological
acceptance as separate evidence tiers. A rejected trial can still teach a
reproducible authoring or diagnostic pattern. Preserve its failed predecessor,
contract repair and remaining limits in the authorised trial/repository record.
Follow [analysis learning](analysis-learning.md) and
[blinded recipe promotion](blind-recipe-promotion.md) before broader reuse.
Do not copy held-out answers or dataset-tuned settings into agent-facing
guidance, or claim that custom-function support itself improved accuracy.
