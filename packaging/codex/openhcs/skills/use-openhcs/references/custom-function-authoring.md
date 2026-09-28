# Add a missing analysis operation as a typed custom function

Use this route when registry search and reflected contracts show that the
required operation is missing or lacks the required semantic outputs. Reuse an
existing compatible function first. A custom function is an ordinary callable
inside a `FunctionStep`; scientific execution still belongs to OpenHCS.

## Establish the missing contract

Request the live `custom_function` authoring context. Retrieve its relevant
custom-function, lifecycle and artifact-contract knowledge targets. For labels
plus object measurements, retrieve `openhcs_callable_artifact_authoring`: its
executable synthetic example demonstrates the ABI, not an assay algorithm.
Record the missing operation and expected input axes, dtype, units, memory
backend, outputs and empty-input behaviour before writing source.

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

For parallel isolated sessions, verify catalog ownership as well as GUI bridge
ownership. In the current local stdio route, the catalog endpoint is selected
from the UI config cache when the MCP process starts; passing a GUI connection
to a later UI call does not redirect catalog registration. Pin the owned cache
selector (`OPENHCS_UI_CONFIG_CACHE_FILE`) before starting that MCP process, then
verify its endpoint. Use the current reflected contract if this route changes.
Do not resolve a timeout by registering on a peer or default catalog.

Use `openhcs_register_custom_function`, which delegates validation, persistence
and registry publication to `CustomFunctionManager`. Choose persistence when
the reviewed pipeline needs a stable import across GUI, backend or fresh worker
processes, after confirming the returned storage directory is in scope.
An ephemeral backend registration does not prove importability in another
process. A timeout leaves mutation outcome uncertain: reconcile the exact name
on the same endpoint before any explicit retry. Creating an existing name is
not a persistence upgrade; use an exposed lifecycle update route or record the
missing capability rather than overwriting its file or mutating private state.

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
