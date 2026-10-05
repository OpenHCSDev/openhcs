Nominal plate-summary authoring checkpoint
==========================================

PR562; scoped source qualified at07eb5bb09. Canonical how-to source is
docs/source/development/callable_artifact_authoring.rst. The manifest declares
that RST as openhcs_callable_artifact_authoring; packaged custom-function MD
only adds a three-line route to its new section. No second guide, runtime
implementation, filesystem aggregation or new registry. Future bundles only;
no live scientific skill/package/source changed.

Determining owner trace
----------------------

The original runtime already supports a custom PLATE callable. Existing
execution_scope and runtime_bound_parameters declarations feed CallableContract;
OpenHCSRegistry.declared_callable_contract explicitly admits plate callables
without axis memory/ProcessingContract. CustomFunctionManager._prepare_source
resolves exactly one admitted top-level function in its real source namespace,
then validates its contract. FuncStepContractValidator enforces the required
keyword-only artifact_batch:RuntimeArtifactBatch and rejects image-processing
contracts. The existing production ExportToSpreadsheet callable uses this ABI.

compiled_plate_execution.validate_plate_scoped_contexts requires coherent,
terminal plate invocations. Its _validate_plate_invocation currently admits
exactly ONE SpecialArtifactType output, not a MeasurementsArtifactType output.
execute_plate_scoped_steps selects the original declared records and calls the
function once in the parent after successful axis execution. RuntimeArtifactBatch
owns records(spec.ref()) traversal; StoredRuntimeValue.value.data is the typed
MeasurementTable selected by the MeasurementsArtifactType input. Its original
ColumnarRows.row_count provides schema-aware measurement-row counts.

The example has one SpecialArtifactType output containing the existing
DataclassMeasurementColumnarRows payload. CsvOptions/MaterializationSpec retain
the original writer. It is a side-channel summary, NOT a new object-measurement
domain. Axis IDs are not guessed well identities; row counts are not biological
counts or whole-task coverage proof. Required input absence must be repaired
through binding, not by loading partially persisted files.

Open PR claims checked before edits: Root394 owns the compiler/runtime/store/
materialization family; its published files did not include this canonical RST,
routing MD, knowledge manifest or reference test. No shared production owner was
edited. Latest observed Root head27f63585 remains independent. The finished560
checkout was reused on a new docs branch, preserving all seven foreign gitlink
dispositions and existing untracked journals. NRA and authoritative audit ZIP,
skill-creator and Diataxis were read; BOUND-2 applies to nominal batch/table
traversal, AGENT-5 to verifying exact declarations and AGENT-7 to avoiding holds.
No structural refactor, copied scanner, full-family R0/R1 or global AST claim.

Actual checks and retained failures
----------------------------------

Original caller: validation/viewer-retirement-519/run_source_controls.py with
actual checkout PYTHONPATH, existing paired interpreter and dependency bootstrap.
No peer target override, install, native/server/viewer/provider launch or science
execution. Plugin autoload/JIT disabled; BLAS threads1. Each original systemd
scope stays in unchanged openhcs-blindsol3phase03.slice, MemoryMax536870912,
MemorySwapMax0, CPUQuota100%, AllowedCPUs3, RuntimeMaxSec60, TasksMax48.
Fresh original resource check had21.3GiB available, common1.35/16.64GB,
Swap0; disk/swap advisory retained. No resource limit raised.

01 at322d07e8 plus the original uncommitted fixture:2 exposure checks passed,
new execution fixture FAILED on unsupported ArtifactOutputPlan keyword
measurement_feature_owner. Whole7.258s,238.6MiB,Swap0/OOM0. Subsequent source
inspection also corrected the draft's unsupported plate measurement-output
claim to the original SpecialArtifactType contract. No validator was weakened.

02 at954fd15f8:2 canonical/projected exposure checks passed, fixture FAILED
because its per-axis output paths violated the original common compiled plate
invocation identity. Whole5.725s,163.4MiB,Swap0/OOM0. The existing plate fixture
already uses one shared plate-output path;03 restores that owner relationship.
Both negatives and original stdout/stderr are retained byte-exact, not edited.

03 at07eb5bb09:2PASS/35deselected in3.53s; whole4.265s,
memory.peak163631104B (156.1MiB),Swap0/OOM0. No broader suite rerun.
Literal code executes through actual custom admission and original compiler,
then reuses test_function_step_execution_scope.py helpers to invoke the actual
parent plate executor. Two axes contain two rows and zero rows; unrelated
measurement artifacts are excluded. One runtime result contains exact declared
schema/counts, and the original CSV writer saves/readbacks both rows. The new
case needs its own declaration only: no generic registry/compiler/consumer edit.

The other final control uses original project_knowledge_assets,
AgentSkillBundle and sync_skills to project/sync every canonical skill resource
byte-exact, returning unchanged on a second isolated sync. The02 exposure
controls retrieved the exact final RST and routing MD through KnowledgeBaseService;
only the test fixture's shared output path changed for03. Original two pytest
plugin-configuration warnings remain in raw logs. Production/docs diff check
passes; no raw log whitespace is rewritten.

Published byte-exact archive beside this receipt includes all six original raw
logs, the original caller and qualified guide/manifest/test source. Temporary
projections/sync outputs are disposable copies, not scientific inputs or results.
No retained scientific history/UNKNOWN operation was replayed or removed.

Archive29878B SHA256:
0934fd3fac7a308574ba141d969cd59e3e62d086d0a8748e1d98d38495afa714.
After all three original scopes were inactive and lsof reported no borrowers,
only owned validation/nominal-plate-summary-tmp01, -tmp02 and -tmp03 were
removed:1425408+1425408+1617920=4468736 allocated bytes released.
All raw journals, published source history and byte-exact archive remain.

Limits
------

This confirms supported custom plate ABI and documentation exposure at source/
package-projection tier. Fresh-process public registration, an installed full
plate journey and autonomous usefulness remain distinct, unclaimed. No inferred
viewer-retention/scaling recipe was added: disabled full-run streaming is not
evidence of a missing bounded-preview recipe or its causal role in an OOM.
