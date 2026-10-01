One materialization batch for saving, publication and observation
===============================================================

This candidate addresses the generic plumbing tracked in issue #384. It is not
an accepted end-to-end performance result. The separate light owner trace bounded
eight repeated renders at approximately 0.297 seconds and metadata finalization
at 0.896 seconds; removing repeated rendering alone cannot close the generic
runtime gap. This is a structural dependency of the broader runtime boundary work.

Ownership and production flow
-----------------------------

``MaterializationBatch`` owns one writer-group rendering and saving algorithm;
its primary path is a derived view. ``SavedMaterializationOutputs`` owns only
completed backend outputs. ``MaterializedRuntimeArtifact`` inherits that shared
backend projection and adds the original reduced artifact binding and observation
behavior. Backend-indexed mappings contain actual destination values, not behavior
handlers. Existing WriterSpec declarations continue to determine format-specific
writing. No new runtime ledger, context cache or identity memoization was added.

``BackendSaver`` reports only payloads accepted by each backend after successful
save calls. Failed saves raise without returning successful outcomes. Artifact
finalization passes those exact outputs to the existing nominal OutputTarget
family. Transient publication targets own the outcomes until publication finishes;
they are excluded from target equality and hashing. Image directories and source
projections consume these outputs without rendering the mutable logical artifact
again. Rendered pixel content is not carried into worker observation transport.

The already declared ``StepExecutionObservation`` now carries actual persistent
locations and declared export paths from finalization. Ordinary worker progress
consumes returned locations; worker result observations accumulate returned paths
before image resources are released. Plate-scoped execution uses the same actual
materialization handoff. Existing ``CompiledPlateExecutionExtras`` carries its
RuntimeExecutionObservation; ``CompiledPlateExecutionResults.runtime_observations``
is a derived collection of worker and parent observations. Both ZMQ value and
outcome exports consume that collection. RuntimeExportObservation no longer
reconstructs output paths from compiled contexts and mutable logical values.

Terminal materializations persist without external-export participation;
streaming-only specs report no persistent destinations. Measurement reducers can
produce synthetic records absent from RuntimeValueStore; outcomes remain bound to
the record actually reduced and materialized. Main-flow manifests retain their
independent inheritance and semantic-address contracts.

Removed code and intentionally retained consumers
------------------------------------------------

Removed ``_materialization_output_groups`` after moving its shared algorithm to
MaterializationBatch.render. Removed the tests-only materialized and observed
materialized path helpers, the obsolete current-runtime export-path helper, the
single-call observed-materialization wrapper, and
RuntimeExportObservation.from_execution_contexts. Routing tests now intercept
batch preparation; physical/export tests pass actual outcome records explicitly.

Historical debug reuse still has an explicit prediction surface named
``preview_reused_*``. It does not create a new-save StepExecutionObservation.
Snapshot-owned physical receipts remain OPEN for that separate debug lifecycle;
these prediction functions are not an ordinary execution fallback. Historical
viewer expectations retain their real declaration-based rendering consumer.
Analysis consolidation retains its real CSV-content derivation consumer; it is a
separate reduction, not a replacement authority for observed export paths.

Evidence and limits
-------------------

Original source: 10f7e7075b412ccea8959f2c4e1aa818455149fa. NRA original syntax/class
census covers 703 modules, 5157 original ClassDefs, 5145 canonical projections and
12 retained OPEN syntax rows. The bounded ownership decision and complete census
are retained in the external benchmark evidence directory. The authored lifecycle,
new return values and argument migration exceed declaration-movement DSL proof
scope; no native behavioral equivalence proof is asserted.

The first consumer gate retained 154 passing and 33 failing tests. Routing spies
intercepted the removed production boundary; metadata fixtures omitted the actual
output handoff. Their assertions were preserved while moving those fixtures to the
new boundary. The next six-module gate passed all 197 tests. A later parent gate
passed 264 tests with three new worker-fixture failures: the fixture failed the
existing DebugExecutionContext nominal boundary. It was replaced with a genuine
ProcessingContext subclass; the production boundary was not weakened.

The final eleven-module gate passes 267 tests in 5.12 seconds. It includes actual
backend acceptance and failed-save controls, exact output-object reuse after
logical input mutation, rejection of re-rendering during ordinary worker progress
and export, all three runtime observation modes, pickle transport after resource
release, exact combined worker/parent export paths, materialization formats,
metadata publication/reconciliation, runtime/viewer validation and ZMQ consumers.

The original unmodified R0 guard passes for a264ee95546ab17a3ded40f81759cc6234d08817
against main e341ac9b55cb2b6a143df9083785b296c23000df. There are no positive debt
deltas; ZMQExecutionServer god-class excess decreases by eight lines and the
artifact materialization foreign-absence probe decreases by one. This revision
includes the normal merge of main's fixture/documentation fix; production sources
are identical to the 267-test candidate.

Combined R1 source qualification, representative ordinary unprofiled timing and
native numerical parity remain required before promotion. No benchmark ratios or
speedup claim are attached to this receipt.

Actual array outputs and raster publication
------------------------------------------

The first combined native comparison retained 28 numerically equivalent cases
and two illumination metadata failures. The saved illumination NumPy arrays were
actual outputs, but their NumPy-only directory had incorrectly become eligible
for raster image inventory publication. The existing FileManager inventory
includes declared raster formats; NumPy array exports are outside that inventory.
The candidate had removed OutputTarget's inherited ``contains_images`` admission
gate while switching directory discovery to actual saved outputs.

The correction restores that existing nominal gate. Actual NumPy saved outputs
and their observation locations remain intact; publication and completed-plate
reconciliation consume only directories with images in the existing inventory.
No second format registry, rerendering fallback or empty source projection was
introduced.

Independent controls use a real FileManager and physical NumPy-only and mixed
TIFF/NumPy outputs. The original candidate fails the NumPy-only control with the
same empty SourceProjectionSet error; its mixed-directory control passes. Both
controls pass after restoration, verifying exact saved pixels, actual observation
paths, raster-only inventory and typed calibration. The focused red and green
receipts are ``materialization-npy-publication-red-v3-20261001.log/xml`` and
``materialization-npy-publication-green-20261001.log/xml`` in the external benchmark
evidence directory. Earlier import-order and typed-unit fixture errors are also
retained separately; they are harness failures, not the product regression.

The expanded eleven-module consumer gate passes all 269 tests using only the
original nominal viewer route fixture from the root test configuration. Two
initial broader invocations retained 264 passes and five missing-fixture setup
errors; the corrected fixture registration preserves those same five controls.
The final receipt is ``materialization-npy-publication-consumers-v3-20261001.log/xml``.
Full native parity and fresh accepted timing remain required for the corrected
combined source; the original 28-pass/two-error receipt is not replaced.
