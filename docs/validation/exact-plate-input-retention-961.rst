Exact compiled plate-input retention
====================================

Issue961 repairs a worker/parent selection mismatch. When a plate callable
requests an image, the former worker filter retained every observed image
artifact. The parent subsequently discarded records outside its exact
compiled input edges. Both consumers now use the existing
``RuntimeArtifactQuery.records_for_input_edge`` query algorithm, moved from
the parent batch builder. No image-export exception list or transport
payload family was added.

The worker preserves original observation order and every selected write.
The parent preserves compiled producer-group order, address deduplication
and plate-wide required-input admission. Unstored source edges select no
records, optional missing inputs remain empty, and full-parent/omitted
observation modes retain their original behavior. Current store merging
continues to select the latest write at each key/location.

Source and consumer evidence
----------------------------

Development base: ``fa61d079c2a31345ba9d1bf55bd9a67275d985ea``.
Original-source retention controls reproduce two failures: source-only and
stored image requests both retain unrelated RGB and measurement records.
The repaired controls preserve explicit stored images, reject same-named
unstored sources, keep static and dynamic producer-group selection, and
reject wrong names, axes, locations and backends. Required missing-input
admission remains on the parent invocation.

The five-file consumer gate passes 183 tests in 2.33s on CPU3:
``test_function_step_execution_scope``, ``test_runtime_value_store``,
``test_compiled_execution``, ``test_orchestrator_execution_result`` and
``test_orchestrator_lane_planning``.

That gate initially exposed three existing fixture failures. The unchanged
base test modules reproduce all three. Fixtures now initialize the existing
PathPlanner declaration context, read consolidated outputs through
``RuntimeContextObservation.outputs`` and supply the declared measurement
dialect. The obsolete artifact-type-only retention test is replaced by
actual compiled-edge/record controls.

The current NRA original-syntax/canonical-family APIs census 1,056 production
modules and 6,374 original classes across OpenHCS and its eight checked-out
dependency source trees, with zero parse omissions. Twenty-three unprojected
classes remain OPEN. This is source ownership evidence, not global dynamic
binding, FULL-detector, native R1 or behavioral proof. Existing compiled
input projections and polymorphic query targets remain the determining
authorities; no new cache, registry or selection family is introduced.

Retained originals and the census are under
``20261005/issue961-exact-plate-input-retention-v1`` in the maintenance state
root. The first original-fixture replay lacked source-checkout activation
and failed collection; its log is preserved beside the corrected three-red
replay. It is not a product defect or a passing gate.

Performance qualification remains open
-------------------------------------

Saved ordinary translocation runs use frozen source
``bf90fda611527b388b49123dcbd776f103aa04d3``. Median axis completion to export
start is 0.278721s for eight assignments/two workers and 0.001355s for one
assignment/one worker. The interval includes transport, deserialization,
lane joins, parent merge and plate preparation. It is an upper bound for
removing that entire interval, not an isolated serialization cost.

The three stored RGB outputs declare source-context relations and are
excluded by the actual database export's image declarations. Their 640x640
saved geometry and declared float32/uint8 constructors imply approximately
84.375MiB across eight assignments. This is a source-derived estimate, not
an authentic retained-byte or pickle census. Saved observation files contain
outcomes only and cannot establish worker payload size.

Before performance promotion, capture the actual typed worker transfer and
run ordinary multiassignment numerical/pixel/relationship parity plus
matched execution timing on one frozen source. No new runtime, speedup or
installed acceptance is claimed by this source gate.
