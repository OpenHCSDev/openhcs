Official30 qualification after main synchronization (#330)
=========================================================

Production source ``4c40348354a0680850ac21cdc102d00e460558ee`` includes main
``2cbfc4a0771bf24d153b076bff4a5e321ac039f4`` and its exact dependency pins.
All 30 native-reference comparisons pass, with zero differences. The original
six compile failures and the subsequent eight execution/output failures are
resolved. This correctness gate enables representative performance work;
it is not a speedup claim.

The determining owners
----------------------

``MeasurementSubject.row_identity_domain`` derives compatible row identities
without merging exact source-qualified image subjects. Common output admission
uses the derived domain; payload policies still enforce their own cardinality.
Ordinary/native single-subject payloads and incompatible scopes/object domains
retain their rejection controls.

Carrier admission follows the authoritative compiled predecessor through
inherited bindings. ``CompiledStepPlan`` owns terminal-source projection, and
every producer transition and terminal physical header remain mandatory.

``StepInputDependency`` determines which anchors originate at pipeline start;
inherited source bindings cannot discard predecessor/artifact-only lifecycle
anchors. ``CallableContract.group_scope_inputs`` owns execution-domain source
selection. The planner projects preliminary source bindings through those exact
refs, then uses its existing producer/lineage resolver. ExampleFly's auxiliary
OrigBlue filename source cannot restrict the composed RGBImage execution domain.
The typed output manifest remains authoritative for actual producer pixels.

``OpenHCSMetadataWriter.OutputTarget`` derives production and reconciliation
targets. Runtime artifact targets enumerate actual declared writer destinations,
and durable typed source projections survive execution-local value-store cleanup.
The declared root remains included so unknown image addresses still fail closed.
Materialization's existing record factory owns the empty-output-plan case;
callers do not add absence guards around its execution-local store.

Terminal and streaming materialization policies now live in the shared
materialization package. Internal diagnostic planes declare persistence without
external export intent. Source serialization preserves each nominal policy
subtype, including its options, backends and write mode. No function-name
exceptions, ignored extra science outputs, generated-name coordinate inference
or CSV normalization are used.

Validation and limits
---------------------

* 586 local tests and 20 subtests pass; one existing optional Napari skip.
* Original CI-pinned R0 passes for OpenHCS, scripts and benchmark, without increases.
* Original NRA R1 passes its two policy-configured detectors with complete
  dependency context and no increases; this is not an all-detector clean claim.
* Original ClassDef census: 5,122 declarations, 5,110 projected, all 12 OPEN retained.
* NRA admitted the two-class policy relocation and its import-consumer closure.
  The initial binding-authority/annotation boundary rejection is retained.
  Authored semantic changes have separate executed tests and native comparison.
* Native progression: 22/30, then 29/30, then 30/30 on the synced source above.
  All final difference counts are zero. Existing 1e-6 absolute/relative numerical
  tolerances, exact discrete/identity checks and declared-image checks remain.

Tests include real image writes into two declared destinations, cleanup and
durable reopen with exact metadata/pixels, unknown-address rejection, implicit
main-flow controls, stored cross-axis and direct-source payload domains, and
three materialization-policy source roundtrips. Three stale fixtures were
reproduced on unchanged main and repaired from authoritative declarations/source
fields and the existing shared ACK fixture; scientific assertions remain strict.

The final gate uses the production comparison suite with the retained native
outputs from ``official30-native-complete-fresh-20260928``. Those outputs are
scientific references. The native clocks and speedup columns in the raw reports
are retained observations, **not fresh comparative performance evidence**. This
gate does not regenerate native clocks or scaling figures and does not assert
complete parity for every possible ROI/export profile outside the suite.

Ready-server startup and shutdown are excluded from pipeline clocks. The suite
uses one inline worker, one numerical thread, CPU5, and no memory observer.
Comparison and qualification work are separate from execution timing. Tests,
audits, builds and other replays do not overlap timed pipeline work.

Receipts and reproduction
------------------------

``official30_qualification_330_evidence_20261001.tgz`` contains source and
dependency receipts, exact task recipes, original guards/census, local test XML,
unchanged-main controls, NRA move evidence, the saved ExampleFly anchor trace,
all three qualification summaries/observations, and the final 30 generated
pipeline sources and measured receipts. ``SHA256SUMS`` authenticates its files.
Large scientific inputs/outputs remain in the benchmark-run workspace.

Extract the archive, check out the validated production revision, and use its
final qualification recipe with the configured benchmark Python and retained
native-reference root. The original controller environment was:

.. code-block:: bash

   env PYTHONPATH="$PROJECT_ROOT" \
       OPENHCS_REFERENCE_EXPORT_PIPELINES_ROOT="$PROJECT_ROOT/benchmark/reference_exports/official30_value_completion_20260914" \
       OPENHCS_CPU_ONLY=true NUMBA_CACHE_DIR="$SHARED_NUMBA_CACHE" \
       OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
       NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 PYTHONHASHSEED=0 \
       taskset -c 5 "$BENCHMARK_PYTHON" "$QUALIFICATION_RECIPE"

The recipe records its source assertion, manifest, retained native-reference
receipt and production ``run_comparison_suite`` arguments. Its local paths must
resolve to those retained inputs. If they are unavailable, produce fresh native
outputs using the public comparison route and configured CellProfiler environment.
The public throughput route remains ``scripts/benchmark_cppipe_well_throughput.py``
with ``--manifest benchmark/manifests/official30_portable_axis1.json --mode 1w_1t``.

This change fixes #330 and references #315, #214 and #324. It does not close
#315's separate parent/live acceptance. Generic runtime ownership remains PR326,
and execution/compilation performance work continues under #162.
