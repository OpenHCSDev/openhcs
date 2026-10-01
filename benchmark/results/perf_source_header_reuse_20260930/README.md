# Reuse immutable image headers through the format owner

`ImageFileFormat` owns one bounded successful-header cache shared by strict and optional metadata readers. Concrete TIFF/NumPy/default ImageIO hooks own parsing. `ImageFileRevision` derives path/device/inode/size/mtime_ns/ctime_ns from the actual file; the bound class reader participates in the key. File rewrite, replacement, deletion/recreation and reader replacement invalidate reuse; failed reads are retried. Only immutable dtype/scale/channel header facts are retained, never pixels or open handles. Existing optional/strict failure policies remain; NumPy strict and optional metadata now derive from its native reader.

Representative 3D preparation made **780 header reads across three actual physical files**. Native production replay, including a freshly cleared cache per sample, has median **0.487s → 0.028s**. Earlier ordinary public-pipeline diagnostics find execution header parsing **780 actual parses → zero**, because the three successful source headers were inherited from pre-fork preparation. High-level header queries cost **0.468s → 0.060s**. Source loading plus source side-artifact materialization (nonoverlapping enclosing scopes) cost **1.875s → 1.257s**. Membership/metadata/header subscopes nest and must not be summed. This is a bounded preparation saving, not a whole-pipeline target achievement.

## End-to-end evidence and variance

**Diagnostic qualification:** a later [thread-isolation reproduction and direct-timer replacement](../perf_payload_slice_projection_owner_20260930/README.md#corrected-diagnostic-scope) establishes background-thread contamination of ordinary CPython 3.12.14 cProfile. Historical profiled production-phase timing/call-graph attributions above cannot establish causal phase reductions. The unprofiled public clocks, native header replay and exact parity checks remain valid.

An earlier 3D-only CPU5 ABBA (two observations/version, older dependency pins) found mean execution **9.938s → 9.095s**, pipeline total **12.385s → 11.524s**. Its preceding mixed-case ABBA found no total gain and no ImagingFlow gain. Both series are retained in full and are not pooled.

After normally merging main and updating all actual source pins/distribution metadata to the ACK runtime generation, the separate current-main ABBA yields:

| Current main a2858341a vs installed candidate cf1f5a4025 | Main | Candidate |
|---|---:|---:|
| Compilation | 1.677s | 1.763s |
| Execution | 9.839s | 9.866s |
| Pipeline total | 12.215s | 12.350s |

**This latest series does not establish an end-to-end speedup.** Candidate execution varied by 1.166s across its two observations, larger than the bounded header-stage saving. Do not attribute that variance causally without a separate measurement. Retain the measured stage elimination and continue the larger runtime data/preparation work; the broad execution goal remains active.

All pipeline clocks **exclude ZMQ server startup and shutdown**. Mandatory callable/kernel preparation finishes before server readiness; workers use **fork**. Unprofiled ABBA uses a shared warm on-disk Numba cache and CPU5, 1w_1t; no timed pipeline or prewarm overlaps our audits/tests/builds/other benchmarks. CLI clocks are recorded separately and never presented as pipeline total. Fresh installed ABI3 wheel runs from `/tmp`; header source hash matches the committed candidate. Native CP and multiwell scaling were not rerun in this checkpoint.

## Scientific and structural gates

All six complete measurement CSVs and 120 label images are exact in each current-main observation: **24 CSVs and 480 label images**. The earlier ten 3D observations retain **60 CSVs and 1200 labels**, plus four complete ImagingFlow CSV digests. Labels preserve exact names/pixels/dtype/shape; CSVs are byte exact. No scientific assertion or tolerance was loosened.

**653 consumer tests pass**, including repeated native headers, same-size/restored-mtime rewrite, deletion/recreation, transient failures, changed readers, TIFF/PNG/NumPy shared strict dispatch, existing strict/optional failure rules, persisted image metadata, source projection/binding, runtime artifacts and CellProfiler semantics. Current main environment installs normally with resolving dependencies. A later outside-source check exposed stale duplicate editable metadata hidden by the initial source-directory pip check; [the repair and clean merged-main acceptance](../../../docs/validation/duplicate_editable_metadata_20260930/README.md) retain both the failure and correction. The incompatible PyQt Reactive pin encountered during this update was fixed and merged in PyQt Reactive PR9 and OpenHCS PR305 (issue303 closed), rather than bypassing the resolver.

Scoped R0/R1 have no increases. Fresh original-class census after the ACK/main integration: **702 modules / 5121 original classes / 5109 projected / 12 retained OPEN**. R1 materializes full committed parent/dependency context (3020 projections/version) while reporting only the changed header module. The authored NRA class-selected transformation provides syntax/revision evidence; native constructor/metaclass/execution equivalence is not automatically proved. Executed native/consumer/installed parity gates provide the stated behavior evidence. Stat fingerprints do not promise atomic concurrent mutation; current stateless format declarations determine the reader hook. Arbitrary mutation of nested helper functions is outside the hook replacement contract.

[Current provenance](validation/perf-source-header-current-main-provenance-20260930.json), [current means and complete parity](validation/perf-source-header-current-main-comparison-20260930.json), [earlier positive/negative protocols](validation/perf-source-header-comparison-20260930.json), [production phase transfer](validation/perf-source-header-phase-comparison-20260930.json), [ownership decision](validation/perf-source-header-ownership-decision-20260930.json), [structural scope](validation/structural_checks.json), and [comparison figure](comparison.png) are retained. Original complete census, captured inputs/images, native fixtures and logs remain under `/home/ts/code/projects/openhcs-benchmark-runs/perf-source-header-*`.

Reproduce exact recipes from `recipes/`; benchmark command is `taskset -c 5 .venv/bin/python scripts/benchmark_cppipe_well_throughput.py --manifest benchmark/manifests/official30_portable_axis1.json --mode 1w_1t --case cp_tutorial_3d_monolayer --output-dir <unique-directory>`, from `/tmp` with the selected installed/source package on PYTHONPATH. Every observation checks status=success and successful_wells=1 as well as process exit.

Fixes #300. Refs #162. Broad performance goal remains active.
