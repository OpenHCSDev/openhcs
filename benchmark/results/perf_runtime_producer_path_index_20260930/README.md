# Remove repeated producer alias reconstruction between steps

The one-well 3D pipeline regenerated the same producer filename aliases for every requested slice. Its profile counted 28,800 constructions in output validation. Adjacent steps already reuse retained pixel stacks; the measured cost was redundant lineage lookup. `ProducedPathRecordIndex` derives a batch record lookup from `ProducedPathSet`; both membership and lookup use the selector's shared lazy matching policy. Existing output selection, path ordering, duplicate requests, template matching and missing/ambiguous lineage rejection remain intact. The index is transient, with no independent invalidation/cache authority.

Eight captured production 60-record/60-path manifests replay **0.622s→0.011s**, selecting identical original records and contexts. A prepared quadratic comparison candidate took 0.024s; the index also removes quadratic comparisons for concrete paths. This changes metadata resolution; processing arithmetic is unchanged.

Source `3118846ef7df0fb71e2f8002114f026414a340be`, main `7b169084`. Actual installed wheel module imports outside the checkout and matches the source hash. All recorded dependencies remain synchronized. No timed run overlaps our audits/builds/tests/other benchmarks.

| Same CPU 5, ordinary 1w_1t, means of 2 | Main | Candidate | Saved |
|---|---:|---:|---:|
| Compilation | 1.741s | 1.719s | 0.022s |
| Execution | 10.951s | 10.195s | 0.755s |
| Pipeline total | 13.425s | 12.635s | 0.790s |

**Pipeline total excludes ZMQ server startup/shutdown.** Registry preparation completes before readiness. Both versions use the same CPU affinity, fork execution and warm cache protocol in ABBA order. The first unpinned ABBA pass had substantial variance and did not establish an end-to-end gain; all original observations are preserved and no ImagingFlow speedup is attributed. The fixed-affinity comparison saves 6.9% execution and 5.9% pipeline total. Two observations per version are a bounded measurement, not a broad scaling/statistical proof. Native CP was not rerun for this unchanged arithmetic. No multiwell scaling claim.

Four installed-candidate observations each preserve all 6 complete measurement CSVs byte-for-byte and all 120 saved label images with identical pixels, dtype, shape and names. Both ImagingFlow candidate observations preserve its complete CSV bytes. No fields are omitted and no tolerances relaxed. **218 consumer checks pass**, including alias construction once per record, shared basenames across directories, overlapping templates, multiple aliases of one record, requested order/duplicates, missing lineage and inherited path membership. Two source-projection tests remain known failures and independently reproduce on unchanged main; retained separately, not counted as passing.

Scoped R0 has zero positive deltas and R1 has no increases. Original class census covers 701 modules / 5100 classes, 5088 projected and 12 OPEN. [Ownership and migration](architecture.md), [structural receipt](validation/structural_checks.json), [scientific parity](validation/perf-runtime-context-scientific-parity-20260930.json), [physical observations](observations/) and [comparison figure](pipeline_comparison.png) are retained. Authored NRA source replay and structural screens are not full semantic proofs; executed production comparisons cover the admitted behavior.

Reproduce both versions with `taskset -c 5 .venv/bin/python scripts/benchmark_cppipe_well_throughput.py --manifest benchmark/manifests/official30_portable_axis1.json --mode 1w_1t --case cp_tutorial_3d_monolayer --output-dir <unique-dir>`. Original commands/clocks are retained in observations. All raw input/profiling/label artifacts remain under `/home/ts/code/projects/openhcs-benchmark-runs/perf-current-3d-*` and `perf-runtime-context-*`. Continue profiling the remaining source metadata preparation and output identity costs after shipment.

Fixes #290. Refs #162. Performance goal remains active.
