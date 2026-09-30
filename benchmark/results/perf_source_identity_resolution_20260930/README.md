# Batch exact source identity resolution

Runtime source side inputs scanned every declared path separately for every provenance identity. The production 3D ImageMath request made 43,200 predicate calls across its two 60-plane side inputs. `SourceIdentityResolutionContext` now owns the existing exact predicate and shared path derivation; `SourceBindingMatchedImageSet` inherits batch resolution and retains binding/set expansion. A query-local path index narrows candidates, while the shared expansion algorithm reuses the already-filtered source universe. No persistent metadata or pixel cache was added.

Captured real queries preserve exact members and ordering: three fixture medians sum to **0.499s main → 0.225s installed candidate**. Actual public-pipeline diagnostics find **four** large membership queries, totaling **0.773s → 0.341s**. Source side-artifact materialization, which includes those queries, totals **1.217s → 0.771s**. These nested scopes must not be summed. One diagnostic run per version establishes production transfer of this bounded stage saving; it is not a statistically established total-runtime improvement.

| CPU 5, 1w_1t ABBA, mean of two observations/version | Main | Candidate |
|---|---:|---:|
| 3D compilation | 1.173s | 1.186s |
| 3D execution | 10.309s | 10.258s |
| 3D pipeline total | 12.214s | 12.133s |
| ImagingFlow execution | 17.994s | 18.405s |
| ImagingFlow pipeline total | 20.536s | 21.110s |

**Pipeline clocks exclude ZMQ server startup/shutdown.** Callable/kernel preparation completes before readiness; workers use fork. Both revisions use the same CPU affinity and cache protocol. CLI clocks are recorded separately. No timed run overlaps our tests, builds, structural audits or other benchmarks. The ABBA ranges are wide, so this checkpoint does **not** establish a material end-to-end gain or an ImagingFlow improvement. Native CP and multiwell scaling were not rerun here.

All six complete measurement CSVs and all 120 saved label images retain exact bytes/pixels/dtype/shape/names in each of six 3D observations, including both diagnostic runs. All four ImagingFlow complete CSVs retain the saved successful digest. No fields or tolerances were relaxed. Consumer checks pass: 777 across source projection, binding, function patterns, runtime adapters, CellProfiler module execution and artifact ownership; the source-binding suite reruns with an additional template-path regression, 49 passing. Tests cover shared files with different planes, metadata-only identities, ambiguous/missing paths, component correlation within one record, query ordering, updated declarations, pickle/MRO/constructor behavior and predicate-count collapse. A template retains its existing first-physical-path projection rather than broadening membership to all mapped files.

Production source `6faadd267b9d4b8e0d40fee8c2396e7c2591f0ec`, additional test `6b6de2130`; main `d3a99c0d46dea979bba3f9076da87386e49cbed3`. The candidate is a fresh installed native wheel used outside the checkout. Recorded dependency pins are unchanged. Scoped R0/R1 show no increases. The original ClassDef census includes 702 modules / 5110 original classes, 5098 projected and 12 retained OPEN. The NRA declaration-selected method promotion rejected unsupported native decorated-class capture; the alternative authored exact move is syntax/revision checked, with executed constructor/pickle/consumer evidence. No complete native semantic proof is claimed.

[Ownership and structural evidence](validation/structural_checks.json), [exact scientific parity](validation/perf-source-identity-scientific-parity-20260930.json), [all physical observations](observations/perf-source-identity-fixed-cpu-abba-observations-20260930.json), and [stage/total comparison](comparison.png) are retained. Raw fixtures, images, logs, complete census and source transactions remain under `/home/ts/code/projects/openhcs-benchmark-runs/perf-source-*`.

The same diagnostic identifies the next source-preparation cost: **780 image-header reads across three recorded paths**, roughly 0.49s in the candidate. Source loading plus side materialization remains about 1.59s; exact membership is now about 0.34s of that. Investigate reuse through the existing source/file-format authorities with explicit file-revision semantics. Also continue output-context and other execution profiling. This change is one measured part of the remaining overhead, not completion of the performance goal.

Reproduce with `taskset -c 5 .venv/bin/python scripts/benchmark_cppipe_well_throughput.py --manifest benchmark/manifests/official30_portable_axis1.json --mode 1w_1t --case cp_tutorial_3d_monolayer --case ExampleImagingFlowCytometryObjectsInGrid --output-dir <unique-directory>` and the selected package on `PYTHONPATH` from `/tmp`. Every retained observation explicitly checks `status=success` and `successful_wells=1` in addition to CLI exit status.

Fixes #296. Refs #162. Performance goal remains active.
