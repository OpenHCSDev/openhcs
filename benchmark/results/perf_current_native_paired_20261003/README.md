# Current paired native comparison

The ordinary public driver and unchanged warm native worker were run on clean source `60b2ac9b4d4fd91558f68aac85ae39b55e575fc8`, including main `f7de9efad` and the qualified ObjectState 1.1.9 / python-introspect 0.1.15 source update. CPU 5, one worker inline, one native thread, default OUTCOMES and process-tree RSS. All startup, mandatory registry/library/kernel preparation and shutdown precede/follow pipeline clocks. Native imports/JVM/pipeline loading and complete warmup -1 are outside its measured invocation.

| Case | OH compile mean | OH execute mean | OH total mean | Native invocation mean | Execution speedup | Total speedup |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3D monolayer | 1.212512 s | 9.127215 s | 11.153507 s | 14.422177 s | 1.58013x | 1.29306x |
| Speckles | 0.663492 s | 1.231350 s | 2.246087 s | 1.954230 s | 1.58706x | 0.87006x |

Both observations are retained; ranges and exact ratios are in `qualification.json`. These descriptive two-observation means are not a causal optimization experiment or statistical significance. Reaching 2x execution still requires 1.916127 s for 3D and 0.254235 s for Speckles. The source/environment differs from historical evidence, so no source change is blamed for the observed spread.

Every OH repetition passed against both fresh native repetitions: eight complete strict comparisons, measurements within the existing 1e-6 policy, exact 3D uint16 image values, known relationship correlations, and complete physical output inventories. OH 3D has six authored CSVs and 120 TIFFs (128 total physical files); native has two logical label volumes. Speckles has three CSVs (five total files). The existing comparator owns the native-only experiment table and managed metadata rules; no new exclusions were introduced. The selected source domains are exactly 180 refs / one volumetric image set and two refs / one image set. Root independently verified all 11 linked qualification artifacts and all 290 unique scientific physical output paths.

The figures use the existing `benchmark.reports.cppipe_figures` owner, means from all four ordinary rows and all four native measured observations, and the 2x reference. They are a two-case preview; full30 and scaling figures remain unfinished. Figure generator evidence and raw sample custody are in `timing_summary.json`; `metrics.csv` retains the declared figure rows.

The external immutable controllers remain at `/home/ts/.local/state/openhcs-maintenance/20261003/current-3d-speckles-paired-preparation-v2/controller.py` (SHA256 `b772d231196eaf23d9a150ffa491f95426cb6e074470ac3febd508afd1d3ad18`) and `/home/ts/.local/state/openhcs-maintenance/20261003/plot_current_paired_timings_v2.py`; their recipes use existing public execution and scientific comparison owners. These are local custody references, not a portable launcher. Original sparse-preparation failure and the exact-current-Git supplement are retained separately.

Qualification SHA256: `3db0f60d3ef04aa0ce846eaef70e746031442422cc693ba943bf78ac8db1ab32`. Science SHA256: `77ab1a1e88d52502c633b646efe0d032ad87f117fc403298cb8b5742a0510190`.

This evidence does not admit the whole PR394 R0/R1 guards, finish full-catalog parity, or establish a new performance improvement. The generic runtime plumbing goal remains active.
