# Paper throughput configuration: new-API probe (2026-09-23)

Status: **one workflow and one declared paper mode completed; the full paper
sweep and matched CellProfiler comparison have not been rerun.** These are
readiness probes, not replacement data for Figure 5 or Supplementary Figure 6.

The source is `benchmark/manifests/official30_portable_axis1.json`. Its
`default_well_filter: 1` selects the first source well. The ordinary throughput
wrapper now resolves that filter before cloning source projections, so each
synthetic well here contains A01 site 1 with two source channels, not every
source well relabeled as one enormous synthetic well. The benchmark uses the
regular compiled ZMQ execution route and its outcome receipts. It keeps
automatic final main-flow images runtime-only while preserving the pipeline's
explicit image exports.

| Translocation case | Completed wells | Server execution | Peak process-tree RSS | Requested overlays | Extra final overlays |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 wells, 1 worker (bounded control) | 8/8 | 40.095 s | 1379.9 MB | 8 | 0 |
| 8 wells, 2 workers (`8w_2c` paper mode) | 8/8 | 36.779 s | 1351.7 MB | 8 | 0 |

Each mode has one observation only. Do not infer a worker speedup from these
numbers: runs were not a controlled timing pair. The retained `*.csv` files,
`*_receipt.json` files and `*_outcomes.pkl.gz` files contain the measured rows,
endpoint identity/environment, compiled-pipeline hashes, successful-axis
outcomes and timing boundaries. The microscopy outputs are not tracked here.

The initial new-API eight-well attempt cloned *all* translocation source wells
into each synthetic well because the throughput wrapper ignored the manifest's
source-well filter. It hit the 6000 MB process-tree limit at 6035.6 MB after
starting six of eight wells. That observation used the wrong workload and must
not be reported as benchmark memory use. A separate one-well probe of the same
unfiltered workload completed, proving execution but not the declared scope.
The task-created large outputs from the failed attempt were removed after its
status was recorded.

The September matched-batch pilot is separate. Its archived driver uses an
obsolete direct `CellProfilerRunRequest` constructor and is intentionally not
edited in place. Undefined object threshold ratios and compiled plate-artifact
axis ownership have owner-level repairs with focused tests, but the eight
*genuine*-well native/output-equivalence comparison, matched concurrency and
timing-boundary study remain outstanding. The full 30-case, four-mode sweep has
not been run with this API.

To reproduce the paper mode from a fresh empty output directory on a checkout
containing this report:

```sh
env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 PYTHONHASHSEED=0 \
  .venv/bin/openhcs-benchmark run-well-throughput \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /tmp/openhcs-paper-mode-repro \
  --case cp_tutorial_translocation_final --preset 8w_2c \
  --max-memory-mb 6000
```

The CLI acquires an unused client-owned execution endpoint if no port is given;
it refuses to attach to an already-running UI server. The path passed to
`--output-dir` must be empty. The official source datasets must be available
through the manifest's configured path roots or acquisition cache.
