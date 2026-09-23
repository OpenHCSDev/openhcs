# Paper throughput configuration: new-API probe (2026-09-23)

Status: **the declared `8w_2c` paper mode completed through the new ordinary
pipeline API, and a separate genuine-well CellProfiler/OpenHCS output pilot
completed.** The full 30-workflow, four-mode sweep and a matched timing study
have not been rerun. These are readiness probes, not replacement data for
Figure 5 or Supplementary Figure 6.

The source is `benchmark/manifests/official30_portable_axis1.json`. Its
`default_well_filter: 1` selects the first source well. The ordinary throughput
wrapper now resolves that filter before cloning source projections, so each
synthetic well here contains A01 site 1 with two source channels, not every
source well relabeled as one enormous synthetic well. The benchmark uses the
regular compiled ZMQ execution route and its outcome receipts. It keeps
automatic final main-flow images runtime-only while preserving the pipeline's
explicit image exports.

| Translocation case | Completed wells | Server execution | Peak process-tree RSS | Declared output files | Undeclared side writes |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 wells, 2 workers (`8w_2c` paper mode, corrected export policy) | 8/8 | 26.962 s | 1380.2 MB | 10 (8 TIFF, SQLite, CPA properties) | 0 |

This corrected mode has one observation only. The earlier `8w_1c` and `8w_2c`
files remain as diagnostic history, but are **superseded**: their imported
pipeline config enabled automatic segmentation-artifact writes beyond the
requested exports. They must not be used as timing or output-equivalence
evidence. Do not infer a worker speedup from any of these rows. The retained
`*.csv`, `*_receipt.json`, and `*_outcomes.pkl.gz` files contain measured rows,
endpoint identity/environment, compiled-pipeline hashes, successful-axis
outcomes, and timing boundaries. The microscopy outputs are not tracked here.

The [matched genuine-well pilot](../matched_batch_pilot_v2_20260923/README.md)
used the same new submission path on eight real source wells, with warm-up and
three observations. Each had eight completed axes, ten declared/native/candidate
files, and zero database or image differences. A separate confirmation used
the strict shared CellProfiler equivalence policy. It is not a matched
throughput benchmark: timing boundaries and concurrency remain to be aligned.

On commit `150699499`, the CLI's `--plan-only` route resolved this paper
manifest to 30 cases and its four declared modes without warnings. A separate
wheel built from that commit passed `scripts/smoke_installed_mcp.py
--exercise-measured-execution` from a fresh installation: the MCP health and
expert benchmark tools, installed CLI sweep planning, and one small ordinary
source-backed job each completed. That wheel smoke uses synthetic data, not
this 30-case paper manifest; the two live translocation rows above are the
paper-manifest execution evidence. The temporary wheel installation was
removed after the smoke test.

The initial new-API eight-well attempt cloned *all* translocation source wells
into each synthetic well because the throughput wrapper ignored the manifest's
source-well filter. It hit the 6000 MB process-tree limit at 6035.6 MB after
starting six of eight wells. That observation used the wrong workload and must
not be reported as benchmark memory use. A separate one-well probe of the same
unfiltered workload completed, proving execution but not the declared scope.
The task-created large outputs from the failed attempt were removed after its
status was recorded.

The *older* September matched-batch pilot is separate and retains an obsolete
direct `CellProfilerRunRequest` constructor. The new genuine-well driver above
uses the current request and measured-submission APIs. Undefined object
threshold ratios and compiled plate-artifact axis ownership have owner-level
repairs with focused tests. Matched concurrency and timing-boundary study remain
outstanding. The full 30-case, four-mode sweep has not been run with this API.

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
