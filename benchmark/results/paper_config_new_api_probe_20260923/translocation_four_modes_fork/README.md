# Paper-manifest four-mode execution probe

This is one bounded `cp_tutorial_translocation_final` run of each mode declared
by `benchmark/manifests/official30_portable_axis1.json` through the ordinary
compiled ZMQ execution API. It is **not** the 30-workflow Figure 5 rerun or a
matched CellProfiler speed comparison. The manifest's first-source-well filter
selects A01 site 1 with two channels; virtual well IDs repeat that same input.

| Mode | Successful wells | Distinct observed worker PIDs | Server job (s) | Peak process-tree RSS (MB) | Explicit output files | Plate `ExportToDatabase` (s) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `1w_1t` | 1/1 | 1 | 3.332 | 1083.5 | 3 | 2.267 |
| `8w_2c` | 8/8 | 2 | 23.530 | 2549.8 | 10 | 18.846 |
| `12w_3c` | 12/12 | 3 | 32.814 | 3349.8 | 14 | 27.804 |
| `16w_4c` | 16/16 | 4 | 42.827 | 4171.3 | 18 | 36.936 |

Each output set contains one TIFF per virtual well, one CPA SQLite database,
and one CPA properties file. The `progress_events.csv` and `worker_lanes.csv`
files show actual worker PIDs and work; merely configuring the count was not
accepted as proof. `step_timings.csv` locates the plate-scoped export. The
retained `runtime_outcomes.pkl.gz` files were read back and each reports every
expected axis successful with the execution ID in its receipt. Submitted
pipeline and global-config snapshots match the SHA-256 values in the retained
receipts byte for byte. The copied CSVs have normalized LF line endings; source
snapshots and outcome files have not been rewritten. Microscopy outputs were
counted but not committed, so this probe is not output-value equivalence proof.

The global mode declaration controls worker count, threading, and start method;
the imported pipeline inherits those fields rather than overriding them.
Earlier probes in this directory retained the importer's explicit `spawn`
setting despite the manifest's `fork`, which caused the three- and four-worker
conditions to use fewer distinct processes than configured. Those rows are
diagnostic failures, not paper data. The single `8w_2c_verified_2pid` probe
proved two processes under that earlier `spawn` override, but did not prove
execution under the manifest's declared start method.

The historical May Figure 5 inputs report much shorter execution times, but
the co-committed May implementation of `ExportToDatabase` was a pass-through
stub. Their exact executed commit, compiled plans, and output inventories are
not retained. This current output-complete probe is therefore **not a direct
timing comparison** with the historical rows; the latter cannot establish
current output-complete throughput.

This run used OpenHCS 0.8.6 from the current checkout with the benchmark runner
whose SHA-256 is `e06f219e959168c9c007fd2e3cbe85db9d2c88b0708e1fe53b256ffc0987bcc5`.
The manifest SHA-256 is
`7f11549c0bc870f9ce2792afc9176f52b6a2b83236e47b33cbedb4a2cac73267`.
Unrelated worktree state was present; this is not clean-checkout publication
provenance. Reproduce into a new empty directory with:

```sh
env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 PYTHONHASHSEED=0 \
  .venv/bin/openhcs-benchmark run-well-throughput \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /tmp/openhcs-paper-four-modes-reproduction \
  --case cp_tutorial_translocation_final --max-memory-mb 6000
```
