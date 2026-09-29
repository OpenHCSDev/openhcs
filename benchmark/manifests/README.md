# Benchmark Manifests

Before running native CellProfiler, follow the
[headless oracle bootstrap guide](../../docs/cellprofiler_headless_environment.md)
and retain its environment receipt with new benchmark evidence.

`official30_portable_axis1.json` is the reproducible 30-case CP-vs-OpenHCS
benchmark manifest. It avoids case-level absolute paths by declaring named,
self-materializing roots:

- `CELLPROFILER_EXAMPLES_ROOT`: sparse checkout of official CellProfiler example
  pipelines and datasets. Defaults to `~/.cache/openhcs/cellprofiler_examples`.
- `OPENHCS_BENCHMARK_DATASET_CACHE_ROOT`: auto-acquired dataset cache containing
  registry-backed tutorial/supplement sources. Defaults to
  `~/.cache/openhcs/benchmark_datasets`.
- `OPENHCS_AXISONE_SUBSETS_ROOT`: compatibility root for older axis-one
  manifests. The official 30-case manifest uses full dataset-cache roots and
  contains no benchmark-private execution subset.

The benchmark manifest loader materializes missing acquisition-enabled roots
before resolving case paths. Set `OPENHCS_BENCHMARK_AUTO_ACQUIRE=0` to disable
this and require pre-existing files.

Relative named roots are resolved against the benchmark command's working
directory when the manifest is loaded. The resulting absolute paths remain
stable when execution continues in worker or tool subprocesses.

Build or refresh registry-backed datasets directly with:

```bash
python scripts/prepare_cellprofiler_benchmark_datasets.py manifest \
  --cache-root "$OPENHCS_BENCHMARK_DATASET_CACHE_ROOT" \
  --output /tmp/registry_cases.json
```

Run the portable manifest with:

```bash
python scripts/benchmark_cellprofiler_vs_openhcs.py run \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /tmp/openhcs_cp30_run \
  --native-reference-root /tmp/openhcs_cp_native_refs \
  --no-memory-metric \
  --speedup-target 4
```

The native adapter resolves CellProfiler from an explicit executable path,
`CELLPROFILER_EXECUTABLE`, `PATH`, the active Python environment, or tool
environment roots declared through `OPENHCS_BENCHMARK_TOOL_ROOTS`. Local
workspace siblings are scanned through the same tool-root contract, so a
development checkout with `.venv-cellprofiler39`, `.venv-cellprofiler`, or
`.venv` does not need per-run shell setup.

The run emits parity/timing CSVs, phase timing, suite metadata, v7-style figures,
and registry-derived compatibility artifacts:

- `module_coverage_summary.json`
- `module_coverage_cppipe_modules.csv`
- `module_coverage_cppipe_settings.csv`
- `module_coverage_absorbed_modules.csv`

These compatibility artifacts describe registry-owned declarations, observed
corpus use, settings, execution scope, and processing-contract coverage. They do
not derive support claims from a copied upstream source tree, contain execution
observations or semantic-parity results, or emit semantic-family coverage.
Semantic-family CSVs under older presentation/result directories are historical
figure inputs.

The run also writes `observations.jsonl`, `observations.csv`,
`phase_timing.csv`, `summary.csv`, and `suite_metadata.json`. A temporary output
directory is suitable for diagnosis, but a published parity claim must retain
those files in durable storage together with the Git/manifest/native-reference
identities and exact command described in
`docs/source/architecture/measurement_equivalence_system.rst`.

## Run a measured well-throughput sweep

First check the modes, cases and missing sources without acquiring data or
starting an execution server:

```bash
openhcs-benchmark run-well-throughput \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /tmp/openhcs_well_throughput \
  --plan-only
```

For a bounded validation, run one declared case and mode in a new output
directory. Omit `OPENHCS_BENCHMARK_AUTO_ACQUIRE=0` if the manifest should fetch
missing sources:

```bash
OPENHCS_BENCHMARK_AUTO_ACQUIRE=0 openhcs-benchmark run-well-throughput \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --case ExamplePercentPositive --preset 8w_2c \
  --output-dir /tmp/openhcs_well_throughput
```

Without `--case` or `--preset`, the command runs every case and the manifest's
paired modes. It uses the manifest's worker start method unless `--start-method`
overrides it. `--well-count` and `--worker-count` select an explicit cross-product
instead of presets. A non-empty output directory is refused; use `--resume` to
continue its ordinary-route `well_throughput.csv`. Failed observations remain in
that CSV and make the command exit non-zero.

Use `--reuse-execution-server` to keep one client-owned execution server across
the selected observations. Its `server_lifecycle` column is `reused-per-sweep`,
and each `total_seconds` measures the observation after the server is ready.
Startup and shutdown are excluded from those per-observation totals; use the
default `fresh-per-observation` lifecycle to include them for each observation.
Both totals begin after the input workspace is prepared. The reused-server
option cannot be combined with `--max-memory-mb`, whose guard may kill the
shared server before later observations.
The two lifecycles have distinct resume hashes and cannot be mixed in figures.

To populate the CellProfiler-relative timing and speedup columns, first produce a
fresh native comparison summary with `openhcs-benchmark run`, then pass it to the
throughput command:

```bash
openhcs-benchmark run-well-throughput \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --native-summary-csv /tmp/openhcs_cp30_run/summary.csv \
  --output-dir /tmp/openhcs_well_throughput
```

Every selected case must have a usable native execution time in the summary.
The resolved baselines and the executable Python sources under `benchmark`,
`openhcs`, and the editable `external` packages participate in the resume input
hash. Rows measured against a different native summary or implementation are not
reused.

`ExampleIlluminationCorrection_Example1_AllMethod` intentionally sends all 72
selected files from its single synthetic source well to CellProfiler because
the upstream pipeline calculates illumination over `All images`. Its 1,800 s
native timeout includes headroom over a measured 945.82 s CellProfiler 4.2.8.1
run on the reference six-core development host.

Each successful observation retains a measured-run receipt and submitted
pipeline/configuration sources under
`<output-dir>/<case>/wells_<n>/workers_<n>/ordinary_run_evidence/<run-id>/`.
Inspect that directory with `openhcs-benchmark inspect-measured --output-dir
<evidence-dir> --report`. These measurements use the ordinary ZMQ pipeline route;
they are not interchangeable with the archived direct-execution data behind the
manuscript's Figure 5. Replacing that figure requires a separately validated
workload and new retained observations.
