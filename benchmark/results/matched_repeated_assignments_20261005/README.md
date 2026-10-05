# Measured repeated source assignments

`benchmark.matched_cellprofiler_batch --repeat-assignments N` selects one
genuine source well using the existing `--well-count 1` / `--well` selection,
then runs that complete input independently N times in both tools. This is a
repeated-source workload, not a claim that the source contains N genuine wells.
The default without `--repeat-assignments` still selects genuine wells.

OpenHCS uses the existing source-workspace assignment projection and execution
axis namespace. Native CellProfiler prepares the original physical input once,
then invokes the same loaded pipeline separately in each corresponding output
namespace. Parallel native jobs partition whole assignments; genuine-well
jobs retain their original image-set partitioning. Native Java startup,
pipeline loading, OpenHCS catalog/kernel preparation and one full warm-up batch
precede measured repetitions.

For example, with the ordinary headless native environment configured:

```sh
python -m benchmark.matched_cellprofiler_batch \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --case ExampleIlluminationCorrection_Example3 --well-count 1 \
  --repeat-assignments 2 --openhcs-workers 1 --native-jobs 1 \
  --repetitions 3 --native-python /path/to/native-venv/bin/python \
  --output-dir /path/to/fresh-evidence
```

Use the manifest's actual case name and declared dataset-root environment.
`--all-cases` supports the same scope through the existing suite lifecycle.

Spreadsheet and database exporters retain the image numbers they actually
assigned as derived views on their materialized outputs and step observations.
Scientific comparison selects each assignment through those admitted numbers
and artifact execution scopes. It does not guess image-number blocks from
maximum values, rewrite saved CSV/SQLite identifiers, or export runtime pixels
through OUTCOMES. Local comparison numbering uses the existing offset law;
noncontiguous admitted local domains explicitly fail rather than invent an
ordering. Cross-assignment relationship endpoints and unowned image numbers
also fail. Duplicate saved paths with conflicting numbering ownership fail.

Every assignment compares complete measurement schemas, values, relationships,
images and file inventories against its native output namespace. Consolidated
OpenHCS export files remain unchanged on disk. The report distinguishes native
module-to-post-run and complete invocation intervals, and OpenHCS execution,
compilation and complete client-operation intervals. Multiwell native prices
are measured batches, never extrapolated singleton timings.

Receiving: 134 focused existing export/matched controls pass, including actual
two-axis spreadsheet materialization and scoped SQLite relationship comparison.
The ordinary Example3 qualification now passes one complete warm-up and one
measured batch: both native assignments process one image set, OpenHCS executes
both axes, and all four declared images match exactly with complete inventories.
This recipe has no measurement export; it does not establish public multiwell
CSV/SQLite parity for other recipes. [receiving.json](receiving.json) retains
the precise scope, source, guards and raw evidence hashes.

The single measured native batch takes 1.271224 s from first module through
final post-run and 1.350442 s for the complete invocation. OpenHCS takes
0.358190 s execution, 0.161058 s compilation and 0.653026 s for the complete
client compile/execute operation. Server/catalog startup is excluded. This is
infrastructure qualification, not the final three-repeat matrix or a minimum
speedup claim. The native first-module interval also includes setup between
assignments; keep that scope visible when reporting it.

The first launch failed before native/candidate execution because the new
caller passed a plain list instead of the existing well-filter configuration.
That failure is retained. The successful raw report initially overwrote the
compile submit/wait durations while grouping duplicate phase names. Corrected
totals aggregate all original immutable receipt intervals through
`PhaseTimingRecord.seconds_by_phase`; saved raw evidence is not rewritten.

The native subprocess now honors the selected manifest's existing
`CellProfilerRunRequest.timeout_seconds`. A declared budget covers each actual
warm-up/measured invocation and repeated assignment; `None` remains unlimited.
The unrelated hardcoded 900-second fallback is removed.
