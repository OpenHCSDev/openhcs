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

Local receiving: 134 focused existing export/matched controls pass, including
actual two-axis spreadsheet materialization and scoped SQLite relationship
comparison. Public two-assignment qualification is pending; this document
claims no throughput result or minimum speedup.
