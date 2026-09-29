# Radial geometry, 1-well ImagingFlow (2026-09-29)

The representative `ExampleImagingFlowCytometryObjectsInGrid` `1w_1t` run spent
about 4.5 s in `MeasureObjectIntensityDistribution`. Its center-propagation
backend traversed every object even though direct octile distances were valid
for more than 99.9% of pixels in the saved label maps. Four distinct maps had
only 7, 1, 1, and 0 objects requiring an obstructed-path fallback. The same
measurement work also computed minimum-enclosing circles using a Python copy
of the NumPy 1.24 tie-order sort while shape and intensity already used an
equivalent Numba implementation.

The estimated ceiling from the prior real-pipeline profile was about 0.7 s of
center propagation plus 1.2 s of circle construction across the distinct
label maps. The candidate keeps the existing propagation backend for
obstructed objects and uses one sort implementation for all three consumers.
Saved-image radial measurement arrays matched exactly. Random connected
components, a holed object, and touching objects matched the full propagation
backend to `1e-12` in distance and exactly in propagated labels.

`review_base_1w_fresh_runs.csv` compares this branch directly with its PR #170
base. Both checkouts were run once to populate Numba caches, then measured
again through the ordinary fresh-server route. The warm runs produced the same
`BF_cells_on_grid.csv` SHA-256:

| Warm run | Compile | Execute | Total | Intensity-distribution step |
| --- | ---: | ---: | ---: | ---: |
| PR #170 base | 2.159 s | 19.587 s | 42.905 s | 4.907 s |
| Radial geometry candidate | 2.192 s | 18.383 s | 41.741 s | 3.799 s |

That is 1.204 s less execution time and 1.164 s less total time on the direct
review base. Its absolute total is high because this base does not include the
other independent runtime PRs integrated in the local performance checkout.

`imagingflow_1w_fresh_runs.csv` records the ordinary ZMQ outcomes route with
fresh servers on that integrated checkout, one thread, identical manifest and
images, and the same output CSV SHA-256 in every run. The sequence was control,
candidate, candidate, control. The first candidate populated new-worktree
Numba caches; its 15.75 s compile time is excluded from the warm comparison.

| Run | Compile | Execute | Total | Intensity-distribution step |
| --- | ---: | ---: | ---: | ---: |
| Control A | 3.144 s | 19.883 s | 25.669 s | 4.524 s |
| Warm candidate | 3.166 s | 18.220 s | 23.976 s | 3.295 s |
| Control B | 3.149 s | 20.200 s | 26.002 s | 4.573 s |

The warm candidate saves 1.66–1.98 s of execution and 1.69–2.03 s of total
time against the adjacent controls. In the separate reused-server official30
suite, all 30 observations succeeded and every generated CSV/image file was
byte-identical to the saved control (`full30_output_parity.csv`). The suite's
execution sum changed from 89.231 to 85.772 s, though those two complete
sweeps were not an interleaved timing comparison and the candidate had colder
compile caches.

Reproduce a fresh single-case observation with:

```bash
OPENHCS_CPU_ONLY=true \
OPENHCS_REFERENCE_EXPORT_PIPELINES_ROOT=benchmark/reference_exports/official30_value_completion_20260914 \
python scripts/benchmark_cppipe_well_throughput.py \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /path/to/new-output \
  --case ExampleImagingFlowCytometryObjectsInGrid --mode 1w_1t
```

The throughput CSV's `total_seconds` starts after source workspace preparation.
On the integrated checkout, Granularity (~5.3 s) and spreadsheet export
(~2.6 s) remain the largest single-thread steps after this geometry change.
