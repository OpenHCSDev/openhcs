# Genuine-well matched-output pilot (2026-09-23)

This is a bounded **output-equivalence and new-API execution check**, not a
CellProfiler/OpenHCS speed comparison or replacement for manuscript timing
figures. The driver is `benchmark/matched_cellprofiler_batch.py`, using the
`cp_tutorial_translocation_final` case from
`benchmark/manifests/official30_portable_axis1.json`.

The input consists of eight actual wells (A01, A12, B01, B12, C01, C12, D01,
D12), one site and two source channels per well. Native CellProfiler 4.2.8.1
ran in a Python 3.9 environment; OpenHCS 0.8.6 ran through an owned persistent
ZMQ execution server with the ordinary compile/run submission API. Both
pipelines requested eight TIFF overlays, one SQLite database, and one CPA
properties file. Optional automatic segmentation-artifact materialization was
disabled, leaving explicit exports intact.

| Evidence | Native batches | OpenHCS batches | Result per batch |
| --- | ---: | ---: | --- |
| Main pilot | warm-up + 3 observed | warm-up + 3 observed | 8/8 axes; 10 native, 10 candidate, 10 declared files; no database/image differences, missing exports, or extra files |
| Strict-policy confirmation | warm-up + 1 observed | warm-up + 1 observed | Same counts and zero differences under the shared strict CellProfiler equivalence policy |

The strict policy is recorded in
`strict_confirmation/equivalence_policy.json`: numeric and image absolute and
relative tolerances are `1e-6`, image differing-pixel allowance is zero, and
the broader compatibility relaxations are disabled. The main pilot used the
then-current runtime comparison policy; its output pairs were subsequently
checked with the strict policy, and the independent strict confirmation is
retained here as a reproducible receipt of that condition.

`report.json` and `strict_confirmation/report.json` contain per-batch file
counts, full SHA-256 output inventories, differences, source hashes, and
endpoint PID. The `candidate_evidence/` directories retain submitted Python
sources and measured pipeline receipts. Full image/database outputs and
runtime observation pickles are intentionally not tracked. Both runs record
`source_dirty=true`, so their source-tree provenance is useful but not a
clean-checkout publication receipt. Absolute paths in the generated reports
refer to task-local directories that were not retained.

The driver accepts `--manifest`, an empty `--output-dir`, `--repetitions`, and
`--native-python` (the CellProfiler 4.2.8.1 Python 3.9 virtual-environment
entrypoint). The native executable must be the venv entrypoint, not its
resolved base interpreter. Its output root must be newly empty. The official
dataset and native environment must be available locally.

No comparative performance claim follows from this pilot. Native invocation,
OpenHCS server-job, and OpenHCS execute-phase timers do not yet have a matched
steady-state boundary, and matched process concurrency above one was not
tested. The full 30-workflow/four-mode paper sweep remains outstanding.
