# Corrections discovered after the panel input freeze

The 14 September Sol panel reviews the fixed PDFs identified in
`paper/review/slas-panel-20260914/input_manifest.md`. Do not silently replace
those inputs. This note is not part of the reviewer assignment.

## Image-reference selection

The earlier audit and frozen manuscript counted three image-comparison
workflows. The advanced-segmentation tutorial's five illumination NPY arrays
are actually under `native_cellprofiler_selected_source_workspace/_source/`.
They are input images, outside the resolved `*_native_cellprofiler` comparison
directory, which contains SQLite/CPA outputs. This directory distinction was
reported by the benchmark agent and independently checked in the retained tree.

The benchmark agent rechecked all 30 cases through the actual reference resolver.
Parent independently parsed
`benchmark/results/official30_reference_root_audit_20260914/reference_inventory.csv`:
21 CSV, three SQLite, one NPY-only and five empty profiles. Only AllMethod and
translocation-final enable image comparison under the historical value-only
policy. Advanced-segmentation has zero compared images and five images outside
the selected reference directory. Update the manuscript, supplement and claim
ledger from this audit. Do not infer compared image counts by recursively
inventorying a profile's ancestor directory. The panel's opinions cannot validate
this source-level fact.

## Five new export cases

The benchmark agent's initial report of five fresh passing cases was withdrawn:
the fresh-reference run had not enabled image-value comparison. Independent
per-file checks found discrepancies. The authoring draft never incorporated the
withdrawn five-pass claim. New results require a receipt showing enabled value
comparisons and the actual pass/fail inventory; preserve the invalid run's
provenance rather than relabeling it as successful value validation.

These facts should be presented separately from the panel's independent review
of the frozen manuscript. No new scientific result is established by reviewer
agreement or a passing CI job.

The subsequent diagnostic run reporting 1/5 workflows and 3/8 artifacts passing
also has an execution-provenance mismatch: the benchmark agent reports that the
0.8.5 client attached to a preexisting 0.8.4 execution server. Treat these results
as diagnostic only, not current-source validation or confirmed current algorithm
defects. Exact endpoint compatibility enforcement and a fresh isolated rerun are
in progress. This update records the agent's finding, not a parent-verified rerun.

## Reviewer factual checks

Reviewer B's supplement reaction says most unequal total-phase ratios favor
CellProfiler. Recomputing `median_native_total_phase_seconds /
median_openhcs_total_phase_seconds` from the original single-process summary,
excluding ExampleWoundHealing, gives 24 of 29 ratios above one, five below one,
and median 3.417713024536691. That reaction is numerically reversed. Preserve the
raw review, but do not adopt this assertion in the panel synthesis. The differing
timing boundaries still prevent a like-for-like speed claim in either direction.
