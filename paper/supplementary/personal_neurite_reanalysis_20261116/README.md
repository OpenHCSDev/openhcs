# Fixed-code re-evaluation of the frozen neurite analyses

These tables report **540 completed evaluations: three frozen methods × 180 original fields**. They are a retrospective re-evaluation after software corrections, not three new agents or new blind-development runs. The original [cohort and measurements](../personal_neurite_autonomous/cohort.json), author reports, source programs and images remain unchanged.

## What changed

The neurite engine file has SHA256 `eee1332e8bdb3b393c6cfa54440cb0f5404abde5a904f1e0f45e08d6c37f38f9`, matching revision `e2f55b0d7158545ae619c3e1bdb61bcf3b67b002`. The existing execution checkout was `ff31dda5b7425432d8d8eb6400bd5e151e46142f`. This engine includes crossing/branch-ownership and centreline-geometry repairs; changes in lengths are not attributed solely to the isolated crossing-function correction.

The captured function expressions retain author-specific preprocessing and parameters. Each replay verifies the original pipeline and image hashes and uses the captured **1.3556 µm** calibration. Three original-source pilot fields reproduced all nine recorded endpoints exactly: **27/27 checks, zero differences**.

Analysis 3 uses two original custom functions. Their obsolete `ProcessingContract.PURE_3D` annotation was translated to `Pure3DContract` in separately hashed execution copies; signatures and numerical-body ASTs are identical. The original files are included unchanged. The unused plate-summary helper was not executed during per-field image analysis. Both original and prepared source hashes and the prepared text are recorded with the measurements.

## Records and validation

- [Complete validation counts](validation.json).
- [Raw replay records and execution protocol](replay_records.zip): all nine successful job records, full measured per-cell/summary JSON, exact worker sources, job manifests and environment/code-origin fingerprints. A separate matched-field code-capture run is labelled as provenance, not counted among the 540 cohort evaluations. Python-source recovery bytes and unrelated editable UI-source differences remain in the retained recovery snapshot; this archive supplies their fingerprints rather than redistributing third-party source trees.
- Each analysis folder contains `paired_sites.csv`, `joined_wells.csv`, `treatment_effects.csv`, its exact original method files and `source_evidence.json`.

The existing `NativeSummary` reader validates cell identities, calibrated units, counts, per-cell totals, means and endpoint values. `SiteMeanWellAggregation` requires all nine unique sites and supplies the **unweighted nine-site well mean**. Existing endpoint declarations calculate treatment effects and guided-minus/over-analysis values. Original MetaXpress and scientist-assisted measurements are retained; differences involving the re-evaluated analyses are recomputed. Zero denominators remain undefined rather than becoming zero measurements.

The coded-to-physical well map comes from the retained evaluation tables. No replacement private source key or acquisition provenance was fabricated.

## Selected results

Pearson correlation uses mean outgrowth per cell across the same 20 wells. Fold changes below compare the 40 µM wells with each drug curve's own DMSO controls.

| Analysis | Mean-outgrowth r | FC-A outgrowth fold | Y27632 outgrowth fold | FC-A branches/cell fold | Y27632 branches/cell fold |
|---|---:|---:|---:|---:|---:|
| 1 | 0.988666 | 1.634914 | 1.685539 | 1.641895 | 1.735019 |
| 2 | 0.963214 | 1.329180 | 1.485467 | 1.257171 | 1.506562 |
| 3 | 0.996015 | 1.596988 | 1.655827 | 1.630678 | 1.722099 |

All three methods retain increased mean and total outgrowth at every nonzero dose. Pooling cells instead of taking the primary nine-site means changes outgrowth fold changes by at most **0.052012**. These comparisons establish treatment-response agreement, not biological tracing accuracy. Figure 6C–E retains the original frozen microscopy view; its quantitative panels and Supplementary Figure 2A–P use these re-evaluated tables.
