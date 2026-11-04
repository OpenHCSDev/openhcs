# Branching discrepancy: saved-record audit

This audit checks the three frozen neurite analyses against the original MetaXpress workbook. It recalculates arithmetic from saved tables; it does not rerun image processing or replace any original measurement.

## What was verified

The recovered `results.xlsx` has SHA256 `ae029a925d05ec16e91105fcb77fedd0a5313f059364b3214caeffc420919e5f`, matching the retained source evidence. The existing workbook decoder reproduces all nine saved reference endpoints at the 20 matched wells, checked separately for each author (540 comparisons, 180 distinct reference values). All 540 native site-level records satisfy `branches / detected cells = branches per cell` exactly. These records cover the same 180 sites evaluated by three methods. Their well values reproduce the declared unweighted mean of nine site endpoints.

Responses use two technical wells at each dose and that drug's own two vehicle wells. These are not biological replicates.

## The smaller fold responses include higher native baselines

Values below are branches per detected cell; fold is treated / vehicle, without units. Treatment is 40 µM.

| Method | FC-A vehicle | FC-A treated | FC-A fold | Y27 vehicle | Y27 treated | Y27 fold |
|---|---:|---:|---:|---:|---:|---:|
| MetaXpress | 1.4707 | 4.4080 | 2.9973 | 1.2827 | 4.1821 | 3.2603 |
| Analysis 1 | 2.3172 | 3.7812 | 1.6318 | 2.1362 | 3.7049 | 1.7344 |
| Analysis 2 | 5.3188 | 6.5752 | 1.2362 | 4.8272 | 7.2512 | 1.5021 |
| Analysis 3 | 3.8947 | 6.3312 | 1.6256 | 3.7204 | 6.3719 | 1.7127 |

Thus a smaller relative response does not mean uniformly smaller absolute branch measurements: analyses 2 and 3 have higher treated endpoints as well as substantially higher baselines. Their absolute gains are nevertheless smaller than the exported MetaXpress gains.

## Pooling does not explain the discrepancy

The native endpoint is `mean(branches_i / cells_i)` across nine sites. As a sensitivity calculation, replacing it with `sum(branches_i) / sum(cells_i)` gives:

| Analysis | Drug | Original gain | Cell-pooled gain | MetaXpress exported gain |
|---|---|---:|---:|---:|
| 1 | FC-A | 1.4641 | 1.5364 | 2.9373 |
| 1 | Y27 | 1.5688 | 1.6027 | 2.8994 |
| 2 | FC-A | 1.2563 | 1.3110 | 2.9373 |
| 2 | Y27 | 2.4239 | 2.4459 | 2.8994 |
| 3 | FC-A | 2.4365 | 2.5301 | 2.9373 |
| 3 | Y27 | 2.6515 | 2.6868 | 2.8994 |

The change is only 0.0220–0.0936 branches/cell and leaves every comparison below the reference gain. The alternative is diagnostic arithmetic, not a correction to the frozen endpoint.

MetaXpress's exported mean is also distinct from dividing its exported totals. For example, B02 reports 4.320854 branches/cell, while exported total branches / exported cell count is 4.2754854401. Using that alternative ratio changes the reference FC-A gain from 2.9373 to 3.0522 and Y27 from 2.8994 to 2.8963; it does not remove the discrepancy. This disagreement does not identify MetaXpress's internal weighting or eligibility rule.

## What a branch means in the frozen native implementation

The cohort fixes software commit `2b404bdfa627a3c87f29324d6c068fcf0f5b9775`. In that commit, `openhcs/processing/backends/analysis/neurite_outgrowth.py:1489–1516` defines a branch as a qualified, owner-specific junction with three distinct image corridors, excluding crossing cores and qualifying a short proximal soma arm. Nearby qualified groups are clustered and counted once per cell. The count is not the number of exported paths, graph nodes or primary-process roots. Per-cell measurements count those qualified branch clusters (`:3809`); field summaries sum them and divide by the detected cell count (`:3893–3912`). The exported well endpoint then averages the nine field ratios.

These are count endpoints, not outgrowth-length conversions. The saved native records consistently use the declared micrometre coordinate unit, and the cohort's XY calibration is 1.3556 µm.

## Reproduce the arithmetic

From the repository root, run:

```sh
python paper/figures/audit_personal_neurite_branching.py \
  --workbook /path/to/original/results.xlsx \
  --output /path/to/branching_discrepancy_audit.json
```

The command uses the existing endpoint/workbook decoders, checks the workbook against its frozen source hash, records every input and generator hash, and reads the branch implementation from the cohort's recorded Git commit. It refuses an output path that would overwrite an input. The machine-readable result is retained alongside this note.

## Remaining scientific boundary

The saved records establish the numerical discrepancy, its baseline contribution, the native branch definition and the small effect of the tested pooling alternatives. They do not expose MetaXpress's internal branch-event, crossing or cell-eligibility implementation, or supply biological ground-truth tracing. Consequently they cannot establish which method is more accurate or attribute the remaining discrepancy to a specific vendor or native detection error. Such attribution needs matched object/topology inspection under verified vendor settings or independently labelled traces, not a replacement of the saved endpoint.
