# Own-data commercial neurite comparator: verified inventory and protocol

15 September 2026. Read-only inventory; no plates reanalysed, GUI state changed,
commercial files modified or matched numerical OpenHCS results claimed.

## Finding and source identity

A new **well-level** comparison is feasible because the commercial exports and
their exact raw images are present. They are a distinct neurite experiment
inside the September axotomy container, not the four already-analysed September
microfluidic PRE/POST acquisitions. The existing axotomy analysis cannot be
joined to these commercial results by row/well labels.

Source root:
`/run/media/ts/0BA20E780BA20E78/axotomy_testing/2026-09-04-(complete)/neurite outgrowth`.

| Commercial acquisition | MetaXpress plate ID | HTD unique plate identifier |
| --- | ---: | --- |
| `2026-09-06-F04-analogs_Plate_24098` | 24098 | `84d8475d-121d-4697-9bad-510ac1d96c1d` |
| `2026-09-06-F04-controls_Plate_24099` | 24099 | `dddfa985-9934-44cb-abbe-d63b0d49ecd3` |

The entire non-image inventory is `results.xlsx` and each plate's same-named
HTD, duplicated byte-for-byte inside `TimePoint_1/`. The workbook has exactly
one sheet, `results`, 206 rows and 25 columns: two metadata/header blocks plus
96 well rows per plate. Sixty wells per block have values, B–G / columns 2–11.
No additional sheet, field/site export, individual-cell table, outline file or
commercial analysis-settings/pipeline file was found in this source tree.

Each plate contains 1,080 TIFFs: 60 wells × nine sites × two channels.
All 2,160 TIFF headers were checked, not just a sample. Every image is a
1024 × 1024 uint16 single plane with spatial calibration enabled at
**1.3556 µm/pixel in X and Y**, and MetaXpress/MetaMorph version `6.7.2.290`.
HTD records one time point, `ZSeries=FALSE`, `ZSteps=1`, a selected 3 × 3 site
grid and `w1=DAPI`, `w2=FITC`. FITC is the acquisition channel name; a specific
neuronal stain, cell type and treatment concentrations are not recorded here.

There are 1,080 complete raw site/channel pairs, no missing image keys within
the selected 60 wells per plate. Filename well/site identities agree with
every TIFF XML `stage-label`. The potential raw-image key is
**HTD plate UUID + well + site + time-point index 1 + Z-step index 1**; channel
is a bound source identity, not another independent observation. Acquisition
timestamps and physical Z positions exist per TIFF but are not additional
time/Z series. The commercial summary key available here is only **plate ID /
plate name + well + summary Z Step 1**; site cannot be recovered from its rows.

## Commercial endpoints and aggregation limits

Headers include Number of Cells, Total Outgrowth, Mean Outgrowth Per Cell,
Total/Mean Processes, Total/Mean Branches, Total/Mean Cell Body Area,
Straightness, Mean Outgrowth Average Intensity, Cells Significant Growth and
%Cells Significant Growth, plus a laser-focus score. All are labelled
`(Neurite Outgrowth)`. Additional `Cell:` headers have one scalar per well,
including Assigned Label #, Total Outgrowth, process-length summaries, branches,
straightness, area and intensity. They are **aggregates, not individual-cell
records**; no per-cell correspondence or spatial accuracy can be measured.

Number of Cells is non-integer in 53 of 60 populated wells on each plate,
consistent with nine-site averaging. For example, analogs B02 reports
174.222222 cells; Total Outgrowth / Number of Cells is about 150.93142, while
Mean Outgrowth Per Cell is 154.004529. The `Cell: Total Outgrowth` column is
150.93142. This establishes that mean-of-ratios and ratio-of-aggregated-totals
are different exported endpoints. It does not prove the full aggregation
settings. Exported measurement units, significant-growth criterion, site
weighting, exclusion policy and analysis parameters are not stated in the
workbook/HTD. TIFF calibration alone does not establish the workbook length
or area units. Verify these before a numerical comparison; do not multiply
commercial values by nine or treat them as well totals by assumption.

## Verified treatment declarations

Both HTD Description and workbook Description agree on these commercial layouts:

| Plate | Rows | Columns 2–6 | Columns 7–11 |
| --- | --- | --- | --- |
| analogs | B/C | F04 | 09-027 |
| analogs | D/E | 06-049 | 09-037 |
| analogs | F/G | 08-115 | 09-079 |
| controls | B/C | Y27 | epob |
| controls | D/E | FC-A | FC-A+EpoB |
| controls | F/G | DMSO | DMSO |

Preserve the source spelling/codes and column identities; the five columns
must not be called a dose series without a concentration declaration. Biological
replicate identities and concentrations remain unknown.

The earlier user correction B/G=DMSO, C=FC-A, D=F04, E=EpoB, F=EpoB+FC-A is
explicitly scoped by `openhcs_reanalysis_20260908/plate_treatment_metadata.json`
to the separate September **P1/P2 microfluidic** acquisitions. It is not the
commercial plates' treatment authority. Those corrected existing results are
under `openhcs_reanalysis_20260908/results/treatment_corrected_20260909/`:
two 336-row method/QC tables, 35 complete PRE/POST pairs and 31 eligible
axon/PRE ratios. Their endpoints are segmented PRE/DAPI/CTB objects, skeleton
pixels/components, foreground pixels and skeleton pixels per PRE object.
These are stitched acquisition-level, method-defined technical measurements,
not MetaXpress cell-associated outgrowth lengths. Their absent/incomplete wells
and QC exclusions remain NA; no commercial well fills an axotomy gap.

## Proposed matched comparison

1. Freeze workbook/HTD hashes, raw identities, commercial aggregation/units and
   explicit layout/concentration metadata. Derive an input-only site inventory
   and a separate comparator table. Preserve absent/unreported entries as NA;
   document contamination exclusions from an actual declaration, not filename
   absence. In this commercial source, selected image keys are complete.
2. Through the supported GUI/MCP workflow, load these exact two raw plates into
   a separate trial/output root. Use the corrected neurite/soma abstraction,
   not the stitched microfluidic axon skeleton recipe. Give a fresh authoring
   trial assay aim, verified DAPI/FITC channel identities and raw inputs, while
   keeping commercial values and solved workflows out of its authoring context.
   HTD Description contains treatment labels; if exposed by plate inspection,
   record that supplied biology rather than claiming treatment blinding.
   Preselect development wells deterministically
   before inspecting algorithm outputs; freeze the workflow before held-out
   execution. Record software revision, recipe, calls/time and every failure.
3. Following the user's stitching amendment, combine the nine sites into a
   channel-registered well mosaic before segmentation. Preprocess and composite
   the channels into a shared registration reference, compute one positions
   artifact, then apply those same positions to the original non-composited
   channels. Keep registration preprocessing separate from analysis input.
   Retain exact tile
   transforms, source identities, mosaic labels, paths and cell-associated
   measurements. Match each mosaic's source fields by the full key and join
   its summary to the corresponding commercial well. Primary candidates
   are cell count and mean outgrowth per cell; total length, processes and
   branches require equivalent definitions before quantitative comparison.
   Never join `P1/P2` to `24098/24099` or pair unrelated wells by drug name.
   A mosaic measures each object once across tile overlaps; the commercial
   export appears to average separate-site results. Preserve these aggregation
   definitions when comparing counts and lengths. Use calibrated mosaic area
   and documented endpoint definitions where normalisation is appropriate;
   neither a sum nor multiplication by nine establishes a matched well total.
4. Report paired well differences and drug/control contrasts separately from
   visual quality. Compare treatment direction and effect sizes against the
   controls plate's own DMSO observations, retaining column/dose strata. Wells
   and fields are not independent agent trials; biological replication is not
   established by this inventory. Do not tune the method to force commercial
   agreement. This is an assay comparator, not a manual biological reference.
5. Review preselected matched raw-image captures and OpenHCS object/path overlays
   for soma splits, missed processes and crossing assignments. Claims of better
   spatial accuracy require independent annotations or expert adjudication on
   those images. The commercial aggregate alone cannot establish per-cell
   accuracy, and commercial spatial overlays are not present for direct review.
   A useful result could be a reviewable workflow with different measurements
   and a consistent assay response, with documented qualitative advantages;
   it is not evidence of accuracy simply because both drug responses agree.

No matched OpenHCS/commercial metric receipt is produced yet: corresponding
OpenHCS outputs for these two acquisitions were not found in the inspected
commercial tree, existing September reanalysis or OpenHCS workspace records.
Raw-to-commercial well matching is available; prediction matching awaits new
coordinated GUI execution and verified aggregation/measurement units.

## Compact source receipts

- `results.xlsx`: SHA256 `ae029a925d05ec16e91105fcb77fedd0a5313f059364b3214caeffc420919e5f`.
- analogs HTD (both copies): SHA256 `870f300dcd5cf3d6274a55f1b6106342439eefbbbf9db8fa155445e28b632baa`.
- controls HTD (both copies): SHA256 `d48bc1b841fbd0fba65918e294e4068d7464623ddf0d6ccea12d898d3d559eb6`.
- Header/identity audit: 2,160 unique raw image keys, 1,080 complete channel
  pairs; uniform representation/calibration; every stage-label agrees.
  TIFF `_IllumSetting_` independently confirms 1,080 DAPI `w1` and 1,080 FITC
  `w2` images, rather than relying only on the HTD wavelength declarations.
  Full raw-image byte checksums have not been frozen by this read-only inventory.
