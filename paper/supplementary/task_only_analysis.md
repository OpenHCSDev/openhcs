# Task-only authoring and independent repair

## Evaluation design

These trials extend the earlier prospective three-assay evaluation without
replacing it. Fresh `gpt-6.1-sol` authors received their task, named acquisitions,
the packaged OpenHCS skill and assigned MCP/viewer resources. Their tasks did
not disclose reference labels, earlier authors' pipelines, accepted parameters
or the coordinator's image diagnoses. Authors selected and revised scientific
settings from their own measurements and visual review. Evaluation scores were
computed by the coordinator after scientific freezing and were not returned
to the authors.

The skill includes general image-analysis principles and examples. Consequently
task-only authoring does not mean an agent receives no domain knowledge. It
means the author must apply that knowledge to its own data without an accepted
dataset-specific solution or subsequent scientific coaching. Runtime and
contract corrections remain part of each trial's operational record.

The first/final comparisons below use exactly the same inputs and reference
definitions within each authoring trial. A first result means the first
completed prediction under the initial scientific settings, not an error-free
first command. References remain unavailable to the author during development;
the evaluated acquisitions do not constitute an unseen image partition.

## H001: notebook-derived bright objects

The H001 image is a single 254 x 256-pixel scalar field. Its predeclared primary
reference is a pinned Haase notebook's scikit-image label array, not a manual
biological annotation. The source is the
[BioImageAnalysisNotebooks algorithm-validation collection](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/tree/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation),
at commit `68845a1afaf53bf601958a3fa7d86f3cf8a43219`. The neutral input is the
original `blobs.tif`, SHA-256
`26403a7c2a11921535499ff86798b73e09b8ac5786329bce8fa4a57fd9933fee`;
only the neutral input was disclosed to the author, while the notebook and
reference outputs were withheld. The original task-only author `H001_FRESH586_96`
retained four attempts and froze its scientific bundle at
2026-10-04T05:51:25.756471 UTC. The unchanged
`benchmark/score_instance_labels.py`
uses maximum-total-IoU one-to-one assignment and accepts assignments with
intersection over union at least 0.5; object label numbers are ignored.

| Measure | First settings, a01 | Final settings, a04 |
| --- | ---: | ---: |
| Reference objects | 64 | 64 |
| Predicted objects | 63 | 61 |
| Matched objects | 59 | 59 |
| Excess / missed objects | 4 / 5 | 2 / 5 |
| Object precision | 93.65% | 96.72% |
| Object recall | 92.19% | 92.19% |
| Object F1 | 92.91% | 94.40% |
| Foreground IoU | 98.19% | 98.19% |
| Mean matched-object IoU | 95.66% | 96.96% |

The repair reduces excess partitions and improves matched-object geometry; it
does not recover additional reference objects or foreground. The author's
final report retains uncertain lobed groups, possible merges, small-focus
exclusions and truncated border objects. Its 61 instances are a defined
bright-object estimate rather than an exhaustive biological census.

Supplementary Figure 18 shows native raw/first/final witnesses from this same
scored author. The overview uses raw window 8–152; the upper-right detail uses
8–248, gamma 1, with filled ROI opacity 0.7. It makes the local elongated-body
false-split repair visible without substituting another trial's result. The
[independent source review](../../figure-collection-20261004/H001-FRESH586-SCORED-NATIVE-REVIEW.rst)
records original capture hashes, matched native states and the independent
verification of all 417 frozen file sizes and hashes. Clipping and scaling are
recorded in the figure receipt; original PNG bytes remain alongside the figure.

An earlier independent author, `H001_FRESH10_96`, scored 62.65% on its first
prediction and 91.34% on its final prediction using the same reference and
scorer. Different packaged versions and independently selected settings
confound a causal attribution to the skill. This retrospective comparison is
not a randomised ablation or an estimate of success on a new dataset.

The retained [H001 evaluation receipt](task_only_analysis/h001-fresh586-postfreeze-evaluation.json)
contains both authors' scorer outputs, derived scores, exact prediction paths
and hashes, reference/scorer identities, freeze digests and invocation. The
primary reference SHA-256 is
`f051ee7663f34fa9093e0d62afd409524408c9074582f95320a605c932245cb0`.
The original H001 scientific report records successful exact viewer/native
closure but a recorded MCP-client exit code of 2, whose cause was not
independently established. Scientific agreement does not erase that operational
qualification.

## BBBC039: paired repair and full-corpus coverage

The original author `BBBC039_FRESH612_96` received the public full-200-field DNA
task without annotations or earlier results. The first scientific settings
produced three frozen masks following technical stack/conversion corrections.
The final settings were applied to all 200 fields. The unchanged installed
`benchmark.validation.scoring.instance_segmentation_metrics` and
`ValidationReferenceStrategy.INSTANCE_MASKS` reference decoder supplied the
evaluation, using one-to-one matching at IoU at least 0.5. Source-set identity
and the original DNA channel define the reference join.

| Measure | First settings, same three fields | Final settings, same three fields | Final settings, all 200 fields |
| --- | ---: | ---: | ---: |
| Reference nuclei | 299 | 299 | 23,615 |
| Predicted instances | 274 | 288 | 21,674 |
| Matched objects | 260 | 274 | 20,521 |
| Excess / missed objects | 14 / 39 | 14 / 25 | 1,153 / 3,094 |
| Precision | 94.89% | 95.14% | 94.68% |
| Recall | 86.96% | 91.64% | 86.90% |
| Pooled object F1 | 90.75% | 93.36% | 90.62% |
| Mean field F1 | 90.97% | 93.76% | 89.24% |
| Mean field panoptic quality | 80.67% | 82.26% | 78.71% |

The three paired fields are `20585_F14_7`, `20586_A06_6` and `20630_A02_1`.
All three improve under the final settings; their pooled F1 increases by
2.606 percentage points. Scientific step declarations change only the marker
suppression distance from 14 to 10 pixels. The evaluation does not extrapolate
the first three outputs into a first-attempt score across 200 fields.

Of the final 200 fields, 135 reach F1 at least 0.90 and 180 reach at least 0.85.
Ten remain below 0.80. Three annotation-empty fields remain in the primary
evaluation with F1 zero and 37 excess predictions in total. Empty annotations
alone do not establish biological absence. The final total undercounts the
reference by 1,941 objects. The scorer's split/merge totals use any positive
overlap and therefore are not visually verified biological split/merge counts.

The preceding `BBBC039_FRESH594_96` full-200 baseline reached pooled F1 89.86%
on exactly the same source keys. Relative to that baseline, 139 fields improve,
45 regress and 16 are unchanged. This comparison does not use its rejected
two-field final revision as a full-corpus result. The separate earlier 120-field
result is not interchangeable with either full-200 evaluation. Neither these
comparisons nor the public train/test/validation names establish unseen
generalisation: the author inspected some sources during development.

The retained [BBBC039 evaluation receipt](task_only_analysis/bbbc039-fresh612-postfreeze-evaluation.json)
contains all 200 per-field scores, the paired first outputs, exact source joins,
pipeline hashes, frozen prediction hashes, scorer identities and the preceding
same-key comparison. The original freeze-manifest SHA-256 is
`b4dd04fc1b897fca1257aead36d43b2938358df78adf254231923c5ccd917ac2`.
The author terminated successfully at 2026-10-04T13:33:23.914 UTC; the recorded
MCP client exited with code 2. Six growing-journal snapshots retain the exact
later post-writer-exit owner seal, without rewriting the scientific freeze.

## Fresh volumetric centres: reference coverage without successful repair

The fresh task-only author `H002_FRESH651_95` analysed the whole original
60 × 256 × 256-voxel acquisition without earlier pipelines, reference centres
or scoring feedback. Its first successful numerical prediction and final
attempt each returned 25 geometric centres. Fourteen candidates touch a volume
boundary; eleven do not. Coordinates are fractional, zero-based Z,Y,X voxels,
not verified physical distances. The final source SHA-256 is
`da8956561fc90078aed8695ecf0e457d4175358318bbba5ae5ab4d1946ac0483`.

Parent evaluation began after the original final answer and process exit.
All 2,528 canonical artifact hashes and four final-source hashes matched, and
exact owned viewer/native closure was independently confirmed. The original
client exit 2 remains separate from the completed scientific execution.
The unchanged point scorer and fifteen-centre manual reference match the
previously sealed digests. One-to-one matching uses the predeclared primary
distance of 30 unscaled voxels, not a fitted threshold.

| Reference comparison, whole volume | First | Final |
| --- | ---: | ---: |
| Predicted centres | 25 | 25 |
| Matched annotations | 15 | 15 |
| Unmatched predictions | 10 | 10 |
| Missed annotations | 0 | 0 |
| Reference precision | 60% | 60% |
| Reference recall | 100% | 100% |
| Reference F1 | 75% | 75% |
| Mean matched distance, voxels | 4.841 | 4.841 |
| Maximum matched distance, voxels | 10.534 | 10.534 |

At the predeclared 10-voxel sensitivity distance, each prediction matches
14 of 15 annotations, with 11 unmatched predictions and F1 70%; at 20 and
40 voxels each matches all 15. The manual reference has not been established
as exhaustive. Thus unmatched predictions are not automatically spurious
cells, and these metrics measure annotation agreement rather than a complete
biological census. Boundary status alone does not identify the extra objects.
No perfect-agreement or infallible-human-reference criterion is imposed.

The author's measured bright-core repair predicted two centres for a condensed
two-lobed structure, but every final row retained shape markers and all 25
centroid, volume and boundary values were unchanged. The author caught this
failed prediction during matched raw/result/combined XY, XZ and YZ review.
The repair did not improve the reference scores. Ordinary supported centres
remain useful, while the biological identity of the condensed masses is
unresolved. The displayed centre raster is not a native Points layer; point
feature selection was not demonstrated. These interaction and biological
limitations are distinct from the completed numerical result.

The [post-freeze evaluation receipt](task_only_analysis/h002-fresh95-postfreeze-evaluation.json)
retains exact scorer/reference/prediction hashes, unchanged API results and all
distance sensitivities. No scientific analysis was rerun, no answers were
supplied to an author and no corrected result was substituted for this freeze.

## Three-dimensional development: count reduction without split repair

A separate same-author development continuation, `H002_CAPACITY_DEV94`, tested
whole-volume nucleus-centre detection on one 60 x 256 x 256-voxel acquisition.
It is not a fresh task-only trial and contributes no autonomous success or
reference-agreement score to the comparisons above. The registered custom
callable smooths the volume, thresholds foreground, and uses distance-map
h-maxima as watershed markers. Each retained partition supplies one geometric
centroid; truncated partitions remain included and boundary-flagged. Physical
voxel spacing was not verified.

Increasing seed prominence from 2.5 to 4 and then 6 voxel-distance units reduced
the output from 29 to 28 and then 26 centres. Boundary-flagged centres fell from
15 to 14 and then 12. The suspect upper-body partitions retained identical
centroids and volumes across these trials; the reductions removed boundary
fragments rather than repairing their unresolved interior multiplicity.
Supported isolated nuclei and a separated neighbour pair remained useful local
detections, but neither a smaller count nor successful whole-volume execution
established one centre per biological nucleus.

The author rejected an unqualified biological count after matched XY,
orthogonal, image-only, point-only and combined review. Fractional centroids
appear on different neighbouring slices, so a single-plane screenshot cannot
establish either duplicate detection or an absent point. The callable retained
smoothed intensity, partitions and centres, but not the consumed distance map
or seed mask. Raw-intensity measurements therefore did not diagnose why its
interior shape maxima survived. The lesson is to inspect the failed marker and
body-association stage, not infer repair from aggregate count changes. No
corrected count, accuracy estimate or complete-volume biological acceptance is
claimed. The frozen pipeline SHA-256 is
`abd709c61c70f7bb36d79374a029c332488dac6a757346fc5ac69988c8612b7e`;
the registered source SHA-256 is
`24606ee04ae0dfc8b1fa95f7f212ec55ab349e17751f6cefd2e3eaab1c272095`.
Original source, execution records and matched captures remain in the named
development archive, separate from the two scored task-only trials.

The input is the nuclear volume derived from the Allen Institute for Cell
Science `cells3d` image through the pinned Haase notebook collection.
Scikit-image records the [Allen Institute's CC0 redistribution confirmation](https://github.com/scikit-image/scikit-image/issues/6181#issuecomment-1012370105).
The earlier curation warning about an unresolved licence is superseded by that
confirmation; it is not a restriction on presenting selected views.

## Operational attrition: an interrupted public translocation trial

The separate fresh-context trial `BBBC013_REPEAT94` inventoried all 96 paired
DNA/GFP source sets and compiled its final catalogue pipeline for the complete
plate. A four-well development run exported measurements for 941 nuclei and
showed the expected direction of nuclear translocation. These readouts were
not accepted as full-plate results or segmentation ground truth.

The full execution was terminated by its configured 4.5 GiB memory limit.
The retained systemd receipt records `Result=oom-kill` and identical
`MemoryPeak` and `MemoryMax` values of 4,831,838,208 bytes. This is evidence of
termination within that limited scope, not evidence that the host exhausted
all available RAM. Complete nuclear, cell-region and cytoplasmic mask sets
survived for 42 of 96 wells; the next well retained only a nuclear plane.
Plate-wide cell and well table export was not reached. Distributed matched
visual review remained incomplete, and a separately submitted statistics
extension had an unresolved registration receipt and did not execute.

This trial is therefore an operationally interrupted analysis, not a completed
assay result or a measured segmentation failure. Its partial masks and
four-well readouts cannot substitute for the missing plate-wide outputs,
replicate statistics or biological review. It is distinct from the earlier
prospective BBBC013 experiment reported in Supplementary Data 7. The original
pipeline, partial inventory, termination receipts and freeze remain unchanged;
the [compact outcome record](task_only_analysis/bbbc013-repeat94-outcome.json)
identifies their paths and verified hashes. No execution or uncertain
registration was replayed for this manuscript update.

## Retinal development: useful candidates with residual misses

The same-author continuation `R0010_REPAIR10_94` revisited one released retinal
field and its own predecessor outputs. It is not a fresh task-only trial or a
held-out evaluation. The source contains paired RBPMS, auxiliary fluorescence
and Hoechst planes at 2586 x 2586 pixels. The final detector uses RBPMS alone;
Hoechst intensity is measured in the same soma masks, not used to certify one
retinal ganglion cell per nucleus.

The completed final pipeline retained 100 soma-detector instances. The 102
exported ROI contours include polygon components and holes and therefore are
not a second cell count. Compared with the released predecessor, matched native
views show removal of broad background-associated regions and a more continuous
southeastern soma footprint. This comparison spans several method choices and
cannot attribute the difference to smoothing alone. A narrower trial changing
threshold smoothing from two to four pixels increased detector instances from
99 to 100 and mask support from 414,225 to 433,545 pixels. Those aggregate changes
motivated image review; they do not themselves establish a biological repair.

Matched raw-only, result-only and combined views retained supported bright
bodies and a separated neighbour pair. A diffuse dim southern body remained
unsegmented, another faint body had only partial support, and a dense central
cluster remained ambiguously partitioned. These limitations qualify the
candidate detections rather than erasing their useful local support. The result
is an inspectable detector output, not a validated biological RGC total or a
completeness estimate. Measurements use original RBPMS and Hoechst pixels with
the same label identities; a grouping correction restored both channel tables
without changing the masks. The final label bytes are identical to those of the
preceding smoothing candidate. Scientific processing completed, but final
packaging exceeded the run's declared time bound by approximately 72 seconds,
and the recorded client teardown exit code was 2; neither qualification is
silently converted to a clean end-to-end pass.

The [retinal outcome record](task_only_analysis/retinal-repair10-outcome.json)
identifies the frozen report, consumed pipeline and retained label bytes. No
new detector execution, reference scoring or pixel transformation was used to
prepare this account.

## Fresh retinal author: measured preprocessing and retained admission loss

The separate fresh-context trial `R0010_STAGED_96` used only the released
2586 x 2586-pixel field, its task brief, MCP and the frozen packaged skill.
It did not read the earlier retinal authors' outputs or receive reference
feedback. Acquisition inspection identified RBPMS, auxiliary fluorescence and
Hoechst; only RBPMS drove soma detection. Nuclear presence was not treated as
proof of an RBPMS-positive soma boundary.

The first two-class adaptive threshold produced 243 measured objects but failed
while settling viewer updates after writing the scientific steps. It remains a
failed execution, not a completed first prediction. A completed three-class
revision produced 105 objects but lost weak-body support and retained granular
nuisance. The author rejected it and measured an analytical response made by
subtracting a broad Gaussian background estimate from a mildly smoothed image.
The two Smooth object-size parameters were 12 and 240 pixels, not Gaussian
sigmas. A manual cutoff of 0.02 applies to the actual signed, normalized float
response; original size and shape-marker settings were retained.

At that cutoff, the independently sampled clear-positive and background
rectangles had 96.84% and 0.1344% support, respectively. The earlier two-class
background admission was 54.8%; a weak-body rectangle retained only 61.61%
support in the contrast response. These are rectangle-level diagnostics, not
complete soma masks, sensitivity or specificity estimates. The final compile
and all six processing steps completed. Primary IDs and geometry reconcile at
109 objects, including 8 border objects; 110 ROI contour members are not a
second object count.

Distributed matched review retained supported bright bodies, partial faint
footprints and unresolved northwest/northeast splits. In a plausible southwest
miss, the actual contrast maximum was 0.0195047, below the 0.02 cutoff, with
zero threshold support and labels throughout the diagnostic rectangle. This
localizes that loss before watershed without establishing the structure's
biological class or proving that a lower cutoff is a successful repair.
Some initially named regional captures repeated the southeast viewport after
rejected navigation commands. Their evidentiary use was withdrawn; corrected
captures and their actual camera coordinates remain separately recorded.

The author personally opened 62 captures and froze its qualified detector result
without claiming a validated RGC total. All 21 source and 119 payload manifest
entries were independently hash-verified. Exact owned viewer/native closure
was acknowledged, with both processes independently absent. Client exit 2
retains accumulated command errors separately from the successful final
scientific execution. The [fresh retinal outcome record](task_only_analysis/retinal-staged96-outcome.json)
binds original source, freeze, report and diagnostic identities. This trial is
distinct from the assisted retinal continuation in Supplementary Figure 11;
no new scientific execution, reference scoring or image transformation was
used to prepare this account. The earlier Figure 9 presentation used the
corrected whole-field and southwest raw/combined captures, not the earlier
misnamed overview captures. Those predecessor captures remain retained;
the current main figure shows the separate 102-instance repeat described below.
Its [native source proof](task_only_analysis/retinal-fresh-native-source-proof.json)
retains original PNG hashes, camera coordinates and exact geometric crops.
Whole-field crops are [566,41,415,415] and southwest crops [413,28,837,442]
in the original 1440 × 944 widgets; no intensity transformation is applied.

## Translocation development: admission repair does not validate compartments

The separate same-author recovery `BBBC013_DEV02_94` completed attempts 20 and
21 on three development wells. Lowering the nuclear threshold-correction factor
from 0.8 to 0.65 recovered a dim broad H12 profile while leaving the minimum
diameter, smoothing and maxima-suppression settings unchanged. Retained native
intermediate measurements identify threshold-shrunken support as the earlier
loss mechanism. The after-only crowded A01 control retained separate supported
regions at the inspected position, without establishing a field-wide regression
rate. Corrected D06 GFP views still showed unresolved propagated-compartment
extent and ownership (Supplementary Figure 12).

This local nuclear improvement does not establish whole-cell boundaries,
nuclear-to-cytoplasmic intensity-ratio accuracy or a treatment effect. The
full-plate continuation remained interrupted. These views are distinct from
the interrupted `BBBC013_REPEAT94` trial above and the prospective held-out
BBBC013 assay in Supplementary Data 7. The packaged
[source proof](task_only_analysis/bbbc013-development-source-proof.json) and
[render receipt](task_only_analysis/bbbc013-development-render-receipt.json)
retain all twelve supporting capture identities and the nine displayed original
PNG embeddings; no new scientific execution or scoring was performed.

## Fresh translocation first candidate: complete plate execution

The independent `BBBC013_FRESH13_88` author measured distributed development
images before choosing its first scientific settings, then froze the pipeline
before opening 90 reserve wells. It completed all 96 wells without changing
those scientific parameters. Technical ingestion and typed-table adaptations
are retained separately; this is not a claim of error-free tool use.

The coordinator inspected nine original development raw/result/combined PNGs,
finding supported ordinary nuclei, separated close pairs and dim-object
localisation, with unresolved complex clusters. The fixed ten-pixel expanded
regions are local photometry proxies rather than whole-cell boundaries.
Independent arithmetic from 96 saved well tables reproduced all 24 dose
summary rows and both assay-statistics rows. Four negative and four positive
control wells gave mean nuclear/cytoplasmic GFP ratios of 1.05 and 7.40 for
Wortmannin (Z′ 0.747), and 1.26 and 7.33 for LY294002 (Z′ 0.493).
These assay-quality findings do not establish unbiased whole-cell photometry
or exhaustive nuclear recall. The
[development and plate-arithmetic review](../../figure-collection-20261004/BBBC013-FRESH13-DEVELOPMENT-VISUAL-REVIEW.rst)
records capture/source identities, formulas and limitations. Final reserve
visual review and lifecycle closure were still in progress at this checkpoint;
complete autonomous scientific acceptance is not inferred from execution.

## Translocation recovery: complete coverage and explicit undefined measurements

A separate retained-context continuation, `BBBC013_DEV89`, completed all 96
source sets and retained 17,340 source-linked cell rows. This is same-author
development, not a fresh autonomous pass or a replacement for the failed
original phase. All 192 original DNA/GFP planes remained unchanged.

Before expanding, the author compared three wells using the same typed
measurement consumer. Lowering only the secondary-cell threshold-correction
factor from 0.8 to 0.4 admitted additional raw-GFP-supported cytoplasm while
preserving the nuclear instances. Zero-growth cases without supported recovery
remained undefined; no imputed denominator or synthetic cytoplasm ring was used.

| Development well | Unchanged nuclei | Zero-growth cases, before → after | Defined non-edge cohort, before → after |
|------------------|------------------|----------------------------------|----------------------------------------|
| A01 | 303 | 104 → 57 | 190 → 232 |
| C06 | 177 | 63 → 32 | 109 → 136 |
| E06 | 148 | 29 → 22 | 111 → 117 |

The full-plate result retained 14,049 numerically defined nuclear/cytoplasmic
GFP ratios: 13,359 were contained and non-edge, and 690 were edge-excluded.
Another 3,291 rows had zero-growth cytoplasm and remained undefined. All 96
per-well tables, the 96-row native Image table and 17,340 native nucleus rows
reconciled without missing or extra source sets. Numerical definition and
identity conservation do not establish biological compartment accuracy;
signal-dependent exclusion and uncertain boundaries may bias aggregate ratios.

The coordinator independently checked all 2,251 scientific artifact hashes and
six frozen source hashes. Original G01 raw/combined views broadly coincided,
while the isolated cytoplasm view retained thin or fragmented regions. That
isolated capture uses a different scale and compartment, not a matched
whole-cell three-view acceptance set. Polygon fill is not dense subtraction
proof. Geometric quantities remain in pixels without verified calibration.

The registered plate-statistics step failed because the supplied authoring
example dereferenced a nonexistent `StoredRuntimeValue.value` wrapper; the
downstream dose step was not executed. Native spreadsheet export completed,
but Z-prime, V-factor and dose-response outputs remain absent, not zero or
accepted. Issue #685 tracks the canonical example correction separately. No
failed or UNKNOWN scientific registration was replayed. The
[development coverage record](task_only_analysis/bbbc013-dev89-outcome.json)
binds the original report, coverage, diagnostic comparison, source and freeze.
The owned processes closed successfully; the original recorded client exit 2
is retained separately from completed computation and qualified data.

## Paired-channel authoring: local repair and qualified territories

A fresh-context author analysed the released paired DNA/actin field in
`H003_POSTPAUSE_88`, without reference-score feedback. Both source planes are
400 x 400 pixels with explicit shared sample identities. The first completed
paired prediction contained 54 nuclei and 54 associated actin territories.
Matched raw review identified a nuclear label spanning two broad interiors.
Subsequent marker and watershed trials improved this local separation, although
a faint neighbour elsewhere remained merged. The author ultimately registered
a custom detector through the ordinary OpenHCS function/artifact route, retaining
its consumed response, markers and support as diagnostics.

Figure 6 shows matched raw and first/final native overlays of
the repaired pair, alongside final raw, result-only and combined views of the
remaining faint merge. The first completed prediction follows a technical
submission repair; these panels compare scientific outputs within the same
uncoached run, not separate authors or a skill-only intervention.

DNA windows are 0–255 for the repaired-pair row and 0–151 for the retained
merge, gamma 1 and final ROI opacity 0.7. The final repaired-pair crop accounts
for an 11-screen-pixel canvas shift at unchanged camera and zoom. Aligned raw
RGB equality establishes presentation only, not segmentation accuracy. The
[source proof](task_only_analysis/h003-native-source-proof.json) and
[render receipt](task_only_analysis/h003-native-render-receipt.json) retain the
unchanged original screenshots and exact crops. Source:
[BBBC007v1](https://bbbc.broadinstitute.org/BBBC007), field A02, Drosophila
Kc167 DNA/actin; Sabatini laboratory, Whitehead Institute; Jones et al. (2005)
and Ljosa et al. (2012), [CC0](https://creativecommons.org/publicdomain/zero/1.0/).
Adaptations are OpenHCS overlays, native display windows and screenshot
clipping/scaling; no scientific pixels were retouched.

The final completed pipeline exported 55 nuclear instances and 55 associated
actin territories. Unique object IDs and parent relationships reconcile across
the tables. Median nuclear area was 370 pixels²; median territory area was
907 pixels². One territory had exactly the same area as its corresponding
nucleus, while 12 nuclear and 17 territory bounding boxes met the image edge.
The retained negative patch contained no labelled pixels in either output.
These are local and table-level checks, not exhaustive accuracy or pixelwise
containment tests. Several actin interfaces remained poorly resolved in the raw
image, so the territories support exploratory occupancy and source-linked
measurements rather than validated physical cell boundaries.

The final review retained 54 matched native captures spanning whole-field and
object-scale positions, both channels and two display windows. Supported local
detections and the repaired pair remain useful; the faint merge, clipped objects
and no-growth territory qualify their interpretation. No exact biological census
or reference accuracy score was reported. All 148 declared frozen artifact hashes
were independently verified, and the owned viewer/native processes were closed.
The recorded client teardown exit code was 2 and remains distinct from scientific
execution completion and successful process closure. The
[paired-channel outcome record](task_only_analysis/h003-postpause-outcome.json)
binds the original freeze, consumed pipeline, registered detector and final
evidence. No detector execution or scoring was repeated for this account.

## Full-field paired-channel repeat: diagnosis without successful repair

A separate fresh author, `BBBC007_FRESH651_88`, completed all 16 paired
DNA/actin fields without reference outlines, earlier scientific solutions or
reference-score feedback. Its first completed scientific candidate contained
1,417 nuclear objects. The final candidate retained 1,335 nuclear identities
and the same number of seed-associated cell labels, with no absent secondary
IDs, extra secondary IDs or lost nuclear seed pixels. These checks establish
identity conservation, not biological recall or physical cell boundaries.

The author identified a dense bright nuclear cluster in A02 site 1 without
outlines and rejected full-field population use. A last change from shape to
intensity markers, with suppression increased from 6 to 8 pixels, reduced
this field's detected count from 46 to 38 without recovering the missing
cluster. Dense actin interfaces, clipping and fragmented compartments also
qualified cell-boundary interpretation. Useful isolated-object diagnostic
findings were retained; they do not establish full-field coverage.

The coordinator independently verified every original manifest entry in its
`attempt_sources` and `payloads` arrays and opened the unchanged corrected
A02 raw and final DNA overlay captures. The final overlay visibly retains
the missing dense cluster. An earlier black raw capture was rejected, and
the corrected raw and final captures have different screen footprints; they
support a field-level finding, not a pixel-matched intensity comparison.
The [independent review](../../docs/validation/bbbc007-fresh651-independent-review-20261004.rst)
records the exact paths, final capture identity and verification scope.
No reference outlines were scored for this repeat.

The final-image finding did not establish the earliest failed stage. Absent
foreground, missing markers and removal of merged components by filtering
remain distinct hypotheses requiring retained intermediate evidence. The
canonical skill already describes that diagnostic sequence. This trial
therefore demonstrates autonomous failure detection but not successful
repair or a validated reusable parameter recipe. Its recorded client exit
exceeded the 75-minute deadline by about eight seconds; that operational
qualification remains separate from scientific completion and rejection.

## Later full-field paired-channel repeat: diagnosed support failure and partial recovery

The independent author `BBBC007_FRESH08_96` processed all 16 released DNA/actin
pairs without reference outlines, earlier analysis solutions or score feedback.
Its first complete candidate missed distinct bright nuclear bodies in the
crowded A02 field. Retained support, marker and unedited-object diagnostics
localized the failure to broad admitted haze, sparse shape markers and merged
basins removed by size filtering. A local minimum-cross-entropy threshold
changed partitions but did not recover the anchors; the author rejected that
repair despite the A02 count increasing from 22 to 50.

Changing the primary method to local Otsu at the same neighbourhood scale
recovered several nuclear anchors and retained the inspected faint-positive
and textured-body controls. Several clear bright bodies remained without their
own nuclear label in the crowded witness. These local gains do not establish
whole-field coverage or a general preference for Otsu. The final pipeline
completed all 16 fields, exporting 1,363 nuclear and 1,363 cell rows; 81 secondary
areas equalled their primary areas. Original CSV review confirmed these counts,
unique source/object keys and matching identity sets. They do not establish
pixelwise containment or biological cell boundaries.

The coordinator independently verified 815 frozen artifact entries
(797,409,650 bytes), five recorded journal prefixes and the final pipeline
digest. It opened original crowded predecessor/repair views and matched faint
and textured raw/combined crops. The native and viewer closure acknowledgements
were checked against process absence; recorded client exit 2 remains distinct
from scientific completion. The [outcome record](task_only_analysis/bbbc007-fresh08-outcome.json)
binds this evidence to the original run. No manual-reference score or unseen
validation claim is made. Supported local detections and partial self-directed
recovery are retained separately from the unresolved crowded-region coverage,
seed-sized cells and body-boundary interpretation.

## Fresh paired-field repeat: local separation gains and a caught regression

The fresh author `H003_FRESH656_96` analysed only the released paired 400 x 400
DNA/actin field, without reference outlines, previous scientific solutions or
reference-score feedback. It retrieved the official ExampleHuman recipe and
marker/body guidance before choosing its first method, and measured distributed
signal, background, internal peaks and genuine-neighbour separation. This is
fresh independent development on released data, not held-out evaluation.

The first pipeline used shape markers and shape partitioning and exported
53 nuclei and 53 seeded cell regions. Changing to intensity markers with
smoothing 8 retained shape partitioning and reduced those counts to 51/51
without resolving the cluster. Changing partitioning to intensity separated
the crowded cluster and genuine pair, yielding 54/54. The final attempt,
REPAIR03, changed marker smoothing from 8 to 4 after the author measured an
absent dim maximum in the actually consumed smoothed response; changing peak
suppression alone could not restore that absent maximum.

The final pipeline completed and exported 56 nuclear instances and 56 seeded
cell regions. Distributed final review still found a dim/bright merge and an
apparent new split inside an isolated mottled nucleus. The author rejected
unqualified counting, preserving the last attempted source and its regression.
Crowded-cluster separation, the genuine-pair control and clear sampled negative
areas remain useful scoped findings. Uncertain actin interfaces and seed-sized
territories do not establish physical cell boundaries. Counts are detector
outputs, not biological truth or a reference agreement score.

The coordinator independently verified all 244 canonical payload hashes and
the final source after cleanup, and personally opened the original isolated-body
raw, result-only and combined native captures. The raw body has no convincing
separating outer boundary at the overlaid seam, supporting the apparent-split
concern rather than an annotated error rate. Low-valued grayscale label IDs
are dark; this is not evidence of missing instances. The combined capture has
a shorter canvas than the raw/result captures, so the review compares the
native region, not exact screen pixels. No reference outlines were opened or
scored. The [outcome record](task_only_analysis/h003-fresh96-outcome.json)
retains source, report, freeze and original capture identities.

The final scientific freeze includes 90 native PNGs: distributed raw/result/
combined views in both channels and additional isolated-split diagnostics.
Physical calibration is unverified; geometric outputs use pixels and pixel².
Typed closure confirms exit of the owned native/viewer processes. The original
recorded client exited with code 2 within the 75-minute envelope; that technical
qualification is retained separately from complete execution and scientific
rejection. This trial improves diagnosis coverage but does not establish better
task-wide accuracy, a causal skill benefit or a reusable parameter recipe.

## Fresh public neurite field: measured faint-process recovery

The independent author `H004_FRESH08_95` processed the complete paired
800 x 800-pixel field through the packaged skill and MCP. Morphology supported
one process/body channel and one nuclear-like channel; stain identity and
physical calibration were not established. The final pipeline retained eight
nuclear objects and eight associated perinuclear candidates. Their total areas
were 5,394 and 9,505 pixel² respectively. The latter are bounded operational
regions, not validated complete anatomical soma boundaries.

The first completed modular candidate missed a faint diagonal. The author
measured its enhanced-response peak at 0.006434, compared with sampled negative
maxima of 0.001519 and 0.002260. The original effective admission was 0.023596.
Its revised admission of approximately 0.002949 recovered supported samples
along the ridge; both sampled 2,601-pixel negative regions admitted zero pixels.
These local controls support this repair, not field-wide specificity or a
universal threshold. Independent review of original matched raw/result/combined
captures confirms local faint-path recovery and bright-trunk support, with
remaining fragments and weak-path gaps.

The author also rejected a multi-image photometry table after raw-pixel checks
showed both named images receiving the same source values. Reordering image
settings did not repair it. Separate source-bound single-image steps restored
the distinct raw-channel values. Original failed tables and sources remain
preserved; issue #722 tracks the underlying implementation defect. Descriptive
photometry is on the original uint8/255 planes; saturation limits interpretation.

The final candidate contained 33,201 foreground pixels, 27,856 outside the
operational perinuclear regions, and 6,678 skeleton pixels. These are method
descriptors, not diagonal-corrected length or complete per-neuron outgrowth.
Distributed review retained useful nuclear detections and recovered processes,
but weak fragments, crossings and field truncation left anatomical topology
unresolved. No manual tracing, reference-answer scoring or accuracy percentage
was available for this fresh development repeat.

The final source SHA256 is
`635703013f51d1d2a5d4de204f854ce2d0fe4ef2a071dea6955103b9c6484733`,
executed as `0f0ec761-7d11-4220-bdb3-ffd166f36f2b`. The final report retains
57 native screenshots. Independent verification matched 3,471 complete files
(105,146,494 bytes); one still-growing outer author transcript matched its
recorded 3,374,616-byte prefix rather than a final whole-file hash. Exact native
and viewer closure was acknowledged and their old PIDs were independently
absent. The recorded client exited with code 2, preserving earlier command
errors, after 4,025 seconds. This operational qualification is separate from
successful final execution and the scoped scientific findings.

Original source, report, freeze, capture receipts and scientific files remain
under `next-public03988-h00495-after08-20261004/H004_FRESH08_95` in the retained
programme archive. This result does not replace the earlier neurite repeat or
constitute evidence of a causal skill effect across fresh authors.

## Independent retinal repeat: useful repair with faint loss

An independent retinal author retained 73 method-defined soma candidates after
repairing a bright-body split and preserving neighbouring-body controls. A weak
southwest feature remained unlabelled, with uncertain complex extents elsewhere.
The [independent native review](../../figure-collection-20261004/RETINA-FRESH11-INDEPENDENT-REVIEW.rst)
records full checks of 1,147 payload entries, ten handoff entries and 83 opened
captures, direct agreement of 73 labels/table rows and 439,694 foreground pixels,
and the same-coordinate positive/faint comparisons. These sets overlap.
Different size, border and preprocessing choices prevent interpreting its count
against the earlier 102-instance candidate as an accuracy comparison. Useful
local findings are retained separately from the unresolved population-level
claim; no manual-reference score was obtained.

## Fresh public neurite field: bright-junction support repair

Supplementary Figure 19 shows an independent author recovering a bright
junction after enhanced support omitted raw-supported pixels. The final
candidate retains weak-path gaps and uncertain crossings. The
[independent native review](../../figure-collection-20261004/H004-FRESH10-NATIVE-REVIEW.rst)
identifies the original captures, journal-prefix qualification and a direct
read of materialized TIFFs confirming the local 19-to-zero missing-pixel
change. Original [earlier](task_only_analysis/h004-fresh10/BIO04.py) and
[final](task_only_analysis/h004-fresh10/BIO06.py) pipelines, native state/capture
receipts and [final descriptive metrics](task_only_analysis/h004-fresh10/final-metrics.json)
are retained without reconstructing outputs. No reference score or accepted
per-neuron outgrowth total is established by this trial.

## Personal neurite fresh13: nine fields with recovered thin-path support

An independent author completed all nine two-channel fields of the personal
neurite acquisition and retained labels, spatial graphs, tables and diagnostic
checkpoints. It identified an early admission loss and reduced the enhanced
threshold correction factor from 0.85 to 0.10. Sampled thin tracks reappeared
while a sampled quiet rectangle remained empty. Site5 retained 244 modeled
body labels; modeled outgrowth increased from 1,238.5 to 18,946.2 micrometres.
These are algorithmic outputs, not independently verified cell counts or
complete neurite lengths.

Independent inspection of the final site1/site9 raw-only, result-only and
combined captures confirmed substantial raw-supported path geometry across
sparse and dense foreground. Fine branches remained missing, with ambiguous
partitions in broad bodies and unresolved crossing ownership. All 298 manifest
entries and the final pipeline hash passed independent verification. The
[nine-field review](../../figure-collection-20261004/P001-FRESH13-NINE-FIELD-REVIEW.rst)
identifies the original evidence and scopes those conclusions. Three fields
received the author's final visual review; six additional fields have saved
outputs but no demonstrated pixel-level review. Overlapping fields were not
stitched or deduplicated, so their counts cannot be pooled as unique neurons.
This fresh-context development repeat used no reference feedback and does
not establish unseen-data accuracy. The completed run is preserved while its
display is reused and stitching continues separately.

## Personal neurite mosaic: technical recovery and retained biological losses

The retained same-author continuation `P001_STITCH_DEV94` used a previously
assembled 2857 x 2858-pixel, two-channel mosaic from nine overlapping fields.
All nine fields were development data; there was no remaining unseen reserve.
Shared placements and blending were reused, not recomputed independently by
channel. Inherited 1st/99th-percentile fits pooled all nine contributing images
per channel: DAPI 616–3839 DN and FITC 143–20445 DN. The continuation applied
those fixed limits without per-field or mosaic refitting. Clipping after
blending does not reproduce clipping before blending exactly.

The first candidate's rescaler unexpectedly mapped the selected interval to
uint16 0–65535. Native raw/processed profiles exposed the mismatch. The second
candidate replaced only that operation with a registered fixed-DN clip; its
checked profile preserved in-range values. Compilation and execution completed,
and the native viewer supplied distributed raw/result/combined comparisons.
The corrected analytical mapping did not resolve the biological failures.

The final output contained 1,429 admitted body IDs and 1,570 nuclear labels.
Native tables reported 150,442.4259 micrometres of algorithm-defined outgrowth,
with 228 zero-growth bodies and 1,201 nonzero graph owners. These are descriptive
outputs, not accepted neuronal totals or complete morphology. The declared
spacing was 1.3556 micrometres per XY pixel and was not independently calibrated.
SWC-coordinate remeasurement exceeded the native path-feature sum by about
0.8326%; the exported geometric and path-feature definitions are retained
separately rather than presented as identical measurements.

The author retained useful local paths, linked graph-feature selection and
sampled seam/junction continuity. Dense-region DAPI review nevertheless showed
clear anchors without admitted ROIs and a close pair sharing one label; several
body masks underfilled connected FITC signal, with uncertain crossing ownership.
The coordinator independently opened the frozen dense-region DAPI triplet and
confirmed the missing anchors. These material counting failures, not a demand
for perfect agreement on ambiguous cells, motivated rejection for complete
counting and morphology. The original freeze remains immutable while further
development is separately assigned.

All 1,033 canonical payload entries and the final pipeline hash passed independent
verification. The run sealed within its 75-minute clock, including cleanup;
owned native/viewer processes were closed, while client exit code 2 remains
recorded. The [stitched-development outcome record](task_only_analysis/p001-stitched94-outcome.json)
binds the original report, manifest and pipeline identities. No new scientific
execution or reference scoring was performed for this account.

## Independent retinal repeat: local gains with unresolved field-wide counting

The fresh-context trial `R0010_FRESH656_95` analysed the same released R0010
acquisition using only its brief, MCP and packaged skill, without earlier
scientific outputs or reference feedback. The final attempted pipeline completed
and exported 118 algorithmic parents; 119 ROI contours are not a second count.
The author preserved its first method, seven attempted methods including one
technical dimensionality failure, processing checkpoints and distributed native
raw/result/combined captures. This was a development repeat, not an unseen
held-out evaluation or controlled comparison of skill versions.

Useful local results were retained rather than discarded with the whole-field
count claim. A conspicuous bright pair remained separated. Increasing intensity
marker smoothing from 30 to 60 native pixels repaired a moderate-body split;
the coordinator independently inspected the final southeast raw/result/combined
set and confirmed one filled footprint in place of the preceding partition.
Other regions still contained splits, diffuse admissions and weak unlabelled
structures. These remaining errors limit cell counting and precise morphology,
but do not erase the local recovery or the inspectable detector outputs.

Admission thresholds 0.05 and 0.04 produced 84 and 124 parents respectively.
That sensitivity is not an accuracy estimate, a biological confidence interval
or proof that either count is wrong. The author selected a final118-parent
candidate after separate marker changes; no manual-reference comparison or
quantitative field-wide error rate was obtained. Acquisition XY spacing was
declared 0.12353054911059548 micrometres/pixel, without independent calibration.
The denominator was one 2586 × 2586 source field with size and border exclusions,
not the entire retina. Hoechst was inspected but all nuclei were not assumed
to be eligible RBPMS-positive cells.

Independent verification covered 215 manifest-declared size/hash entries,
1,465,782,627 bytes, including three exact journal prefixes, and all82 indexed
native PNGs (46,730,113 bytes), with no mismatches. Exact owned native/viewer
closure was acknowledged and independently confirmed; the original client
exit2 remains recorded. Outer author journals require sealing after their writer
exits and are not certified by this prefix check. The
[retinal repeat outcome record](task_only_analysis/retinal-fresh656-outcome.json)
identifies the preserved report, manifest, pipeline and inspected captures.
No analysis, private scoring or source-image transformation was rerun for this
account. The separate 109-instance predecessor retains its original captures
and source proof. Main Figure 7 shows the later 102-instance repeat, not this
118-instance repeat.

## BBBC039 fresh08: batch coverage completed in a separate continuation

The independent author `BBBC039_FRESH08_88` froze a pipeline before its
reserved-field review and retained complete label/table outputs for 182 of
200 public fields. Its original partial disposition and interrupted execution
remain unchanged. `BBBC039_COMPLETION18_REV02_88` subsequently completed the
missing 18 fields as a retained-context development continuation, not a fresh
blind author. Its scientific parameter file is byte-identical to the original;
selected wells and distinct output declarations separate the new outputs.

The original recorded MCP terminal status reports completion with no errors.
Independent reconciliation found exactly one lossless labels TIFF, one primary
detector table and one object-measurements table for each expected source
identity. The 18 additional fields contain 2,136 object rows; every primary
detector count matches its field's row count and every object label is unique
within that field. The continuation's frozen pipeline and parameter hashes
also passed independent checks. The combined coverage is therefore 200 fields
across two recorded execution phases, rather than one retrospectively
successful uninterrupted run.

This coverage result is not an accuracy estimate. Regional native review of
the fresh author's frozen output showed useful localisation alongside lobed
merges and a partition through one continuous body. No reference masks or
scorer were opened for this account, and the continuation's label pixels were
not independently scored. Counts remain algorithmic outputs. The useful
completed batch and regional failure evidence are retained for subsequent
learning rather than discarded for failing to achieve perfect segmentation.
The [completion record](task_only_analysis/bbbc039-fresh08-completion18.rst)
identifies the source phases, original terminal receipt and independent checks.
These outputs do not replace Figure 5's separately scored trial.

## Retinal fresh09: local repair with a retained neighbour control

The independent author `R0010_FRESH09_96` analysed the released R0010 field
without earlier retinal outputs, reference masks or supplied parameter
corrections. Candidate08 repaired a southeast continuous-body partition but
merged a genuine northwest pair; candidate09 retained that regression.
The author independently identified it and changed marker suppression in
candidate10. Parent review of matched raw/result/outline triples confirmed
separate northwest neighbours and a continuous southeast envelope together
in the final candidate. Southwest views retained plausible isolated-body
detections, while diffuse northeast support left some boundaries and identities
uncertain. These are regional visual judgements, not a field-wide error rate.

Independent table reconciliation found 102 object rows with unique labels
1–102 and an image-level detector count of102. The frozen pipeline SHA256 is
`59f48a9ff4ee70f988f2ff0fed1eadf7df97a8de3bad8d9753e6432635b0e0a0`.
The retained source manifest binds these tables to R0010.czi/site1/Z1/time1,
RBPMS AF647 channel1; the CSVs themselves lack acquisition/source columns.
Exact owned native and viewer exits were acknowledged and independently
confirmed by absent process IDs. The original client exit2 and missed final
sealing deadline remain recorded separately from completed numerical outputs
and visual acceptance. No manual retinal count or mask score was obtained.

The [independent final review](../../figure-collection-20261004/R0010-C10-INDEPENDENT-LOCAL-REPAIR-REVIEW.rst)
and [intermediate tradeoff](../../figure-collection-20261004/R0010-C08-REGIONAL-TRADEOFF-REVIEW.rst)
retain original capture identities, table checks and lifecycle qualifications.
Main Figure 7 now shows this final candidate's whole field, northwest pair
and southeast continuous envelope. Its [native source proof](task_only_analysis/retinal-fresh09-native-source-proof.json)
binds six unchanged original PNGs, the frozen pipeline, native camera settings
and exact geometric crops. Raw views use window 0–63 and gamma 1. The outline
background uses the pipeline's source-intensity stretch followed by the manual
display range 0–63/255, so it is brighter than the native raw presentation;
same-coordinate matching does not imply identical photometry. Neither display
changes the frozen labels or supplies a reference score. The preceding
109-instance trial retains its separate source proof and original captures.

## Scope and retained evidence

### Retinal fresh13: supported localisation with weaker faint boundaries

The independent `R0010_FRESH13_89` author retained 129 AF647 soma detections
after its own foreground-admission repairs. The initial 235 detections included
excess background; a stricter 91-detection attempt lost a faint regression
control, and the intermediate final settings recovered some of that support.
These counts describe parameter sensitivity, not a biological confidence interval.

Independent native review supports useful bright-body localisation and clear-pair
separation. Faint crescents, outline contamination and broad-cluster multiplicity
remain less reliable; no manual total or reference accuracy score was obtained.
The labels, table and ROI archive agree on 129 members, but that consistency
does not establish that each member is one biological cell. The [independent
final review](../../figure-collection-20261004/R0010-FRESH13-INDEPENDENT-FINAL-REVIEW.rst)
records the complete pipeline identity, unchanged 106-file payload freeze and
parent review of four matched three-view sets. All eight declared final sets
have matching camera, axes, raw transform and window 0–47/gamma 1. Scientific
artifact freezing is separate from the harness's final runtime/journal closure.

### H003 fresh09: nuclear instances and associated-region geometry

The independent author `H003_FRESH09_95` analysed the released paired
400 x 400-pixel DNA/actin field through MCP using the packaged skill, without
reference labels, a target count or parameter coaching. Before its first
scientific candidate it retrieved the ExampleHuman contract and conditional
marker/admission guidance, and measured internal texture, a genuine pair and
actin positive/background support. This preparation is documented behaviour,
not a controlled estimate of the skill's causal effect.

The final pipeline exported 55 nuclear rows and 55 associated-region rows.
Independent readback confirmed both row counts and the frozen complete source
SHA256 `3c2766253361ce1f469ea6fb7c34aca36c260890ee345480e442742e5efe21be`.
Its own repairs increased propagation regularization, rejected a gradient
watershed trial that produced winding contact strips, and raised the actin
foreground threshold while retaining four visibly faint bodies. Assigned
actin support decreased from 55,903 to 52,787 pixels without changing counts.
This was within-run autonomous repair, not an externally corrected pass.

Matched native review retained useful nuclear localisation and body coverage,
but an unsupported associated region equalled its nuclear seed, another weak
body had unresolved extent, and lobed/contacting identities remained uncertain.
Counts are algorithmic, not a manual cell census. Pixel-native geometry does
not establish physical calibration. The qualified nuclear estimate is retained
separately from exploratory actin regions; these local limitations are not
reported as failure of all localisation. No held-out scoring or accuracy
percentage was obtained.

The original report, final manifest and source remain under
`/home/ts/wt/openhcs-issue-batch-20260929/next-h003-fresh09-95-after720-20261005/H003_FRESH09_95/author-workspace/output`.
Label planes, tables and original matched QA captures remain on HDD under
`/run/media/ts/hdd/openhcs-science/next-h003-fresh09-95-after720-20261005/H003_FRESH09_95`.
These paths identify retained evidence rather than a portable archive. At the
independent checkpoint runtime cleanup was pending; biological output completion
does not imply sealed outer journals or verified runtime retirement.

### BBBC039 fresh10: complete independent repeat

The independent `BBBC039_FRESH10_COVERAGE_96` author completed all 200 fields
with 21,371 predicted instances. Parent-only postfreeze scoring matched
20,207 of 23,615 reference objects: precision 0.9455, recall 0.8557 and pooled
F1 0.8984. The earlier complete author scored 0.9062 on exactly the same field
keys, reference hashes and IoU0.5 matching implementation. The repeat incurred
314 additional misses and eleven additional excess predictions. Across fields,
61 F1 scores improved, 123 decreased and sixteen were unchanged; 133 reached
at least 0.90 and eleven remained below 0.80.

The author retained its original primary scientific method after rejecting
three development repairs. Its complete-corpus result is not a best-of score
from those repairs or a first-200 comparison. The repeat shows substantial
agreement with a remaining difficult-field tail, rather than a causal skill
improvement. Supplementary Figure 20 displays all paired field scores and the
pooled detection tradeoff. The [evaluation receipt](../../figure-collection-20261004/bbbc039-fresh10coverage-postfreeze-evaluation.json)
and [original scoring account](../../figure-collection-20261004/BBBC039-FRESH10-FULL200-SCORE.rst)
retain unchanged frozen payloads, references, original failures and lifecycle
dispositions. No reference-score feedback was given to the author.

### H003 fresh10: nuclear recovery and selective body admission

A separate task-only author corrected internal-texture splits, then detected
and repaired a bright/dim neighbour merge. Subsequent shape-marker revisions
recovered dense-region nuclei lost when oversized merged basins were filtered.
The final output contains 55 nuclear instances and 53 admitted actin-associated
regions; two weak associated regions remain separately reported rather than
silently removed from the nuclear result. Integer-mask readback distinguishes
the final pair even where adjacent label colours look similar.

The [independent native review](../../figure-collection-20261004/H003-FRESH10-INDEPENDENT-RECOVERY-REVIEW.rst)
and [source proof](task_only_analysis/h003-fresh10-source-proof.json) retain
original matched raw/result/outline witnesses, frozen source identity and
claim-specific qualifications. Useful nuclear localisation and local recovery
are supported; crowded actin boundaries and an elongated nuclear identity remain
uncertain. No manual-reference accuracy or exhaustive biological count is claimed.
These are the author's own revisions, not externally corrected analysis.

### H002 fresh10: ordinary-body repair and unresolved cluster identity

The independent task-only author `H002_FRESH10_89` analysed the complete
released 60 × 256 × 256 single-channel volume without reference answers,
target count or parameter coaching. It measured raw body extent, internal
peak spacing, a genuine neighbour pair and background before its first
candidate. The official 3D example supplied workflow structure, not assay
settings or a physical calibration.

The first completed numerical output contained 28 provisional centres.
Increasing marker prominence left its centre CSV unchanged. Compatible
maxima-component connectivity reduced the count to 26 and repaired a
lower-border split, but another continuous body retained a duplicate.
Measured component-local, axis-aware spacing then produced 22 centres,
with the same 718,474-voxel foreground support. Native review supported
one centre in the repaired round body and retained two in a genuine pair;
one bright multi-lobed cluster remained unresolved. Count reduction alone
does not prove biological improvement or complete detection.

Independent readback found 22 rows in the final centre CSV. The author also
reconciled 22 persisted ROI geometries, native feature rows and image count.
These delivery checks are separate from biological validity. Supplementary
Figure 17 shows final-only native XY, XZ and YZ witnesses; it does not show
the earlier candidates or independently establish their repair chronology.
The [native source proof](task_only_analysis/h002-fresh10-native-source-proof.json)
binds six byte-identical screenshots, matched camera/axes/windows, the frozen
pipeline and registered callable, and the source report and table hashes.
No analysis or reference scoring was rerun for this account.

The author withheld acceptance of a global biological nucleus count while
retaining useful ordinary-body repairs. Identity of the bright cluster,
possible dim misses, close-neighbour sensitivity and border-truncated
geometry remain uncertain. Coordinates are voxel indices, not verified
micrometres. This independent run is distinct from the earlier 26-centre
repeat and from the same-context development trial. Its original report,
pipeline, callable, QA audit and reconciliation remain under
`/home/ts/wt/openhcs-issue-batch-20260929/next-h002-fresh10-89-20261005/H002_FRESH10_89/author-workspace/output`;
canonical payloads remain on HDD at the paths in the source proof.

### H002 rotation repeat: useful localisation with an incomplete census

The separate `H002_FRESH10_ROTATION_96` author retained 25 volumetric
candidates, fourteen boundary-flagged, under its initial scientific settings.
The [independent frozen-run review](../../figure-collection-20261004/H002-ROTATION-FROZEN-REVIEW.rst)
verifies all 395 payload and 23 control-file hashes, reconciles the saved
tables, and inspects ordinary-body and clipped-boundary native triads.
Ordinary localisation remains useful; ambiguous bright masses and incomplete
boundary geometry prevent interpreting the candidates as a complete cell
census. No reference score or biological parameter improvement is claimed.

### BBBC007 fresh10 rotation: coverage failure with consistent exports

The [independent frozen-run review](../../figure-collection-20261004/BBBC007-FRESH10-ROTATION-INDEPENDENT-REVIEW.rst)
retains complete 16-field execution and 1311 site-local nucleus/cell pairs,
alongside observed missed groups and incomplete final-candidate QA. Direct
saved-mask checks confirmed matching IDs and containment, not biological
accuracy. The original timed trial stays frozen; separately assigned development
continuation does not convert its rejected outcome into an autonomous pass.

### Programme-wide evidence scope

[Figure 5 plot data](../figures/slas/task_only_analysis_plot_data.csv) retains
the plotted first/final observations and all 200 field scores. Its
[figure receipt](../figures/slas/task_only_analysis_provenance.json) records
source, generator and output hashes. The
[generator](../figures/build_slas_task_only.py) reads these evaluation receipts
without opening their prediction or reference paths and does not run a scorer.

These two completed cases show useful autonomous method choices and within-run
repair. They are not an exhaustive inventory of programme attempts, a
human-equivalence comparison or a controlled estimate of the skill's effect.
Unfinished or interrupted trials are not counted as successful results, and
same-author development continuations are not counted as fresh independent
authors. Qualitative gains in neurite tracing, cell boundaries or volumetric
segmentation require their own references and cannot inherit the object F1
reported here.

Only small evaluation receipts and selected figure assets belong to this paper
package. Raw images, prediction arrays, original tool journals and native QA
remain in their original frozen study bundles. The receipts identify those
local paths and hashes; they are provenance records, not a portable copy of
the entire scientific archive. No scientific pipeline or scorer was rerun to
prepare this manuscript section.
