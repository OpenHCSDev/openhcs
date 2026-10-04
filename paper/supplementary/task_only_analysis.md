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

## Scope and retained evidence

[Figure 7 plot data](../figures/slas/task_only_analysis_plot_data.csv) retains
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
