Fresh volume repeat: frozen development and annotation localisation
==================================================================

H002_FRESH22_89 used the task brief, receiving22 packaged skill and MCP on
isolated display89. Its first method produced 30 centres and split a continuous
elongated body. Component-local seed suppression repaired that sampled split
while retaining separate neighbouring bodies. The final method retains 26
fractional Z/Y/X centres, including 16 border-touching basins. These are
algorithmic candidates, not a validated count of nuclei.

The author froze its scientific method before evaluation, completed its final
message and exited its author scope before the coordinator opened the manual
reference. No reference feedback went to this or another blind author. No
scientific arrays or pipeline were rerun. Coordinates were not rounded,
rescaled, offset or filtered. All 26 predictions are evaluated.

.. csv-table:: Existing one-to-one Euclidean matcher, unscaled voxel indices
   :header: "Distance", "Matched of 15", "Unmatched predictions", "Mean error", "Maximum error", "Ambiguous reference points"

   10,14,12,4.4113766635,7.1956380615,0
   20,15,11,4.8205338250,10.5487340860,0
   30,15,11,4.8205338250,10.5487340860,1
   40,15,11,4.8205338250,10.5487340860,2

Thirty voxels is the retained primary threshold; 10, 20 and 40 are the
existing sensitivity thresholds, not newly selected for this result. At 30,
reference-relative precision is 15/26 and recall is 15/15, giving F1
0.7317073171. Reference coverage has not been established as exhaustive:
the evaluator's false-positive field means unmatched predictions, not
demonstrated false biological detections. One-to-one matching remains enforced
when a reference has multiple nearby candidates. No physical-distance or
segmentation-boundary score follows from these point comparisons.

The preceding fresh15 trial also matched 15/15 at 20 and 30 and 14/15 at 10,
with mean error 4.795057 at 30. This repeat supports annotation-localisation
consistency, not a new accuracy gain. Independent native review found useful
ordinary-body centre placement and a repaired continuous-body split, while
an irregular bright cluster and cropped supports remained ambiguous.

Independent freeze and native review
------------------------------------

Control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-h002-fresh22-89-after918-20261006/H002_FRESH22_89/author-workspace/output.
Payload root:
/run/media/ts/hdd/openhcs-science/next-h002-fresh22-89-after918-20261006/H002_FRESH22_89.
FINAL-REPORT.rst, final-manifest.json, original proposals and all technical
failure receipts remain unchanged. Independent checks verified all 96 listed
payload/control files, 57860568 bytes, zero missing or mismatched entries.
Manifest SHA256:
6db16045c88a831983fbe3c71091e2e880e1a09cbb8aa8b555ae59bea0180877.
Pipeline SHA256:
1ce28f71ec91844725c0bb69e5809c182d0a3e581d39cdc3dfc5191f021de74a.
Integer labels SHA256:
7e87eb19db78de259fe7476a3eedfee508de1dbb44ef92fdd7603aa8ff2e628a.

All 85 capture files independently match indexed sizes and hashes. The
coordinator personally opened first XY and final XZ/YZ matched triplets, not
all 85 captures. Final XZ at Y157.5 and YZ at X42.5 preserve identical native
dimension ordering, coordinates and canvas within their raw/point/combined
sets. Slice-hidden points cannot establish missing detections. The original
QA index retains anomalous selection highlights and corrected captures rather
than replacing failed witnesses.

Two earlier executions failed during viewer settlement after saving scientific
results. The final technical delivery retry disabled execution-time streaming;
persisted final points were reopened through the ordinary MCP viewer route.
The final execution da6b8a16-a37d-4f62-951c-30791afcc02a completed.
Owned viewer/native exits were independently checked; original client exit2
is preserved. Live outer-journal prefixes are not represented as complete
post-writer seals. No UNKNOWN scientific mutation was replayed.

Reproduce the table-only comparison
-----------------------------------

Use the existing interpreter:
/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/bin/python.
Import read_csv_points and score_points from the original
/home/ts/code/projects/openhcs/benchmark/score_point_centres.py, read fully
before invocation. Its SHA256 is
a80eecefc791dd755444892cde5816df8c6a6bad15b9dd350fadfd23d6156af8.
Read the reference columns axis-0/axis-1/axis-2 from
/home/ts/.local/share/openhcs-blind-evaluation/haase_cells3d_20260927/cells3d_annotations.csv,
SHA256 572f71b8770b4190cc6806000bde6a4e118f0c17d758faef0a7a5d0e4fbaa81f.
Read prediction columns center_z/center_y/center_x from the payload root's
candidate02_retry/staged-input_openhcs/checkpoints_results/image.ome.tif_site-1_channel-1_timepoint-1_volume_centres_step0_details.csv,
SHA256 b45813b71b66e84682a2db77f8d481c40ced84e40b699846f02d1cca425b6575.
Call score_points(reference, prediction, threshold) for 10,20,30,40.
The coordinator's original table-only evaluation exited0; no environment,
dependency, new scorer or live viewer was created.
