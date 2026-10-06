# Notebook-derived blind task presets

Coordinator reference, 2026-09-27. Do not give this file, the source notebooks,
or the evaluator directory to an authoring agent. The source collection is
[Bio-Image Analysis Notebooks](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/tree/68845a1afaf53bf601958a3fa7d86f3cf8a43219),
pinned at `68845a1afaf53bf601958a3fa7d86f3cf8a43219`. The earlier
[translation audit](../paper/plans/haase_notebook_translation_candidates_20260915.md)
and [validation-corpus audit](../paper/plans/haase_validation_corpus_20260917.md)
give the detailed provenance and caveats. This index records launch readiness.

| ID | Agent-visible task | Sealed evaluator evidence | Endpoint | State |
| --- | --- | --- | --- | --- |
| H001 | Segment bright objects in one 2-D greyscale image; retain instance labels and an object table. | The pinned [Otsu/label example](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/scenario_otsu_segmentation.ipynb) and four saved label arrays. | Foreground-mask disagreement, ID-independent object matching, count and area distribution, plus raw/label QA. Computational parity, **not** manual biological truth. | Input and evaluator staged. First fresh-agent attempt froze as rejected after a runtime filename-address failure and unsupported instance splits; no notebook score was run. |
| H002 | Detect 3-D nucleus centres from one volume and save point coordinates. | The [spot-counting notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/validate-spot-counting.ipynb) and its 15 manually annotated centres. | Predeclared-distance one-to-one point matching, localisation error and count error in voxel coordinates. | Input and reference staged locally. A lossless ZYX OME-TIFF wrapper exposes all 60 Z planes through OpenHCS. Fresh blind-agent run froze as QA-rejected for unsupported border/low-Z points and split nuclei; no reference score or physical calibration. Resolve the underlying `cells3d` licence before redistribution. |
| H003 | Segment nuclei and cells in paired DNA/actin images. | [BBBC007 manual outlines](https://bbbc.broadinstitute.org/BBBC007), with the [Haase sparse-Jaccard example](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/segmentation_quality_estimation.ipynb) as a separate tutorial comparison. | Official directed adjacent-cell boundary score within 2 px, nuclear-count and nucleus–cell overlap diagnostics; raw/result QA. Monochrome outlines do not support object IoU or split/merge truth. | One prior-development field and private outlines staged; source hashes verified. Fresh MCP inspection found two separate inferred samples, each channel 1; typed two-channel source projection must compile before launch. |
| H004 | Apply a supplied frozen morphology classifier to segmented objects in the small blobs image. | The [APOC object-classifier notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/27_cell_classification/apoc_object_classifier.ipynb) and its frozen per-object predictions; the model must be agent-visible input. | Per-object class parity by stable instance identity and a rotation check. | Not staged or launchable: needs pinned reference predictions and a reviewed APOC adapter using the existing `PlateInputFile` declaration. Image-only classification with both model and strokes withheld would be underdetermined. Model parity is not independent biological truth. |
| H005 | Link objects across a 48-frame time series. | The [btrack notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/34_timelapse_analysis/tracking.ipynb) and a reference link table to be generated. | Link and track-membership agreement modulo track-ID renaming. | Not launchable: no machine-readable reference track has been frozen. |

H001's neutral input is
`mcp_outputs/haase_blind_20260927/inputs/H001/image.tif` (SHA-256
`26403a7c2a11921535499ff86798b73e09b8ac5786329bce8fa4a57fd9933fee`).
It is a 254 × 256 `float32` greyscale TIFF. Its agent-facing contract is beside
it. The evaluator notebooks and outputs are outside the repository at
`/home/ts/.local/share/openhcs-blind-evaluation/haase_otsu_20260927/`;
the evaluator manifest there records exact digests and the fixed primary
reference. Neither that path nor this coordinator reference belongs in an
agent prompt. The coordinator-only [instance scorer](score_instance_labels.py)
compares masks and objects without assuming identical label numbering; its
five focused tests and pinned-output self/variant checks pass. Do not score
any agent output until its pipeline and QA decision are frozen.
The first H001 attempt's independent
[trial report](../mcp_outputs/haase_blind_20260927/trials/H001_astra_20260927/TRIAL_REPORT.md)
and frozen bundle retain the pipeline, compile/run receipts, partial arrays,
and six personally inspected raw/ROI witnesses. Compilation passed;
execution did not complete. Its partial arrays are diagnostics, not a scored
prediction.

H002's neutral input is `mcp_outputs/haase_blind_20260927/inputs/H002/image.ome.tif`
(SHA-256 `4159cea76f174acb51e11abc6885a0bb6aeaaf401f6371f362c9f4f100a891f7`).
The [lossless wrapper](prepare_haase_cells3d_ome.py) verified voxel equality
against the pinned 60 × 256 × 256 `uint16` source and declared `ZYX` axes;
read-only OpenHCS inspection found 60 of 60 Z planes with no parse errors.
Its reported pixel size of 1 is a placeholder, not physical calibration.
The source image, 15-point reference CSV and notebook remain in the private
evaluator directory `haase_cells3d_20260927` outside the repository.
The coordinator-only [point scorer](score_point_centres.py) uses one-to-one
matching at a preregistered voxel-distance threshold; its six focused tests
and reference self-check pass. It has not been applied to an agent result.
The fresh H002 [trial QA](../mcp_outputs/haase_blind_20260927/trials/H002_sol_20260927/QA.md)
and file manifest freeze a completed execution with 115 provisional point rows,
but reject the candidate after visual review of same-coordinate raw/ROI slices
and orthogonal raw/point cuts. Those rows are diagnostics, not accepted nuclei.
The user's separate over-segmentation observation was not sent to the agent
during the blind run; its frozen rejection was independent of that feedback.

H003's agent-only [input contract](../mcp_outputs/haase_blind_20260927/inputs/H003/BRIEF.md)
uses the two 400 × 400 greyscale DNA/actin TIFFs from BBBC007 field A02 in
the prior development split. Their SHA-256 digests are
`cb97674830100b30b15c13677a8753d5bc6b0c5773ce9c125914207eb8766607`
and `74753e8d820a6982f0871a91643ae1883552977ab5d341a24ab0f07abc7f00f1`.
The originals and matching hand-drawn outlines are sealed in
`/home/ts/.local/share/openhcs-blind-evaluation/haase_bbbc007_20260927/`,
with an evaluator manifest and the fixed `score_007` scoring contract.
This is an official-manual-outline task, not exact reproduction of the Haase
sparse-Jaccard notebook. Fresh MCP inspection on server PID 1516985 found two
readable 400 × 400 `uint8` planes, but automatic Bio-Formats discovery projected
their physical filenames as two separate samples, each with channel 1. The
ImageXpress parser recognized both names but lacked its required HTD metadata.
The agent-facing brief now requires typed exact-file source bindings to project
the shared A02 well with distinct channels 1 and 2. A read-only artifact-plan
preflight first rejected a tuple where the typed declaration required a list;
the corrected request hit the MCP call boundary's 10-second timeout without a
compile receipt. Health remained current afterward. Despite the capability's
read-only classification, the timed-out compile initialized
`openhcs_metadata.json` in the input folder. That generated metadata showed one
A02 well with DNA/actin channels 1/2, but no completed step plan; it and its
lock file were moved intact to the coordinator-only
`trials/H003_source_projection_preflight_20260927/` directory. A fresh MCP
inspection confirmed the input folder is back to its original loose-TIFF
Bio-Formats state. Do not launch a blind agent until a compiled
source-workspace receipt proves the two-channel pairing.

H004 has two distinct possible tasks. For *frozen-model inference*, give the
agent the pinned `blobs_object_classifier.cl` model and image as inputs, but
withhold the notebook's per-object class outputs; compare assignments by
instance identity after the pipeline is frozen. For *training from examples*,
give the sparse class strokes as input and withhold a separate test set; the
notebook's training-image predictions alone cannot establish generalisation.
Do not offer an image-only three-class task without either model or examples.
The pinned model declares three features, three classes, ten trees, and APOC
0.6.2; current training defaults are not an exact substitute. OpenHCS already
has a typed plate-relative `PlateInputFile` declaration for a supplied model
path, so the missing piece is an APOC-compatible processing adapter and
verified model provenance, not a second path registry. `apoc` is absent from
the current environment, and a pinned reference run remains prerequisite to
launch.

For every preset, the agent receives only neutral input and the endpoint,
uses OpenHCS MCP, retains a complete PipelineDocument, execution receipts,
per-object data and personally inspected same-coordinate raw/result QA at
several positions and display windows. Freeze those artifacts before the
evaluator opens the notebook output. A visible notebook recipe is a different
*translation* task; it must not be pooled with this blind-from-input track.
The separation is procedural, not an OS access-control boundary, and public
notebook outputs are discoverable online. Record any outside-source access.

Other open candidates found after the local audits: the [Cell Image Library
CCDB:6843](https://ccdb.ucsd.edu/images/CCDB_6843) provides paired
phalloidin/DAPI images and manual neuronal/nuclear boundaries, making it a
possible neurite-related manual-reference task; its published pixel-size
metadata needs verification before physical measurements. The [SH-SY5Y
phase-contrast record](https://zenodo.org/records/19634700) includes raw
images, an ilastik model and example outputs, but no independently established
manual neurite truth in the record inspected. Neither is staged or scored.
