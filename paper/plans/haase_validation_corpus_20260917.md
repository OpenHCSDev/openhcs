# Robert Haase and clEsperanto validation-corpus audit

Date: 2026-09-17

This is a discovery and evidence-classification report. It does not claim that
OpenHCS has run or passed any candidate below. It identifies a reproducible
panel for comparing autonomous pipeline authoring across agents after the
current BBBC039, BBBC007, and BBBC013 work is complete.

The sources were inspected at these revisions:

- [BioImageAnalysisNotebooks `68845a1afaf53bf601958a3fa7d86f3cf8a43219`](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/tree/68845a1afaf53bf601958a3fa7d86f3cf8a43219)
- [human-eval-bia `f6edaa15545e84951f5428d07e16db04155f2266`](https://github.com/haesleinhuepf/human-eval-bia/tree/f6edaa15545e84951f5428d07e16db04155f2266)

BioImageAnalysisNotebooks code is BSD-3-Clause and its book content is CC BY
4.0 unless an individual dataset states otherwise. human-eval-bia is MIT
licensed. Dataset licences remain dataset-owned and are recorded separately
below.

## Evidence classes

- **Independent ground truth**: manual or independently curated annotations
  remain hidden from the authoring agent until the pipeline is frozen.
- **Deterministic parity**: a pinned notebook, assertion, array, or table defines
  an exact computational result. This validates translation and execution, not
  biological truth.
- **Visual/QC only**: the notebook provides an algorithm and plausible output
  but no accepted independent reference. It can test agent workflow and
  evidence gathering, not accuracy.

Evidence quality is graded A when an independent reference and suitable metric
are both available, B when exact deterministic outputs are available without
biological ground truth, and C when only reproducible visual or structural
checks are available.

## Recommended first-wave panel

| Candidate | Evidence | Source and data | Licence and approximate size | Expected output | Dependencies | Likely OpenHCS translation | Validation metric | Quality |
|---|---|---|---|---|---|---|---|---|
| BBBC039 nuclei | Independent ground truth | [Official record](https://bbbc.broadinstitute.org/BBBC039), [images](https://data.broadinstitute.org/bbbc/BBBC039/images.zip), [masks](https://data.broadinstitute.org/bbbc/BBBC039/masks.zip), [metadata](https://data.broadinstitute.org/bbbc/BBBC039/metadata.zip), [official mask decoder](https://gist.github.com/jccaicedo/15e811722fca51e3ae90e8b43057f075) | CC0; 200 520 by 696 16-bit fields, about 77.9 MB of images, 2.8 MB of masks, and 18 KB of metadata | Instance masks for about 23,000 manually annotated U2OS nuclei | TIFF/PNG reader; connected-component decoding for the colour masks | Agent selects or authors a 2-D nucleus instance-segmentation workflow; masks are withheld until freeze | Object matching, IoU/Jaccard, AJI or PQ, split/merge counts, boundary error, object-count and area error | A; strongest held-out test for the present over-segmentation failure |
| BBBC007 nuclei and cells | Independent ground truth | [Official record](https://bbbc.broadinstitute.org/BBBC007), [images](https://data.broadinstitute.org/bbbc/BBBC007/BBBC007_v1_images.zip), [outlines](https://data.broadinstitute.org/bbbc/BBBC007/BBBC007_v1_outlines.zip), Haase [sparse-Jaccard notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/segmentation_quality_estimation.ipynb) | Broad waived copyright/CC0; full images about 6.2 MB and outlines about 638 KB; Haase repository also contains six 340 by 340 crops and sparse annotations | Hand-outlined nuclei and cells in DNA/actin images | scikit-image; optional `napari-segment-blobs-and-things-with-membranes` and `the-segmentation-game` for notebook parity | Source bindings for two channels, seeded nucleus/cell segmentation, label and measurement artifacts | Official boundary-pixel score within 2 px; sparse Jaccard only for the Haase tutorial subset; split/merge, count and area distributions | A for official outlines; the sparse Haase subset is supervised tutorial evidence, not a headline test |
| `cells3d` centroid detection | Independent point ground truth | Haase [spot-counting notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/validate-spot-counting.ipynb), checked-in [`cells3d_annotations.csv`](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/cells3d_annotations.csv) and [`cells3d_nuclei.tif`](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/cells3d_nuclei.tif) | Fifteen manually annotated centroids; each 60 by 256 by 256 channel is about 7.9 MB. The local source note says public domain, but scikit-image historically recorded uncertainty about the original data licence; resolve before redistribution | Detected 3-D nucleus centroids and point table | pyclesperanto or equivalent Gaussian blur, local maxima, labeling, and centroid measurement | A chain of registry functions or one reviewed custom function returning point/spatial-graph and table artifacts | One-to-one matching over a preregistered distance sweep; TP, FP, FN, ambiguous matches, F1, localization error and count error | A for point detection after the licence is resolved; not an object-mask reference |
| Platynereis 3-D labels | Independent-reference metric exercise | Haase [metric notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/metrics_to_investigate_segmentation_quality.ipynb), [Zenodo source](https://doi.org/10.5281/zenodo.1063531), checked-in [reference](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/Platynereis_tp7_channel1_rescaled%28256x256x103%29_gt.tif) and [Voronoi-Otsu result](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/Platynereis_tp7_channel1_rescaled%28256x256x103%29_voronoi_otsu_label_image.tif) | The two 103 by 256 by 256 arrays total about 190 KB. Haase's note says CC BY 4.0, but associated publication text has also been described as CC BY-NC-ND; verify the Zenodo record before redistribution | Reference labels, comparison labels, sparse/binary Jaccard, precision, recall, F1 and confusion matrix | scikit-image, scikit-learn, optional `the-segmentation-game` | Begin as a metric/artifact parity task; use the raw Zenodo data for a blind segmentation task only after its exact input/reference mapping is verified | Exact metric parity plus object-level 3-D overlap and orthogonal-slice review | A for label comparison, but not yet a blind end-to-end pipeline from the two checked-in arrays alone |
| human-eval-bia image functions | Deterministic parity | [57 pinned task notebooks](https://github.com/haesleinhuepf/human-eval-bia/tree/f6edaa15545e84951f5428d07e16db04155f2266/test_cases) | MIT; most tasks use tiny synthetic arrays and notebooks of roughly 2 to 12 KB | Exact scalars, arrays, columns, or bounded numeric values encoded by each `check` function | Per-task scientific Python dependencies; never use the repository's untrusted-code execution harness | Register the requested function through OpenHCS, expose its reflected controls, compose a FunctionStep, execute and materialize its typed result | Reuse the task's exact/tolerance assertion and additionally verify OpenHCS contract, schema, code/UI round trip and artifact provenance | B; best low-cost cross-agent function-authoring track |
| Cross-library Otsu plus labeling | Deterministic parity | Haase [scenario](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/scenario_otsu_segmentation.ipynb), [visual comparison](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/visual_comparison.ipynb), [quantitative comparison](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/29_algorithm_validation/quantiative_comparison.ipynb), and checked-in arrays in the same directory | Repository licence; input and four output TIFFs total about 1.2 MB | scikit-image and clEsperanto outputs have zero binary XOR pixels; ImageJ differs by 830 pixels. Counts are 64 versus 63, with committed area vectors and summary statistics | scikit-image, pyclesperanto, optional Fiji for the ImageJ branch | Ordinary Otsu and connected-component steps on NumPy and pyclesperanto backends; Fiji output is an external reference | Exact binary XOR, count, per-object area vector/distribution, and table parity | B; unusually good backend-parity test, not biological ground truth |
| S-BIAD634 folder workflows | Deterministic parity with supplied labels | [human-eval-bia example data](https://github.com/haesleinhuepf/human-eval-bia/tree/f6edaa15545e84951f5428d07e16db04155f2266/example_data/S-BIAD634), [source study](https://www.ebi.ac.uk/biostudies/BioImages/studies/S-BIAD634), [count task](https://github.com/haesleinhuepf/human-eval-bia/blob/f6edaa15545e84951f5428d07e16db04155f2266/test_cases/workflow_batch_process_folder_count_labels.ipynb), [measurement task](https://github.com/haesleinhuepf/human-eval-bia/blob/f6edaa15545e84951f5428d07e16db04155f2266/test_cases/workflow_batch_process_folder_measure_intensity.ipynb) | About 32 MB in the repository. The local readme names the source but not a clear redistribution licence; verify before repackaging | Exact label counts 300, 398, 368, 378 and 363; measurement table with 1,807 rows, five columns, label maximum 398, intensity extrema 7 and 255 | TIFF reader, NumPy, pandas, scikit-image | Folder ingestion, paired image/label source bindings, label counting and per-object measurement artifacts | Exact counts, row/column schema, extrema and bounded numeric assertions | B until provenance/licence and reference-generation history are clarified |

## Second-wave visual and volumetric tasks

| Candidate | Source/data | Licence and size | OpenHCS task | Required checks | Quality |
|---|---|---|---|---|---|
| BBBC022 Voronoi-Otsu | Haase [notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/20_image_segmentation/11_voronoi_otsu_labeling.ipynb), [official record](https://bbbc.broadinstitute.org/BBBC022) | CC0; checked-in crop 1.65 MB, full experiment much larger | Translate the fixed `spot_sigma=5`, `outline_sigma=1` workflow; exercise pyclesperanto or a reviewed custom function | Exact parameter provenance, object count/area distribution, high-saturation raw/label overlay and field-uniformity checks | C; deterministic algorithm but no manual reference in the notebook |
| BBBC032 3-D blastocyst | Haase [3-D notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/20_image_segmentation/Segmentation_3D.ipynb), [official record](https://bbbc.broadinstitute.org/BBBC032) | Broad waived rights; checked-in resampled crop 13.4 MB, full images about 1.14 GB plus about 473.5 MB of ground truth | Isotropic resampling, global-versus-slice intensity handling, 3-D background correction and segmentation | Orthogonal raw/label overlays, 3-D continuity, slice-uniformity, object matching against official GT when the full reference track is prepared | C for the tutorial crop; A is possible with the official manual reference |
| Tiled nuclei counting | Haase [notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/32_tiled_image_processing/tiled_nuclei_counting.ipynb), [Zenodo source](https://zenodo.org/records/4276076) | Notebook states CC BY 4.0; checked-in crop about 21 MB | Custom count function over tiles, count-map artifact, memory and tile-boundary behavior | Count-map schema, edge/interior distributions, seams, overlap sensitivity and percentile-matched visual review | C; no manual GT in the notebook |
| Cancer-cell migration | Haase [tracking notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/34_timelapse_analysis/tracking.ipynb), [Zenodo source](https://zenodo.org/records/5206107) | Checked-in crop 1.6 MB plus 3.3 MB labels; source record about 140.6 MB. Verify the source licence before redistribution | Time-axis ingestion, object measurements, btrack/custom tracking, table and Napari Tracks artifacts | Track count/schema, frame continuity, gaps, splits/merges and label/track overlay | C; supplied segmentation is a deterministic input, not accepted tracking GT |
| Membrane segmentation/post-processing | Haase [refinement notebook](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/20h_segmentation_post_processing/refine_cell_segmentation.ipynb) | Checked-in time lapse about 656 KB; courtesy attribution but no clear redistribution licence | Membrane segmentation, border removal and temporal consistency | Same-coordinate percentile overlays, object counts, retained-border objects and stability across time | C; local visual use only until permission is confirmed |

BBBC013 remains valuable as a separate plate-level biological track: use the
[official images, plate map and reproduction package](https://bbbc.broadinstitute.org/BBBC013)
to compare treatment/control ordering, dose response, Z-prime/V factors and
nuclear-to-cytoplasmic translocation. It has no manual object masks and must not
be presented as segmentation ground truth.

## Cross-agent execution protocol

1. Pin the source commit, dataset record, OpenHCS commit, environment lock,
   authoring-context revision, model route and complete prompt before the run.
2. Give every agent the same biological objective and data subset, but do not
   reveal manual masks, centroids, held-out assertions or accepted metrics.
3. Require health, first-use routing and the registered
   `image_analysis_workflow` context. Let the agent search the live function and
   example catalogues; custom functions remain valid when registered through
   the same reflected contract path.
4. Preserve every attempt, pipeline snapshot, validation/compile error, MCP
   event, generated source, dependency decision and output root. A failed
   attempt is operational evidence, not a file to overwrite.
5. Use a declared development subset for tuning. Freeze the complete pipeline
   and parameters before exposing the hidden reference or scoring a held-out
   field. Execute each held-out score once unless a preregistered infrastructure
   failure invalidates the run.
6. Score task correctness and operational autonomy separately. Task evidence
   includes the metric named above plus raw/result overlays at identical
   coordinates and multiple percentile clips. Operational evidence includes
   valid declarations, compile refusals, successful recovery, tool calls,
   elapsed time, manual interventions and custom-function use.
7. Compare models on the same frozen cases and repeat count. Do not pool a
   supervised BBBC007 tutorial, a hidden BBBC039 reference and a visual-only
   BBBC022 tutorial into one accuracy number.

## Selection recommendation

Start with six to ten exact human-eval-bia functions and the `blobs` backend
parity case because they are cheap and expose translation errors. Run BBBC039
as the main held-out segmentation challenge, BBBC007 as the boundary/sparse
reference track, and BBBC013 as the orthogonal plate-level biological track.
Add `cells3d` for 3-D point detection after resolving its data licence. Add
BBBC032 or Platynereis for volumetric evidence only after confirming the exact
raw/reference mapping and licence. Keep BBBC022, tiled counting, tracking and
membrane examples labelled visual/QC-only until an independent reference is
added.

