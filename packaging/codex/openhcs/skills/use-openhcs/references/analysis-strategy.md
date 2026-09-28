# Choose an autonomous microscopy analysis strategy

Use this guide when an assay is unfamiliar, before choosing a detector. It is a
task router, not another API catalogue. Retrieve only the relevant companion
guide through the existing knowledge service, then describe the actual callable
returned by the live OpenHCS function registry. A Fiji plugin recipe does not
establish that its implementation or parameters exist in OpenHCS.

## Establish what the images can support

Start from the biological question and acquisition metadata: target, stains,
channels, XY calibration, Z/time axes, controls and independent experimental
units. Inspect the available raw channels together at matched coordinates.
Build a provisional interpretation yourself: nuclei, cell bodies, processes,
puncta, background, debris and ambiguity. Do not wait for the user to tell you
which channel looks useful. Ask for missing acquisition or biological information
when alternative interpretations would materially change the analysis.

Retrieve [openhcs_image_interpretation](image-interpretation.md) for unexpected channel appearance,
clipped highlights, an RGB export, dim signal, uneven background or unclear axes.
It distinguishes missing information from an unhelpful display.

## Match the strategy to the failure

| Observation or task | Retrieve | Decision to make |
| --- | --- | --- |
| Uneven background, noisy seeds, dim objects, bright outliers | [openhcs_image_preprocessing](image-preprocessing.md) | Which nuisance model fits, and what biology must survive? |
| Touching nuclei, one body split, merged cells, zero-growth secondary objects | [openhcs_segmentation_diagnostics](segmentation-diagnostics.md) | Is the failure in foreground, markers, separation or secondary growth? |
| Thin neurites, disconnected traces, puncta or irregular cells | [openhcs_segmentation_diagnostics](segmentation-diagnostics.md) | Does the object model match the target and its topology? |
| Intensity, volume, colocalisation, comparisons or final figures | [openhcs_measurement_interpretation](measurement-interpretation.md) | Which pixels, geometry, units and experimental units support the claim? |
| Repeated errors or transferring a successful recipe | [openhcs_analysis_learning](analysis-learning.md) | Is this a source-backed recipe, an observed repair or an untested hypothesis? |
| No registered operation has the required input/output contract | [openhcs_custom_function_workflow](custom-function-authoring.md) | Can the missing operation become a typed, reproducible registry function? |
| Raw/overlay review or a changed viewer canvas | [openhcs_viewer_qa](viewer-qa.md) | Are the three views matched, interpretable and personally inspected? |

Search the first-class Official30 examples for the closest task, retrieve the
exact OpenHCS Python section and inspect the reference case's inputs and parity
scope. Use it as a working starting point, not as proof for the new assay. The
ExampleHuman nuclei card is one example, not the only eligible pipeline.

## Run a discriminating development trial

Choose a spatially distributed development sample before tuning: bright/dim,
centre/edge, sparse/dense and suspected failure regions. Select a clear positive,
a plausible miss and a regression-control close pair or faint path. Make a
specific prediction about the earliest failed stage and change one operation or
parameter group. Retain its source, parameters and diagnostic intermediate.

Use the canonical `image_analysis_workflow` and `viewer_review` contexts for
native-coordinate raw-only, result-only and combined inspection, numeric display
windows and viewer-state checks; follow [the viewer QA procedure](viewer-qa.md)
for the matched capture set, including user changes to canvas geometry.
Compare raw and processed images separately;
a prettier image or a plausible count does not establish improved segmentation.
If the evidence contradicts the prediction, reject the hypothesis before adding
more stages. Freeze the candidate and acceptance criteria before held-out access.

## Keep execution bounded

Begin with one bounded sample and estimate array bytes from dimensions and
dtype. Include concurrent raw, processed, label, intermediate and viewer copies,
plus model/device memory; file size alone is not a RAM estimate. Limit parallel
jobs and retained viewer layers. When model startup dominates, prefer a supported
resident/batched OpenHCS route with proven grouping and axis semantics; never
reinterpret Z as time just to copy a Fiji batching trick. Retain only the
intermediates needed to diagnose the trial, and confirm job completion before
launching a replacement. Respect the user's isolated display and RAM limits.

## Transfer sources and scope

This is an OpenHCS adaptation of Agentic-J's task-specific knowledge retrieval,
version-scoped plugin recipes and reusable experience approach, inspected at
[`7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67`](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills).
Its `bioimage_course`, `morpholibj_documentation`, `3d_imagej_suite_documentation`,
`cellpose_documentation`, `stardists_documentation`, `coloc2_documentation`,
`image_publication_standarts` and `learned_memory` packs inform the linked guides.
No ImageJ/Groovy execution code, model preference, plugin default or vector
database is imported. OpenHCS contracts and current assay evidence own execution
and acceptance. Better autonomous decisions are the aim, not a demonstrated
accuracy improvement; evaluate them on a frozen blind task before claiming one.
