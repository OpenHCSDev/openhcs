# Annotated datasets for an additional agent-operation pilot

Date: 15 September 2026. Research and source inspection only; no analyses run.

## Recommendation

Independent annotations would strengthen the agent result by measuring biological output quality separately from successful execution. For the manuscript, start with **BBBC039 nuclei**, **BBBC007 nucleus-to-cell segmentation**, and **BBBC013 translocation**. These cover chemically varied nuclear phenotypes, two-channel object association, and a downstream assay endpoint using existing OpenHCS functions. BBBC039 and BBBC007 share nuclear segmentation, but BBBC007 additionally tests seeded cell boundaries and channel association. BBBC013 adds a different scientific endpoint; its reference is assay-level, not manual object truth. If manual object annotations are required for every additional task, replace BBBC013 with **BBBC010 overlapping worms**. A smaller two-dataset pilot can use BBBC039 and BBBC013 (or BBBC010); retain the current NeuronCyto II example as the neurite-specific case.

The current Figure 3 is a historical run, not a ground-truth accuracy result. Evaluating its retained outputs against newly located NeuronCyto II reference measurements is a retrospective evaluation. Algorithm corrections and new agent runs must remain separate records. Correcting field 1 and obtaining the expected cell count does not by itself show generalization.

## Current-example repair and media refresh

These deliverables are part of the plan, separately from the additional-dataset
pilot. They are pending, not completed by the retrospective manuscript update.

1. Diagnose and correct the soma/nuclear over-segmentation and crossover
   assignments through the existing segmentation and tracing abstractions.
   Validate object identities and paths against the images and available
   independent references; matching an expected count alone is insufficient.
2. Re-run the corrected workflow into a separate output directory, preserving
   its pipeline, software revision, measurements and validation record. Keep
   the original unattended run and its subsequent correction records intact.
3. Rebuild **Figure 3** from the validated result using the existing figure
   generator and capture infrastructure. Show the neuronal and nuclear inputs,
   aligned object outlines and inspectable paths, including the previously
   problematic soma and crossing. Update the caption, Results and provenance
   together so a corrected capture is not presented as the original unattended
   run. Rebuild and visually inspect the manuscript PDF.
4. Replace the affected **website media-gallery screenshot** with a fresh
   capture of that same validated result through the supported MCP/UI capture
   path. Trace its gallery declaration and derived assets, update the associated
   caption and provenance, and inspect the rendered gallery. Check linked
   thumbnails/posters for the same stale image; preserve historical videos
   with their correct labels rather than silently changing their provenance.

## Active implementation checkpoint

The 15 September 2026 current-source GUI/MCP rerun now preserves one bottom
nucleus and soma (eight of each across the field). Final filled neuron labels
project rooted trace ownership rather than secondary propagation. Both reported
crossings were checked in isolated native viewer captures. A subsequent user
review found a short gap in the cyan neuron's left filled neurite: the measured
path repairs that gap using local signal, but expansion clips it against the
earlier detector foreground. A regression reproduces this projection failure;
the fix must preserve final trace support, not invent a connection. Core edits
are coordinated around the independent author trial's stable source generation.

BBBC039, BBBC007 and BBBC013 input/reference partitions are frozen separately;
their preparation receipt and scoring declarations are recorded in
`benchmark/annotated_validation_20260915.md`. A fresh Sol BBBC039 trial is using
the desktop MCP surface and its own viewer, without reference annotations.
Retain its first result, development iterations and operational friction;
freeze before held-out scoring. Other assay authoring trials remain pending.

Additional user-requested scope:

- Validate padded label convex-hull flashing in the live UI. Generic
  pyqt-reactive changes pass native Qt paint tests, including 2x DPI.
- Validate definition editing during execution without changing the submitted
  plan or losing active progress. Structural guards and regression tests are
  repaired; live acceptance remains pending.
- Compare the user's own neurite-outgrowth experiment under
  `/run/media/ts/0BA20E780BA20E78/axotomy_testing/2026-09-04-(complete)/neurite outgrowth`
  with the retained MetaXpress summaries. Initial inventory identifies two
  separate 6 September analogue/control plates, raw images and well summaries,
  not the existing axotomy PRE/POST analysis. Match actual plate/layout identities
  and aggregation; use MetaXpress as an independent comparator, not biological
  ground truth. The inventory/protocol is delegated in parallel.

Figure 3, the gallery replacement and manuscript integration remain pending
until the corrected implementation's final live checks and measured validation
are recorded. Historical evidence remains unchanged.

### Manager preview demonstration

Add native screenshots of the Plate Manager and Pipeline Editor list previews,
not only the individual parameter forms. Show the same row in compact and
expanded/wrapped modes, with its effective configuration readable. Include a
real field differing from defaults (the `_`/underline marker) and a real
unsaved field (the `*` marker), followed by its saved state. These meanings
already belong to the shared form/list state projections; use those owners
and existing gallery capture declarations, not staged or painted markers.
Pair the row with its corresponding form or code document where useful.
Keep the main UI visible in at least one composition. Use matching parent and
step configurations to make the inheritance bridge readable across the manager
preview and the individual form: inherited value, explicit override, unsaved
edit, then saved override. Captions must distinguish underline styling from a
literal underscore and derive the marker meanings from the existing renderer.
Do not interrupt or modify the running blinded scientific workflow to capture
this demonstration; use a separate engineering state after UI ownership is
released. Keep new captures and captions distinct from historical trial media.

## Dataset candidates

| Dataset | Independent reference and task | Files and scale | OpenHCS feasibility | Priority |
| --- | --- | --- | --- | --- |
| [BBBC039](https://bbbc.broadinstitute.org/BBBC039) | Approximately 23,000 manually annotated nuclei across 200 chemical-perturbation fields; instance segmentation | Single Hoechst channel, 200 TIFF fields, 520 x 696, 16 bit; images 77.9 MB, masks 2.8 MB, split metadata 18 KB | `identify_primary_objects`; normalization/enhancement and `measure_object_size_shape`; evaluate retained labels independently | First: explicit train/validation/test partitions and clear split/merge errors |
| [BBBC007](https://bbbc.broadinstitute.org/BBBC007) | Hand-outlined nuclei and cells, with one outlined cell per nucleus; adjacent-cell boundaries | Paired DNA/actin TIFF channels, approximately 512 x 512, 8 bit; images 6.2 MB, outlines 638 KB | `identify_primary_objects` then `identify_secondary_objects`; measures source binding, nuclear seeding and cell identity | First: directly relevant to the erroneous soma split in Figure 3 |
| [BBBC010](https://bbbc.broadinstitute.org/BBBC010) | Human-corrected foreground plus a separate binary mask for each worm, including overlap; experimental positive/negative control labels | 100 images from a control plate; brightfield/GFP TIFFs, 696 x 520, 16 bit; images about 70 MB, individual masks 2.7 MB | `untangle_worms_with_overlap` / `untangle_worms_both`, or thresholding and `identify_dead_worms`; shape measurements | Alternative: meaningful non-neuronal task and explicit overlap truth |
| [BBBC013](https://bbbc.broadinstitute.org/BBBC013) | Experimental treatment/plate-map labels and published assay Z'/V factors; nuclear translocation | FKHR-GFP/DNA, 640 x 640; BMP images 31 MB, native FRM 77 MB; two drugs and replicated dose curves | Primary/secondary/tertiary object segmentation, `measure_object_intensity`, `calculate_math`; dose-response summary | First: complementary assay-level evaluation, not manual segmentation truth |
| [BBBC038](https://bbbc.broadinstitute.org/BBBC038) | Broad-created manual per-nucleus masks and publicly released challenge solutions; varied stains, organisms and imaging contexts | PNG inputs and masks; training archive 82.9 MB, stage-1 test images 9.5 MB, stage-2 test 289.7 MB | Existing nuclei segmentation; stratify fluorescent versus histology images rather than assuming one preprocessing choice | Reserve: more acquisition diversity, but partly overlaps BBBC039 |
| [DIADEM olfactory projection fibers](https://diadem.janelia.org/olfactory_projection_fibers_readme.html) | Nine independently traced 3D axonal arbors with aligned SWC reconstructions | Confocal-derived TIFF stacks, 512 x 512, 8 bit, 60-101 planes; RAR archive 18.2 MB | 3D skeleton measurements exist, but the current neurite-outgrowth function is not a demonstrated substitute for rooted volumetric tracing | Later: genuine spatial neurite truth, but a method-development task rather than a quick validation run |

### References, licenses and scoring details

- **BBBC039:** CC0. Cite Caicedo et al. and the BBBC collection as specified on the [dataset page](https://bbbc.broadinstitute.org/BBBC039). Decode colored PNG masks using the linked reference decoder; use the supplied partitions. Score one-to-one object matching at IoU 0.5, object precision/recall/F1, split/merge counts and pixel Dice. These are proposed pilot metrics, not scores already obtained. Do not choose thresholds by inspecting test masks.
- **BBBC007:** Public-domain waiver for images and truth; cite Jones et al., CVBIA 2005, and BBBC. Its [published boundary evaluation](https://bbbc.broadinstitute.org/BBBC007) measures the fraction of relevant adjacent-cell boundary pixels within two pixels of a manual boundary. Preserve that metric and add nucleus/cell count and association errors. Inspect outline encoding before converting outlines to filled instances; do not silently fill ambiguous/open boundaries. Never supply manual nuclear seeds to the agent in an end-to-end raw-image trial. An annotation-seeded boundary-only trial is a different task.
- **BBBC010:** CC0; cite the Ausubel image set, BBBC, and Wahlby et al., Nature Methods 2012. The [reported 81%/94% figures](https://bbbc.broadinstitute.org/BBBC010) differ by automatic versus manually corrected foreground, so they are not interchangeable end-to-end baselines. Match independent per-worm masks to predictions without removing overlapping pixels. Report object F1 and count error; treatment labels support control separation, not exact individual live/dead truth. Verify the v2 image/v1 annotation filename pairing before scoring.
- **BBBC013:** CC BY 3.0, Ilya Ravkin. Cite BBBC and Logan/Carpenter 2010 or Carpenter et al. 2006 as appropriate. [Published Z'/V factors](https://bbbc.broadinstitute.org/BBBC013) are assay-level reference results, not fixed per-object intensity ground truth. Report control separation and dose response under a declared measurement definition; numerical disagreement with a published factor is not automatically an implementation error. Do not provide its reproduction pipeline to the agent if evaluating autonomous authoring.
- **BBBC038:** CC0; cite Caicedo et al., Nature Methods 2019, DOI [10.1038/s41592-019-0612-7](https://doi.org/10.1038/s41592-019-0612-7). Freeze the annotation version, obey ignored-image flags, and exclude BBBC039 overlaps if both datasets are used. Public challenge masks/solutions are independent annotations, but are particularly exposed to pretraining contamination. Do not claim that fresh context makes them unseen to the model.
- **DIADEM:** Cite Brown et al., Neuroinformatics 2011. [Official documentation](https://diadem.janelia.org/data_sets.html) supplies manual/semi-manual traces and coordinate rules, but no explicit redistribution license was found on the pages inspected. Verify permission before redistributing files. Use the supplied training/qualifier/final allocation and dataset-specific [DIADEM metric](https://diadem.janelia.org/metric.html). SWC coordinates use pixel XY and plane-index Z; physical scaling must follow the README. Flattening the stacks would change the task and cannot validate the original 3D references.

Existing functions were inspected in `openhcs/processing/backends/cellprofiler/{primary_objects,secondary,intensity,shape,worms,measurement_math,skeleton,object_overlap}.py`. This establishes implementation availability, not successful current-MCP authoring or biological accuracy on these datasets. Worm descriptors/training-derived parameters may require additional setup; benchmark those choices on development images, not held-out masks.

## Verified public download endpoints

All endpoints below returned HTTP 200 to HEAD requests on 15 September 2026, with ZIP/RAR content types where applicable. No bulk archive was downloaded or decoded in this search; HTTP availability is not a verification of every contained annotation.

- BBBC039: [images](https://data.broadinstitute.org/bbbc/BBBC039/images.zip), [masks](https://data.broadinstitute.org/bbbc/BBBC039/masks.zip), [partitions](https://data.broadinstitute.org/bbbc/BBBC039/metadata.zip).
- BBBC007: [images](https://data.broadinstitute.org/bbbc/BBBC007/BBBC007_v1_images.zip), [manual outlines](https://data.broadinstitute.org/bbbc/BBBC007/BBBC007_v1_outlines.zip).
- BBBC010: [images v2](https://data.broadinstitute.org/bbbc/BBBC010/BBBC010_v2_images.zip), [foreground](https://data.broadinstitute.org/bbbc/BBBC010/BBBC010_v1_foreground.zip), [individual worm masks](https://data.broadinstitute.org/bbbc/BBBC010/BBBC010_v1_foreground_eachworm.zip).
- BBBC013: [BMP images](https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_images_bmp.zip), [plate-map loader file](https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_platemap_all.txt). Inspect the linked treatment maps/loader before interpreting its very small loader file as the entire experimental layout.
- BBBC038: [training images/masks](https://data.broadinstitute.org/bbbc/BBBC038/stage1_train.zip), [released stage-1 solution](https://data.broadinstitute.org/bbbc/BBBC038/stage1_solution.csv).
- DIADEM: [olfactory stacks and SWC references](https://diadem.janelia.org/datasets/Olfactory%20Projection%20Fibers.rar).

## Minimal fixed protocol

1. First verify annotation/image identities, coordinate conventions and licensing; freeze checksums, dataset version, image selection and scoring code before agent trials. Keep truth outside the MCP-accessible input/output roots.
2. Give each fresh agent the same operational guide and prompt template: assay aim, channel descriptions, raw input root, output requirements, allowed tools and budget. Give neither a solved pipeline nor reference masks/counts. Record explicit biology supplied by the prompt; this evaluates authoring with that information, not autonomous assay identification.
3. Proposed cap: 15 minutes and 150 MCP calls per authoring trial, matching the order of the existing 609-second/140-call demonstration. Record which limit stopped the run. Allow MCP repairs within the cap; prohibit shell/source inspection and new custom implementations in the initial pilot, as in the historical trial.
4. Have the agent author and visually inspect on a fixed development subset; then freeze the generated workflow and execute it unchanged on held-out images. BBBC039 uses official partitions. For BBBC007/010, preselect development and evaluation fields with a fixed seed and balance control wells where relevant; do not select attractive examples after seeing outputs. A candidate pilot is 3-5 development fields and at least 10 held-out fields per task, subject to actual annotation coverage.
5. Prefer three independent authoring trials per task (6-9 total) if practical. Keep one trial per task explicitly a feasibility case series, not a reliability estimate. Images and cells are not independent agent trials. Retain every attempted trial, including failures, and score all held-out outputs through one independent evaluator.
6. Score the frozen first-run outputs before revealing ground truth or making any human-assisted corrections. Report operational completion, validation refusals, authoring time/calls, scientific metrics and reviewer-identified mistakes separately. If an algorithm is repaired after scoring, retain the initial scores and label subsequent trials as a new software version. Do not pool corrected historical outputs with fresh-agent performance. The published NeuronCyto II cell list is not an explicit guarantee of exhaustive spatial annotation; nine detected objects versus eight listed traced cells is not automatically a demonstrated single false positive.

For the manuscript, this can support a compact finding about reviewable agent-authored workflows across distinct assays, plus independent object-quality measurements. It cannot establish general autonomous scientific competence from two or three datasets. The existing CellProfiler comparisons answer a different question: preservation of selected native-tool outputs, not correctness against independent biological annotations.
