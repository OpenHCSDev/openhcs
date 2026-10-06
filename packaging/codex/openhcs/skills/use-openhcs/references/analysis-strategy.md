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
| FIRST foreground proposal, especially textured/ring bodies or regional nuisance | [openhcs_image_preprocessing](image-preprocessing.md#normalize-segmentation-inputs-before-tuning), then [openhcs_segmentation_diagnostics](segmentation-diagnostics.md#compare-body-admission-models) | Are the analytical input mapping and units established, and does admission on that alias/response preserve distributed positives while excluding nuisance-only regions? |
| FIRST threshold proposal or widening a positive-only sample to more fields | [openhcs_measurement_interpretation](measurement-interpretation.md#include-no-object-fields-before-widening) | Does the sampled scope include available whole no-object fields as well as genuine dim positives? |
| FIRST marker/declumping proposal, including a shape-based method | [openhcs_measurement_interpretation](measurement-interpretation.md#choose-the-marker-landscape-before-the-first-candidate) | Does the actual chosen landscape distinguish within-body maxima from a genuine pair, with justified competition and spacing units? |
| Uneven background, noisy seeds, dim objects, bright outliers | [openhcs_image_preprocessing](image-preprocessing.md) | Which nuisance model fits, and what biology must survive? |
| Comparable fields of one well or mosaic, including field-by-field analysis | [openhcs_image_preprocessing](image-preprocessing.md#shared-scaling-for-fields-of-one-mosaic) | Does the analysis use the requested shared input scaling over the complete per-channel SITE stack, rather than independent field fits or only internal detector-response scaling? |
| Touching nuclei, one body split, merged cells, zero-growth secondary objects | [openhcs_segmentation_diagnostics](segmentation-diagnostics.md) | Is the failure in foreground, markers, separation or secondary growth? |
| Thin neurites, disconnected traces, puncta or irregular cells | [openhcs_segmentation_diagnostics](segmentation-diagnostics.md) | Does the object model match the target and its topology? |
| Intensity, volume, colocalisation, comparisons or final figures | [openhcs_measurement_interpretation](measurement-interpretation.md) | Which pixels, geometry, units and experimental units support the claim? |
| Choosing size, seed separation, smoothing, background scale or shape priors | [openhcs_measurement_interpretation](measurement-interpretation.md#measure-feature-scales-before-choosing-parameters) | Which representative native raw measurements justify the parameter range? |
| Unfamiliar task, raw morphology conflicting with an example, repeated errors or recipe transfer | [openhcs_analysis_learning](analysis-learning.md#retrieve-before-first-authorship-and-retries) | Which conditional lesson informs the FIRST method, and what raw evidence could disconfirm it? |
| No registered operation has the required input/output contract | [openhcs_custom_function_workflow](custom-function-authoring.md) | Can the missing operation become a typed, reproducible registry function? |
| Raw/overlay review or a changed viewer canvas | [openhcs_viewer_qa](viewer-qa.md) | Are the three views matched, interpretable and personally inspected? |

Search the first-class Official30 examples for the closest task, retrieve the
exact OpenHCS Python section and inspect the reference case's inputs and parity
scope. Use it as a working starting point, not as proof for the new assay. The
ExampleHuman nuclei card is one example, not the only eligible pipeline.

For a first segmentation proposal, use both applicable first-method routes above,
not just the foreground route or a recipe's detector defaults. Retrieve the named
sections before committing method and parameters; their worked examples own the
details. Raw morphology informs support, but admission consumes a particular
alias/response and markers consume a particular landscape. Use the measurement
guide's compound-detector reasoning to map each proposed parameter to ALL its
coupled mechanisms in the reflected callable, not just its apparent size role.
State the predicted effect on distributed positive/nuisance and
continuous-body/genuine-pair controls;
keep marker extraction distinct from the subsequent division boundary. If no
marker stage is proposed, do not invent one merely to follow this route.
Use raw or processed evidence already available; an unproduced enhanced response
or marker landscape remains a provisional hypothesis to inspect in the first
bounded candidate, not a reason to withhold an exploratory proposal. Record an
unavailable control, such as a genuine pair, rather than inventing one or making
its absence an approval gate.

When the task is unfamiliar or raw morphology contradicts an example's method,
follow [pre-authorship learning retrieval](analysis-learning.md#retrieve-before-first-authorship-and-retries)
before adapting it. Retrieve general foreground/marker/division reasoning through
the existing knowledge service, not a sibling task's worked solution. Include the
lesson query/source/applicability in the same example-selection record below;
if none fits, proceed from measured raw evidence rather than waiting for a recipe.

Before authoring, retain an example-selection record in the authorised trial:
the search query, returned document/section ID, retrieved source identity and
`truncated=false`, reference case and available parity evidence, input axes,
channel roles and units, and the decision to adapt or reject it for this assay.
Inspect the complete generated pipeline, not just the search snippet or a
function with a similar name. If none fits, record the closest example's
specific contract mismatch before using the custom-function route. Do not
invent parity evidence when only conversion or execution is evidenced.
Reusable method examples are distinct from a blind task's worked answers;
keep scoring references and held-out material sealed. A later retrieval must
be recorded as later evidence, not retroactively claimed as the basis of an
already frozen candidate.

## Run a discriminating development trial

Choose a spatially distributed development sample before tuning: bright/dim,
centre/edge, sparse/dense and suspected failure regions. Select a clear positive,
a plausible miss and a regression-control close pair or faint path. Make a
specific prediction about the earliest failed stage and change one operation or
parameter group. Retain its source, parameters and diagnostic intermediate.

Before widening a measurement batch or adding a late aggregate, discover the
current artifact-planning and persistence capabilities and inspect the compiled
plan for the selected outputs. Distinguish runtime-only measurements from saved
checkpoints, including their source/object identities and output scope. A global
materialisation flag alone does not prove that every declared output is saved;
retained label images do not establish retained photometry.

When a downstream join or aggregate can fail after expensive upstream work,
retain the minimal per-unit measurements and identities needed to diagnose and
reproduce it through the registered persistence/export route. Check a bounded
saved sample's rows, scope and source identity before expanding. Do not save every
array. If the installed contract cannot retain the required output, report that
specific gap and keep supported analysis moving; distinguish saved results from
runtime-only evidence that may disappear on closure. Preserve failed checkpoints
and uncertain attempts rather than replaying them to reconstruct missing output.

Use the canonical `image_analysis_workflow` and `viewer_review` contexts for
native-coordinate raw-only, result-only and combined inspection, numeric display
windows and viewer-state checks; follow [the viewer QA procedure](viewer-qa.md)
for the matched capture set, including user changes to canvas geometry.
Compare raw and processed images separately;
a prettier image or a plausible count does not establish improved segmentation.
If the evidence contradicts the prediction, reject the hypothesis before adding
more stages. Freeze the candidate and acceptance criteria before held-out access.

Rejection ends that hypothesis, not the authorised development workflow. Preserve
the failed candidate and choose the next discriminating trial from observed raw
and intermediate evidence; recheck the failure and a regression control after
each change. A frozen rejected checkpoint is neither an accepted recipe nor a
reason to wait for the user to select routine parameters. Continue while the
task's trial/resource budget permits useful diagnostics. If progress requires
missing biological information, a missing tool contract, new authority or unsafe
resource use, report the exact boundary and retain the best candidate with its
known failures. Do not force unsupported structures into a mask to finish.

## Scope conclusions to the evidence

Judge each requested claim at its declared object, relationship and spatial
scope. Keep supported findings, clear failures and ambiguous cases distinct,
with their witness and persisted identities. Uncertain body boundaries or path
ownership do not automatically invalidate independently supported centres or
path geometry; those findings do not establish complete bodies or correct
body-to-path associations either. Technical completion remains separate from
these biological judgements.

Autonomous success means materially useful quality for that scope, not perfect
accuracy or exact agreement with human annotations. Report achieved coverage,
clear misses, nuisance admission, splits/merges, boundary quality and downstream
measurement suitability separately across the distributed sample. Link each
judgement to witnesses, spatial extent and uncertainty rather than collapsing
them into a single validated/rejected label. Useful detection can coexist with
uncertain outlines: for detection/counting, assess whether distinct supported
bodies are represented once and localised appropriately, with splits, merges,
material misses and nuisance still affecting that claim. Area, shape and
fluorescence measurements need their own boundary evidence. Do not force outputs
to an expected count or prior candidate's positions. Quantify frequency only
when the reviewed sample supplies a defensible denominator.
Human annotations and algorithms can both be incomplete or mistaken: retain
reference disagreement rather than treating either as exhaustive biological truth.
An isolated plausible error does not automatically reject the whole analysis.
Systematic or material missed paths, false bridges, wrong channels, invalid
units, misaligned geometry or catastrophic failures still reject the affected
claim. Do not invent a universal error tolerance or relax the task's declared
criteria to fit a result.

For neurite outgrowth, distinguish principal-shaft recovery from exhaustive
fine-protrusion tracing before choosing detection settings. State the intended
structures in the task brief and candidate rationale. For a shaft-focused assay,
an appropriate brief is: "Segment the soma-connected thick neurite shafts,
including dim stretches of those shafts; fine filopodia are outside the target."
Thickness and brightness are different: a faint shaft can still belong to the
target. Do not silently expand that endpoint during repair. When the requested
endpoint concerns soma-connected
main shafts, assess their distributed raw support, continuity and false bridges;
unrequested filopodial completeness is not an acceptance gate. Lowering a
threshold to add uncertain twigs or increase graph length/branch counts is not
necessarily an improvement. Retain the author's best-supported candidate with
its inclusion rules and known misses. If the task requires fine-branch counts
or complete arbor length, those finer structures still need their own evidence.

Useful algorithm-defined assay or morphology estimates can include counts and
per-object summaries with stated inclusion rules, observed errors and uncertainty.
They are not biological ground truth. Do not require proof of every body's cell
identity or resolution of every overlap/crossing before reporting any supported
estimate; withhold the particular ownership-dependent metric if its assumptions
fail. Conversely, biased favourable crops cannot establish global accuracy or
excuse material omissions in the distributed review.

Report reviewed coverage, inclusion rules, exclusions with their denominator,
and unresolved cases alongside the supported result. When ambiguity affects a
total, retain a justified lower/upper bound or sensitivity analysis if the evidence permits;
do not invent a confidence interval or silently drop uncertain objects. A few
accepted witnesses do not establish whole-field completeness. Withhold a
whole-population claim when unresolved cases invalidate it, not every unrelated
finding merely because one claim remains uncertain.

When the user accepts an imperfect result for a stated use, retain it as a
practical reviewed baseline with its exact source/result identity, matched
witnesses, supported claims and known limits. This is not proof of unreviewed
claims, independent validation or autonomous performance. Keep that best-reviewed
baseline distinct from the latest local-repair predecessor: compare recovered
coverage and regressions against both when relevant, rather than assuming that
the newest candidate is the best overall. Acceptance need not end useful
development, and an unresolved case need not erase the accepted findings.

Partial support is not a stopping rule for a clear failure. Follow the existing
[earliest-stage diagnosis](segmentation-diagnostics.md), make one discriminating
repair while the authorised budget permits, and revisit distributed regression
controls. Improved downstream paths cannot repair an unchanged failed body
stage; diagnose that stage rather than repeatedly tuning faint-signal thresholds.
Preserve frozen evaluations unchanged. Record a later evaluation-policy change
separately, not as a retroactive author pass; apply new guidance only to future
authorised runs, never as feedback to live blind authors.

## Development corrections and autonomous evaluation

Declare the run's purpose before starting. Development aims to reach an
evidence-supported result and learn which general guidance or software contract
is missing. Preserve the same analysis context through useful corrections;
rejecting a hypothesis or archiving a failed checkpoint does not require a new
agent. Do not impose an arbitrary candidate-count cap on development unless the
task explicitly requires one. Bound work by time, RAM, disk and a discriminating
next action instead. Record every source version and failed attempt, including
technical failures before scientific execution; keep technical repairs distinct
from changes to the analysis hypothesis, without deleting either denominator.

External corrections, including operational guidance or a mid-run harness fix,
make the completed continuation assisted development evidence, not an autonomous
pass. Record who supplied what, when it arrived, the affected source/software
version, and the result after correction. A successful corrected journey can
identify how to reach success; it does not establish that a fresh agent would
discover that journey unaided. If a technical failure requires an engineer,
retain the exact request and owner, and resume development after repair rather
than resetting the scientific context. Observation timeout alone never permits
mutation replay or process replacement; resolve the original handle first.
Preserve already frozen records unchanged and start an explicitly linked
development continuation instead of rewriting their disposition.

For an autonomous-performance evaluation, freeze the harness and skill before a
fresh context-isolated run. Supply only the scientific brief, acquisition facts
and authorised images, not the intended method, suspected failure, prior trial
conclusions or worked answer. Internal agent review may be part of the declared
harness. Self-correction using that frozen harness is autonomous; externally
corrected or repaired continuations are not. If assistance is supplied, retain
the original unassisted outcome and its evaluation denominator, then label the
continuation separately. Do not change a declared evaluation budget mid-run.

Assess autonomous quality on the author's final frozen choice after its own
inspection and repairs, including its decision to retain an earlier candidate
when a revision regresses. A poor first candidate does not fail the whole run
if the author independently reaches a useful result within the declared scope.
Report the first completed prediction separately as an initial-selection and
repair-effort diagnostic, not as the autonomous success criterion. Preserve
first, rejected and final artifacts; do not substitute the evaluator's
highest-scoring attempt for the author's final choice or feed scores back to it.

Transfer only general, tested operational or reasoning improvements into the
skill/MCP harness through [analysis learning](analysis-learning.md). Do not copy
dataset-specific thresholds, object identities, expected masks, scoring answers
or the successful trial transcript into the fresh agent's instructions. Freeze
the new harness before testing it without corrections. Reusing a consulted
development image tests repeatability, not unseen generalization; keep a genuine
untouched reserve for the latter. Final candidate freezing precedes held-out
access, not every unsuccessful development iteration.

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
