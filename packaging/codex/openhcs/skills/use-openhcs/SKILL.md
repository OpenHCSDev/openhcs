---
name: use-openhcs
description: Operate local OpenHCS microscopy workflows through the bundled MCP server. Use when Codex needs to inspect plate data, discover processing functions, author or validate pipelines, compile and execute jobs, control viewers, or interact with a running OpenHCS GUI.
---

# Use OpenHCS

1. Call `openhcs_health_check` before relying on other tools. Report a bootstrap or stale-server failure instead of working around it.
2. Call `openhcs_get_authoring_context` with `kind="first_use"` when choosing or resuming an OpenHCS workflow, then request exactly the task context it names. For multisite assembly, registration, normalisation, segmentation review, or image-result QC, `kind="image_analysis_workflow"` is the canonical operating guide; follow it rather than reconstructing those rules from this skill.
3. Treat Python pipeline source as one complete `PipelineDocument`: `pipeline_config` plus ordered `pipeline_steps`. Never send a steps-only fragment, mirror configuration through a second argument, or strip source bindings from the reviewed document. UI-visible and headless routes use these same declarations even though their process and state owners differ.
4. Call `openhcs_search_capabilities` with task-relevant workflow, target, or text filters. Its current `surface_profile`, registry-owned workflow metadata, side effects, and security metadata—not a remembered tool list—decide whether to use a UI-visible or exposed headless route. Use `openhcs_list_capabilities` only when the complete selected surface is required.
   Before the first cold local function-catalogue search, discover `catalog preparation` capabilities and follow the existing [responsive preparation procedure](references/custom-function-authoring.md#register-on-the-intended-process-owner) (`openhcs_custom_function_workflow`) on the intended existing endpoint. Observe its exact handle until READY; keep cold warming separate from ordinary 10-second tool observations. A timeout is not permission to restart or replay.
5. Use validated OpenHCS/CellProfiler benchmark examples as working contracts, especially the first-class Official30 corpus. Search the biological task plus `OpenHCS Python`, retrieve the exact `openhcs_official30_benchmark_recipes` section with `max_chars=50000`, and inspect its native reference, pipeline, input/channel assumptions, settings, and case-specific parity evidence. Benchmark parity is meaningful validation for that reference scope; it is not biological raw/overlay acceptance for a different assay. Record the example source and evidence tier before adapting it. CellProfiler image, object, measurement, relationship, and export semantics lower into the same OpenHCS declarations and runtime.
   For a compact, structured example of those fields, retrieve `openhcs_official30_examplehuman_nuclei_recipe_card` when the task involves ExampleHuman-style nuclei segmentation; its selected-value parity and unassessed new-assay QA are deliberately separate.
   When the task is unfamiliar or raw morphology conflicts with an example, follow [pre-first-authorship learning retrieval](references/analysis-learning.md#retrieve-before-first-authorship-and-retries) (`openhcs_analysis_learning`) before choosing its method. Retrieve an applicable conditional lesson through existing knowledge search; benchmark defaults alone do not resolve contradictory raw evidence.
   Before authoring, retain the example-selection record described in [the autonomous analysis strategy](references/analysis-strategy.md) (`openhcs_autonomous_analysis_strategy`); reading this instruction is not evidence of retrieving a pipeline. Preserve failed checkpoints and continue authorised development; apply that guide's distinction between self-directed repair and external assistance, judging autonomous quality on the final frozen result rather than the first candidate. For an unfamiliar assay or an unresolved biological failure, use that guide's task-specific routes to image interpretation, preprocessing, segmentation diagnostics, measurements and recipe/error learning. Retrieve only the relevant guide; infer a provisional strategy from acquisition and matched raw channels before asking the user for missing information. These guides adapt Agentic-J's domain knowledge, not its Fiji command strings or model defaults.
6. Inspect real plate data and registered function declarations before authoring. If the microscope is unsupported, set `PipelineConfig.source_bindings_config` with `LazySourceBindingsConfig` from `openhcs.core.config` to filter files, extract metadata, name semantic sources, and project a virtual workspace; make each consuming `FunctionStep` select those aliases through its step-local source bindings. Never parse filenames inside processing functions. Reflect `global` or `pipeline` configuration with `openhcs_describe_config_schema` before setting non-obvious fields. Keep filesystem operations inside configured read and write roots.
   When importing an external metadata table, retrieve `openhcs_image_sources#joining-an-external-metadata-table` before declaring its join keys; plane-specific metadata and logical source-set metadata have different scopes.
   Before multi-channel photometry or consuming labels produced on another channel, retrieve `openhcs_image_sources#plan-image-stacks-and-source-bound-labels-before-authoring`; image-stack assembly and typed label input context are separate declarations.
7. Validate and compile before execution. Do not infer that source code, UI state, or an earlier validation result implies a current compiled plan.
8. Start read-only. Continue routine bounded work within existing task authorisation without asking again for each edit, execution or viewer action. Follow **Task authorization** in `openhcs_architecture_quick_start` for actions outside that authority; capability-registry metadata, path policy, declared confirmations and fresh revision/request tokens still apply.
9. Preserve the active ownership route. Discover the GUI bridge before UI tools and apply code/state changes with current tokens. Use headless tools only when their workflow group is exposed. Treat structured errors and recovery hints as authoritative; never bypass path policy, stale-process checks, compile requirements, or bridge authentication.

If registry discovery finds no contract-compatible operation, request the
`custom_function` authoring context and read
[how to add a missing analysis operation](references/custom-function-authoring.md)
(`openhcs_custom_function_workflow`). A custom callable becomes an ordinary
typed registry function, not an alternative pipeline or viewer execution route.

## Image-analysis QA

For segmentation, neurite tracing, faint structures, or a report that an overlay
looks wrong, load both `image_analysis_workflow` and `viewer_review` before
tuning or judging the result, and read [the matched viewer-review procedure](references/viewer-qa.md)
(`openhcs_viewer_qa`). Inventory the physical source's channels yourself;
inspect matched raw channels across positions, scales and numeric contrast
windows. Capture raw-only, result-only and combined views through MCP and open
the bitmaps yourself. Re-read viewer state and recapture if the user changed
the canvas, camera, axes or presentation. Log the witness, a clear positive,
a plausible miss/ambiguity and your explicit decision before widening the run
or reporting counts. Use the live contexts' typed evidence contracts and the
procedure's capture details, not a previous conversation or separate assay
skill. Follow the earliest failed stage through one bounded diagnostic and
recheck a regression control.
Before the FIRST segmentation method/parameter proposal, follow
[the task router](references/analysis-strategy.md#match-the-strategy-to-the-failure)
(`openhcs_autonomous_analysis_strategy`): connect
[foreground/nuisance admission](references/segmentation-diagnostics.md#compare-body-admission-models)
(`openhcs_segmentation_diagnostics`) AND
[the chosen marker landscape](references/measurement-interpretation.md#choose-the-marker-landscape-before-the-first-candidate)
(`openhcs_measurement_interpretation`), where those stages apply. Do not stop at
body admission or wait for a split to retrieve marker reasoning. Use the
[empirical measurement procedure](references/measurement-interpretation.md#measure-feature-scales-before-choosing-parameters)
to relate distributed positives and nuisance-only controls to the actual consumed
alias/response and its units, including
[available whole no-object fields before widening](references/measurement-interpretation.md#include-no-object-fields-before-widening),
and within-body maxima versus a genuine pair to
the proposed landscape. Keep method/parameter rationale in the trial, not a
borrowed default justified only by raw diameter.
When an image defect motivates analytical preprocessing, read
[the preprocessing decision guide](references/image-preprocessing.md), also
retrievable as `openhcs_image_preprocessing`, before changing the pipeline.
For extended-object point counts, false splits, merged neighbours, zero-growth cytoplasm
or disconnected neurites, use [stage-specific segmentation diagnostics](references/segmentation-diagnostics.md)
(`openhcs_segmentation_diagnostics`) to choose one discriminating trial rather
than retuning the entire chain. Preserve raw and processed routes for comparison.
Read [the source-grounded evidence reference](references/biological-image-analysis-evidence.md),
or search knowledge for `biological image analysis evidence raw overlay` and
retrieve the same `openhcs_biological_image_analysis_evidence` source when
interpreting a segmentation, intensity measurement, or recipe-transfer claim. Its cited
scientific sources inform the review; live OpenHCS function contracts and the
current assay's raw pixels remain the operational evidence.
Before calling a tested pipeline a reusable recipe, follow
[the blinded recipe promotion guide](references/blind-recipe-promotion.md).
Treat compile/run success as technical evidence only; keep the held-out reserve
sealed until the candidate, parameters, and biological acceptance criteria are
frozen. The guide's metadata audit is read-only and cannot prove biological
validity or enforce blinding by itself.
For transferring a repair or contributing reusable knowledge, read
[analysis recipe and failure learning](references/analysis-learning.md)
(`openhcs_analysis_learning`). Keep failed-predecessor and rerun evidence distinct
from biological acceptance; do not write personal memory or publish a recipe
without the authority for that action.

For apparent round-object over-segmentation, discover the registered
`inspect_metaxpress_round_objects` function and inspect its typed labels and
measurements at the same raw coordinates. Interpret them by the canonical
`image_analysis_workflow` policy; do not invent a second segmentation or a
viewer-only diagnosis.

For package/skill version drift or harness installation, read
[skill installation and synchronisation](references/installation.md).
The package carries the full skill; `openhcs skills sync --skills-dir PATH`
updates only unmodified managed copies and never replaces development symlinks.
