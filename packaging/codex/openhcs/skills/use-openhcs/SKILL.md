---
name: use-openhcs
description: Operate local OpenHCS microscopy workflows through the bundled MCP server. Use when Codex needs to inspect plate data, discover processing functions, author or validate pipelines, compile and execute jobs, control viewers, or interact with a running OpenHCS GUI.
---

# Use OpenHCS

1. Call `openhcs_health_check`, then `openhcs_get_authoring_context(kind="first_use")`
   and the task context it names. For image analysis, `image_analysis_workflow`
   owns the operating contract; do not reconstruct it from remembered tools.
2. Discover the current route through `openhcs_search_capabilities`. Its surface
   profile, workflow and security metadata determine UI-visible versus exposed
   headless operation. Discover the GUI bridge before UI actions and use current
   revision/request tokens. Follow structured errors, not policy bypasses.
3. Inspect acquisition data, channels, calibration and registered function
   declarations before authoring. Reflect non-obvious configuration with
   `openhcs_describe_config_schema`. Submit one complete `PipelineDocument`:
   `pipeline_config` plus ordered `pipeline_steps`, including source bindings.
   Validate and compile that document before execution.

Start read-only, then continue bounded work already authorised by the task.
Do not request permission again for each routine edit, execution or viewer action.
For work outside that scope, follow **Task authorization** in
`openhcs_architecture_quick_start`. Respect configured filesystem roots and
declared confirmations. A timeout is not permission to restart or replay:
observe the original process/job handle and resolve its outcome.

Before a cold function-catalogue search, discover `catalog preparation` and use
[responsive preparation](references/custom-function-authoring.md#register-on-the-intended-process-owner)
on the intended endpoint. Keep cold warming separate from ordinary tool
observation and follow its handle until READY.

## Choose an analysis

Before choosing a segmentation or tracing method, read
[the analysis strategy](references/analysis-strategy.md)
(`openhcs_autonomous_analysis_strategy`). Its task router owns example selection,
conditional learning retrieval, foreground/marker reasoning, parameter evidence
and development versus autonomous-evaluation rules. Follow the relevant routes,
not every reference in the bundle. Infer a provisional approach from acquisition
and distributed raw evidence; ask for missing biological facts only when they
materially change the analysis.

Search the biological task plus `OpenHCS Python` for a compatible Official30
example. Retrieve its exact `openhcs_official30_benchmark_recipes` section with
`max_chars=50000`, inspect the complete pipeline and record its reference/parity
scope as described in the strategy. Benchmark parity does not validate a new
assay. ExampleHuman nuclei tasks also have
`openhcs_official30_examplehuman_nuclei_recipe_card`.

Establish the detector's actual input units and preprocessing contract before
tuning; use [preprocessing choices](references/image-preprocessing.md#establish-detection-inputs-before-tuning)
(`openhcs_image_preprocessing`). Preprocessing can be separate steps or earlier
callables in the same step's function chain. Check embedded operations and their
switches rather than applying them twice or assuming all filters are necessary.

## Inspect results and repair

For image-result QA, load `image_analysis_workflow` and `viewer_review`, then read
[matched viewer review](references/viewer-qa.md) (`openhcs_viewer_qa`). Review
distributed raw-only, result-only and combined views, opening the captured
bitmaps yourself. The procedure owns contrast, axes, canvas changes and witness
selection. A layer listing or capture acknowledgement does not prove rendering
or biological quality.

For misses, false bridges, splits, merges or zero-growth objects, use
[stage-specific diagnostics](references/segmentation-diagnostics.md)
(`openhcs_segmentation_diagnostics`). Inspect the earliest failing intermediate,
make a discriminating change and check distributed regression controls. Preserve
failed candidates; judge the author's final frozen choice, not its first try.
For apparent round-object over-segmentation, discover
`inspect_metaxpress_round_objects` and inspect its labels/measurements at the
same raw coordinates under the canonical image-analysis policy.

Keep execution success, biological usefulness and reproducibility distinct.
Freeze the candidate and acceptance criteria before held-out access; keep
treatment identities and scoring references sealed according to the task's
evaluation protocol. External corrections are assisted development, not fresh
autonomous success. See [biological evidence](references/biological-image-analysis-evidence.md)
for claim scope and [recipe promotion](references/blind-recipe-promotion.md)
before publishing a reusable recipe.

## Other routes

- Unsupported microscope: declare `LazySourceBindingsConfig` in
  `PipelineConfig.source_bindings_config` and consuming steps; never parse
  filenames inside processing functions. For metadata joins or cross-channel
  labels/photometry, retrieve the corresponding `openhcs_image_sources` sections
  before declaring joins or stacks.
- Missing compatible operation: request the `custom_function` context and read
  [custom-function authoring](references/custom-function-authoring.md)
  (`openhcs_custom_function_workflow`). A custom callable joins the ordinary
  typed registry and runtime, not an alternative execution route.
- Transferring repairs or contributing knowledge: read
  [analysis learning](references/analysis-learning.md) (`openhcs_analysis_learning`).
  Do not publish recipes or write personal memory without that authority.
- Package/skill drift or harness setup: read
  [installation and synchronisation](references/installation.md); preserve
  development symlinks and locally modified managed skills.
