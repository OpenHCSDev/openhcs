## Clarified diagnosis — 2026-09-29

The exact selector already exists on the CellProfiler declaration. This is a
catalog discoverability defect, not a missing selector mechanism:

- `MeasureObjectIntensityModule.object_measurement_binding.parameter_name` is
  `None`, but `require_parameter_name()` supplies
  `select_object_sets_to_measure`; the binding is repeated.
- Author `select_object_sets_to_measure=("Cells",)` in the measurement
  `FunctionStep` kwargs, where `Cells` is the exact declared secondary output.
  This compile-time selector is consumed by declaration reconstruction.
- `labels` is the runtime payload parameter, not an authorable selector.
- The agent catalog projected the raw optional `parameter_name`, concealing the
  existing derived selector. Draft [PR205](https://github.com/OpenHCSDev/openhcs/pull/205)
  projects `require_parameter_name()` and explains exact tuple authoring.

Current source verification uses the real `PipelineDocumentAuthority` and
`FunctionStepDocumentAuthority` render/parse routes followed by
`InProcessCompileInspectionGateway.compile`. With primary `Nuclei` and
secondary `Cells` producers, `("Cells",)` survives both roundtrips and the
compiled scalar `labels` edge points only to secondary source step 1. Omitting
selection still fails closed; a one-producer pipeline still compiles.

A complete same-source two-producer run additionally proves that the real
orchestrator measures the grown secondary `Cells` region, not primary `Nuclei`.
The current focused suite passed 80 unit cases and five real headless journey
cases; the paired-channel regression below was explicitly deselected, not fixed.

The paired DNA-channel-1 / actin-channel-2 runtime reproduction exposes a separate
input-scope defect before measurement: the secondary step requests exact
`Nuclei` labels under channel 2's fixed execution scope, while their record
belongs to channel 1. `RuntimeArtifactInput._matches_execution_scope` rejects
that address-matched record. This remains an explicit acceptance blocker; it is
not evidence of a missing selector and is not bypassed with fallback selection.
Zeno now owns that runtime/input change under the explicit scope extension. PR205
reuses the existing secondary input's `InputGroupLineageSourceRelation` and
declaration-derived typed image-set identity policy, not a global channel-ignore
flag or another selector. All 48 lightweight runtime-store regressions pass,
including both adapter consumers and wrong well/site/z/time/producer, missing
relation/source, wrong referenced source, absent site plane, and ambiguity cases.
The full paired headless journey could not acquire Euler's validation lock
(exit 75, no pytest started) and remains pending without deselection. Actual GUI
interaction and installed-stack verification also remain coordinator-owned.

The coordinator's empty/asymmetric scope witness is now covered explicitly.
It reproduced four address-matched input failures when declaration projection
left no shared context keys. The artifact boundary now admits vacuous additional
constraints after exact producer selection; the unrelated plane-identity
compatibility predicate remains unchanged and still rejects empty identities.
All 56 runtime-store cases pass after this correction. Full paired execution
awaits the explicit worker validation-slot handoff after the parent's #151/#212
MCP/installation checkpoint; no first-release race or baseline change will occur.

## Original observed failure and acceptance (preserved)

Original title: Allow typed exact object-label selection for scalar CellProfiler measurement steps

## Problem

An OpenHCS pipeline that produces both primary and secondary object-label
artifacts cannot add a scalar `measure_object_intensity` step to measure the
secondary cells on the actin channel. Compile inspection rejects the step
before execution:

```
Callable 'measure_object_intensity' scalar artifact-fed parameter 'labels' has multiple exact artifact occurrences (IdentifyPrimaryObjects_1_object_labels_1, IdentifySecondaryObjects_2_object_labels_1).
```

The ambiguity is correctly rejected, but the public PipelineDocument / UI
code-document route must expose a typed way to select the intended exact
producer for that scalar `labels` input. Supplying `labels` as a function kwarg
is not valid because it is runtime-owned; the UI code-document roundtrip also
removed such a kwarg in the observed H003 diagnostic. This is not a request
to guess the newest artifact or silently pick one.

## Minimal reproducer

1. In one complete PipelineDocument, step 0 calls
   `identify_primary_objects` on a DNA plane and emits primary labels.
2. Step 1 calls `identify_secondary_objects` on a paired actin plane and
   consumes those primary labels, emitting secondary labels.
3. Step 2 calls `measure_object_intensity` on the actin plane to measure the
   secondary cells.
4. Compile or call `openhcs_inspect_pipeline_source_artifact_plan`.

The current result is the multiple-exact-occurrences error above. The two
source planes may be tiny synthetic arrays; no biological input is needed to
reproduce this declaration boundary.

## Acceptance

- A declaration-owned typed selector identifies the exact secondary-label
  producer for the scalar `labels` parameter, through the headless and UI
  code-document routes; roundtrip preserves it.
- Compile plan shows one exact secondary-label artifact input for the
  measurement step, and a focused synthetic run measures the secondary
  objects rather than primary objects.
- An omitted selector when both are available still fails closed with a
  useful ambiguity diagnostic; existing unambiguous pipelines still compile.
- Tests cover compile, code-document roundtrip, and runtime binding without
  parallel registries, string-name heuristics, or silent fallback.

Owner: OpenHCS blind-analysis coordinator; continue in an isolated worktree,
keeping the current H003 blind worker independent of prior trial findings.
