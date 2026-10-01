Issue360: declaration-owned compile-selector authoring
======================================================

Owner: Dewey/Codex authoring sidecar. PR365 reviewed head
6f18daea291de61ceb22b3d347d65e264e1eee9b stays frozen for parent-installed
acceptance. Independent follow-up worktree:
/home/ts/wt/openhcs-authoring-compile-selectors-360-20261001.
This branch is stacked on that exact checkpoint, not a competing decoder/source
implementation. No other owner's tree, installed environment or mutation is used.

Follow-up draft: https://github.com/OpenHCSDev/openhcs/pull/367.
Qualified production source: 9a0dfc9a5d3c2ce945bc0d232a31f887dd8dec90.
Subsequent delivery changes are evidence/docs only.

Original witnesses and relation
-------------------------------

Parent's installed transcript under openhcs-issue-batch-20260929/
paired350-installed-20261001 remains unchanged. Advertised declaration selectors
were rejected by signature-only validate/render admission. Named FITC(red),
DAPI(blue) compile in FITC,DAPI order, not source-binding DAPI,FITC order.
Omitting numeric channel kwargs failed exact module-block reconstruction.
Original explicit red1/blue0 choices produced swapped observed pixels; they
remain explicit user choices, not something this patch silently rewrites.

The ten initial focused checks on the original frozen production source record
6 failures / 4 passes, 4.05s / 302.12MiB. The six failures include both source
render modes, selector-only reconstruction, another actual module, and a new
declaration. Original failures are retained, not replaced by subsequent passes.

Required relation: compile-only selectors are admitted only by the same nominal
declaration that consumes them. Ordinary signature arguments still bind to the
actual signature. Unknown names, injected image/label/context payloads and
ambiguous ownership remain rejected. Omitted authoring defaults derive from
the declaration's existing setting projection; explicit choices remain intact.

Owning implementation and review
--------------------------------

IMPL-4/IMPL-13: extend the original InvocationContractProviderFactory and
PipelineInvocationContractProviderAuthority, whose original auto-registered
declarations already own compile-only consumption. The existing CellProfiler
provider uses exact canonical CellProfilerModule ownership, not a consumer
CellProfiler/GrayToColor/type/name switch. No new registry, cache or DTO schema.

MEMB-1/BOUND-2: CellProfilerModuleSettings, an existing capability ancestor in
CellProfilerModule's real MI, derives parameter admission from original setting
bindings and the canonical callable ABI. Its shared normalization algorithm
constructs the original ModuleBlock using original binding record emitters;
concrete declarations supply only the default hook. Runtime parameter exclusion
still uses the original CallableContract and parameter documentation policy.

IMPL-12: the existing CompositeInvocationContractProvider owns single-claim
admission for both compile and authoring projections. Its previous inline
claim validation is removed in place, not copied into a new authoring facade.
The provider's zero/one/multiple-claim behavior remains the same.

TIME-7: GrayToColor's small cooperative default hook reuses its existing
_gray_to_color_kwargs setting/channel projection and SettingsBinder. No copied
channel algorithm, default table or hand-maintained selector list. Its original
module reconstruction hook now recognizes named inputs and marks omitted
inactive roles explicitly. Existing ordinary three-input inference is retained.
No numerical operation, runtime executor, provenance or scientific engine edit.

New-case evidence
-----------------

The focused suite includes CorrectIlluminationApply, RGB and CMYK declarations,
real label injection rejection, explicit numeric choices and output-name-only
default preservation. A new module declaration inherits the existing settings
capability and composes an independent ExtraOutputSettings capability through
real MI. Both selector membership and a cooperative super() default hook flow
through its declared MRO without any generic consumer edit. Duplicate provider
authoring claims fail closed through the same original owner as compiler claims.
Actual authoring -> validate -> clean/full render -> parse -> exact numbered
module reconstruction -> callable ABI and compile-only kwarg consumption are
checked without executing the numerical function.

Qualification boundary
-----------------------

Complete decoder/source/formatter/authoring suite: 53 passed,
7.41s / 396.36MiB. Fourteen are new compile-selector/default cases, with
no deselection. Adjacent activation/cardinality declarations: all19 passed,
4.32s / 300.37MiB, including unchanged plain three-image RGB inference.
Original PINNED R0 on six changed production paths against frozen PR365:
PASS, 16.83s / 82.68MiB, 5188 measures, increased[]. The original tool runs
under actual Python3.14 with read-only metaclass backing; no detector copy.
Ruff F/I and git diff checks pass.

The full adjacent invocation-provider suite is NOT passing: 25 pass and
test_classification_rules_remain_public_while_declaring_prior_measurements
fails measurement-subject validation. Together with the fourteen new cases,
the retained receipt reports 39 passed / 1 failed, 7.54s / 387.90MiB.
The exact same original test fails against frozen PR365 production source:
25 passed / 1 failed, 6.80s / 383.46MiB. Its source is unchanged, and no
assertion is removed or waived. Out-of-scope interface:
ClassifyObjectsSingleMeasurementModule measurement output declarations ->
MeasurementsArtifactType.require_output_subject in compile_function_pattern.
Named handoff: parent/release scientific declaration owner for disposition;
this sidecar does not modify classification, artifacts or the scientific test.

Source checks only: CPU0, combined command RSS512MiB, wall60s, thread pools1,
read-only parent interpreter/dependencies and explicit own Python source.
Subprocess launches are forbidden by the focused fixture. The read-only native
tabular extension is imported only to satisfy existing contracts; no native
execution, UI/MCP/science process, installation, download or heavy lock.
Receipts are persistent under this worktree's validation directory.

Parent controls fresh installed acceptance after the blind slot terminates.
This source proof does not establish native rendered-pipeline execution or pixel
correctness. Engineering selector-only source outside the authoring service
gets exact block reconstruction but no new runtime kwarg injection: runtime
execution defaults/ABI are unchanged. Explicit red1/blue0 remains red1/blue0.
Original AUTO/PREPARED_WORKSPACE provenance rejection is correct and unchanged.
Global85 NRA FULL remains unqualified; no full heavyweight gate is run here.
