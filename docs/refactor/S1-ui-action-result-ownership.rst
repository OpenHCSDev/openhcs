S1 UI action result ownership checkpoint
=======================================

Owner parent integration. Base remote main094425c8c81324da7a3878379074e1bd8234ff52.
Tracking issue: https://github.com/OpenHCSDev/openhcs/issues/348.
Isolated branch fix/typed-ui-workflow-rendering-20261001 under /home/ts/wt.
No blind-trial source/package/skill change or UI mutation. Original installed
reproducer fails in3.71seconds/237.86MiB: CLI exit0, status/receipt/targets none
despite UiSelectedPlateWorkflowResult.action_result accepting scope engineering.

BOUND-2: UiActionInvokeRenderer read top-level widget/action/status fields while
UiActionInvokeResult owns nested identity. The selected-workflow command fed
its richer wrapper into that unrelated raw reader and copied workflow arguments
as pretend action identity. IMPL-4/12/13: existing typed renderer ingress was
bypassed, and generic call serialized/re-read the same authoritative receipt.

Target: shared owning UiActionResultRenderer ABC algorithm with real typed
result projection hooks. Direct action and selected workflow are sibling
presentation members, not sibling DTO subtyping. Existing AutoRegisterMeta
derives membership; existing codec descends the real DTO exactly once. No new
DTO/registry, consumer name/type switch or field mirror. Cooperative hooks
permit independent capabilities. Deleted old raw invocation reader and selected
call override; workflow-control readers consume the same decoded action.
No stored format, scientific algorithm or UI dispatch contract changes.

Current evidence and limits
---------------------------

Same real CLI reproduction passes against this source4.76seconds/241.71MiB,
oneCPU/512MiB/60seconds. Actual source path is this worktree. First source attempt
failed before import because unbuilt _tabular_native was absent; failure retained.
Source checks reuse copies of the two exact current-installed abi3 extensions
in this own worktree, not a build/download or backing-environment change. Source
and installed MCP readiness remain distinct. New provider-free tests exercise
actual CLI retained identity and independent capability MI in both MRO orders.
New family checks3PASS in4.86seconds/243.87MiB. First shard1PASS/2FAIL because
the new fixture passed positional arguments to keyword-only UiActionIdentity;
corrected the fixture without changing production or weakening an assertion.
Both original failures and corrected output retained. Optional pytest plugin
configuration warnings are not hidden. No source tests stand in for live UI QA.

Historical failing checkpoint: existing named selected-workflow --wait is a
distinct composite presentation. Its current raw summary/state projection is
not closed by the new primary-action binding. Need preserve/migrate that real
production poll path and prove its existing behavioral controls before merge;
do not silently replace it with the first primary-tool result. All new tests,
rejection/malformed/JSON/external-receipt controls, original R0 and R1 evidence,
and an installed actual affected entrypoint gate remain to be completed.
Full R1/global ownership is unqualified, not zero debt. No compatibility
facade, permissive decode or error suppression is allowed to hide this gap.
Existing compact poll control actually FAILS7.41seconds/295.82MiB: retained
batch production rendering no longer matches the distinct composite summary.
Its fixture also omits required action DTO fields; restore a full nominal
fixture without weakening any summary/row expectations, then fix the real
composite owner rather than adding serialization or raw decode fallbacks.

Typed poll migration checkpoint
-------------------------------

Deleted the partial poll-summary reader, raw result/first-payload descent,
duplicate workflow error traversal and text quoting helpers. The original
WorkflowPollSummary now remains the producer-owned result until the explicit
JSON output boundary; its original encoder owns that projection. No synthetic
MCP capability or parallel schema registry is introduced. SelectedWorkflowCommandSpec
composes TypedCompositeCommandSpec and CapabilityBackedCommandSpec through MI.
The shared composite ancestor delegates JSON framing to the original ancestor
without recursively dispatching the typed compact hook on a serialized record.

The selected workflow's dynamic state document descends once into the existing
UiPlateManagerState. Its rows are UiPlateManagerRowState, not partial records or
a second schema. Missing required row facts fail closed. Other UI state-surface
renderers/controllers remain unmigrated S1 work; this is not global S1 closure.
The internal summary and action schemas are not advertised as new public formats.

Real CLI/controller/codec source checks, with only the MCP wire controlled,
cover dispatch, operation receipt, state polling, terminal row presentation,
compact output without serialization, JSON output, malformed receipt/nonzero
exit and original invalid-wire preservation. Existing stale-terminal, missing/
failed receipt, transient timeout, rejection and failure controls retain their
assertions. Full native fixtures replace incomplete hand-written records; no
permissive decoder was added. Independent MI capability hooks are checked in
both base orders, including the actual declaration-derived renderer binding.

The focused family passed30 checks in8.81seconds/276.48MiB before adding the
declared-state negative. A broader one-process CLI run stopped at the unchanged
512MiB limit (514.24MiB observed,22.48seconds); it is not a passing run. Its
first failing direct-action fixture omitted native schema/identity and framing.
Those facts were restored without weakening receipt/poll/error assertions.
The full CLI family is now split by exact test-node identity in50-function
shards, not by omitting cases or increasing limits. Shards0/1 pass50 checks each;
shard2 passes64 including all new action/MI/CLI/declared-state-negative checks.
Their respective peak RSS is280.80/283.63/284.58MiB, each under11seconds.
Final non-live shard passes36 checks in8.74seconds/290.17MiB. The four shards
total200 passing checks, including every CLI case except the separately assigned
real MCP startup test. That test's combined pytest/child process crossed512MiB;
the original full/final-shard failures remain retained and it is not waived or
claimed passing. Real installed MCP startup/affected UI acceptance is still due.

Original pinned R0 entrypoint on production b6cdef197 versus main094425c8 passes
in17.66seconds/83.68MiB, Python3.14, allfour changed production paths. It reports
5175 metric projections, all deltas zero; these include full class inventory and
are not5175 NRA detectors. No copied measures, exceptions or consumer registry.
Global/full R1 and installed actual UI acceptance remain incomplete. All original
failed commands and corrected checks remain in owned receipts.

Schrodinger's original scientific trial is now terminal technical abstention,
with zero scientific admissions. Original processes and listeners exited and
the serialized native slot is independently verified released. Issue350 owns
the separate channel-domain/provenance engineering repair; its worktree never
changes this command/action family or the frozen trial. Parent owns PR349 source
and release/live acceptance. This PR remains DRAFT, not merged/installed/live
verified. No hosted CI wait. Full expanded ZIP/goal scope remains ACTIVE.

Installed widget-tree regression354
-----------------------------------

The first private wheel passed all785 OpenHCS member-byte checks and its real
installed MCP health check. Live GUI inspection then exposed a retained-result
CLI regression: WidgetTreeCommandSpec owns --output outline/json, but the shared
CapabilityBackedCommandSpec path directly assumed args.json. The read-only tool
returned before presentation raised AttributeError and terminated the shell.
Earlier source tests called render_response instead of the actual CLI chain.
Issue354 records the original failure; no scientific analysis was dispatched.

The existing McpDevCommandSpec ancestor now owns requests_json_output, queried
by both retained and serialized command paths. WidgetTreeCommandSpec supplies
its small hook using its existing WidgetTreeOutputFormat declaration. There is
no second json flag, getattr/default, consumer type/name switch or renderer copy
(IMPL-4/IMPL-5 closure). Original options and JSON alias remain unchanged.
Real CLI/codec regression covers default outline, explicit outline, explicit
JSON, JSON alias and generic call. Only MCP wire is controlled; the original
typed window/tree DTO and renderer are used. The initial new tests incorrectly
expected an invented outline header; that3-failure receipt is retained. Corrected
tests supply the native window summary and assert its actual title and no-tree
presentation, not merely absence of an exception.12 family checks now pass.

All existing non-live CLI checks were re-run in the original four exact-node
shards:50+50+69+36=205 checks. No input or failure case was omitted; the separately
assigned real MCP startup check and actual affected UI workflow remain due.
The first GUI seed also failed typed Path validation; that setup failure and
foreign-version refusal are retained in gui-seed-rejected.log. The corrected
isolated GUI started own5993/6993, but its cold connect failed while preparation
was active; final native process absence is verified, not inferred from timeout.
This is a separate native startup boundary, not proof that349 is ready to merge.
The frozen blind trial and original backing installation remain unchanged.

Latest installed checkpoint supersedes pending live status above:
``S1-ui-action-result-installed-20261001.rst``. It records actual affected GUI/MCP
acceptance, original R0/census/overlay, retained incomplete R1 and named independent
follow-through. Historical failures above remain evidence, not current status.
