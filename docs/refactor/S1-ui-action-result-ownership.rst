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

This is a DRAFT, not merge-ready. Existing named selected-workflow --wait is a
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

Scientific native slot is currently owned by Schrodinger's frozen neurite task.
No live native/UI test or private install update may compete with it. Parent
continues this source family and serializes affected installed acceptance after
the original scientific handles close. Full ZIP/goal scope remains active.
