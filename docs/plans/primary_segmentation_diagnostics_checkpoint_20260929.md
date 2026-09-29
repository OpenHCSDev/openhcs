# Primary-segmentation diagnostics (#214)

Implementation owner: Singer. Base audited: `a0263e82a1b3296f34f8c5cdd50ffae5c33ef7dd`.
Worktree: `/home/ts/wt/openhcs-primary-segmentation-diagnostics-20260929`.
Issue: https://github.com/OpenHCSDev/openhcs/issues/214.

## Contract and ownership

The final mask alone cannot locate a loss in threshold support, peak suppression,
watershed or filtering. IPO now captures the actual threshold support before
hole filling and connected components before declumping. It returns exact
maxima-response, maxima and marker arrays from the existing execution, followed
by image projections of the canonical unedited/small-removed label variants.
There is no second segmentation, fixture-capture dependency or biological verdict.

`PrimaryObjectDiagnosticPlanes` owns stage names, order and slot types. The
module's existing cooperative `finalize_artifact_contract_outputs` hook appends
image `QA_CHECKPOINT` sidecars with source-stack and exact object-output relations.
Their names are `<object>__qa_checkpoint__<field>`. Source address, group/plane
coordinates and compiled producer remain owned by the existing artifact path.
The first three ordinary return values are preserved, including ordinary
ArrayBridge main-output dtype handling; seven typed image values follow them.
Direct tuple-unpacking tests are migrated, not supported by an old-return alias.

These are not new object sets, do not alter measurement subjects, do not enter
main flow and use `ON_DEMAND` viewer streaming. Normal runtime artifact persistence
still applies by default. Declumping-disabled and no-foreground executions have
wholly invalid response/seed masks and NaN response pixels: absent evidence is
not represented as a measured zero. Pipeline settings and threshold support
distinguish disabled from empty execution. Diagnostic intensity metadata describes
the stage's pixels, not the acquisition's uint16 scale.

Evidence is bounded to seven planes per IPO plane. Only threshold support and
initial components are snapshotted to protect their pre-transform stage identity.
Executed response/seed arrays and payload variant arrays are referenced, not
rerun or cloned. Source validity is decoded once and shared across stages;
unexecuted stages share one invalid mask. No input or private benchmark was read.

## Actual focused checks

Seven lightweight tests passed in 1.74 seconds, using the prescribed project
Python 3.12 environment, this worktree and all eight recorded submodule source
directories on `PYTHONPATH`, with `OPENHCS_CPU_ONLY=true`, thread limits of one,
`PYTEST_DISABLE_PLUGIN_AUTOLOAD=1` and:

```
python -B -m pytest -q --confcutdir=tests/unit tests/unit/test_primary_object_diagnostics.py
```

Two unrelated pytest async-config warnings remain because plugins are disabled.
Verified import paths are under this worktree and its recorded submodules.
The first test iterations exposed incorrect fixture assumptions about source
spatial-domain construction and the payload's count owner; those fixtures now
use `SourceSpatialDomain` and `objects.domain.declared_object_count` directly.

This is a focused source/AST audit, not a complete NRA scan:

- IMPL-1/2/3/7: actual new diagnostic source has no string/type/kind dispatcher;
  executed and unexecuted evidence own their behavior under an ABC.
- MEMB-1/3: artifact projection reads the typed record's `_fields`; no parallel
  stage roster or handler registry. ABI slot types derive from the same annotations.
- BOUND-1/2/7: no string-key raw record reads, duck-typed fallback access or bypass
  of `ObjectLabelPayload` variant ownership in the new source. One source decode
  precedes all stage projections.
- IDEN-5/6: exact input-source and object-output relations are exercised; projections
  retain coordinates and share the authoritative arrays rather than reconstructing
  filtering evidence or inventing a competing object identity.
- Actual AST comparison against the pinned baseline confirms the segmentation
  body is unchanged except evidence captures and the augmented return.
- The real image-output contextualizer preserves absent-stage masks and numeric
  pixels, provenance and stage intensity semantics.
- New-case experiment: one added nominal record field is picked up by the actual
  artifact projection without a catalog/dispatcher edit. A real new computed
  stage requires its field plus its same-execution producer argument (two sites);
  output names, slot annotation and consumers derive without extra maintenance.

## Remaining acceptance and scheduling

The new worktree cannot yet import IPO because main's newly required native
`_granularity_reconstruct` extension is not built here. No native build, algorithm,
MCP, JVM or GUI has been started. Build the extension only in this worktree
(`python setup.py build_ext --inplace --parallel 1`) after explicit slot handoff.
Do not install or change the running baseline.

`tests/integration/test_primary_segmentation_diagnostics_journey.py` is prepared
but NOT run. It covers real registered IPO on a small synthetic close-pair/faint
field (empty, disabled, intensity and shape declumping), then source-document
roundtrip, normal compiled execution, secondary binding and persisted review
through the existing runtime/filemanager. Native parity, these real journeys,
fresh MCP discovery, persisted MCP result review and isolated-display same-coordinate
raw/intermediate/final viewer inspection remain required. Passing metadata tests
does not prove them or biological QA.

Parent takes the first released slot for #151/#212. Wait for the parent's explicit
handoff, then acquire `/home/ts/wt/openhcs-issue-batch-20260929/validation.lock`
nonblocking, run the resource guard and retain at least 8 GiB RAM. Use a single
worker and owned disposable test output under
`/home/ts/.cache/agent-scratch/openhcs-primary-diagnostics-20260929`, retain receipts,
then clean disposable output. Do not poll the lock or start a GUI without display
allocation.

Core artifact/runtime/adapter files owned by Zeno are unchanged. This bus has no
verified Zeno route, and the parent cannot relay; obtain a direct route before any
shared-file changes or manual adapter-fixture migration. One existing hand-written
IPO executor fixture still declares only the previous two artifact slots; it must
derive the new diagnostics before its native suite is run. Normal compiled contracts
already use the module hook.

Independent draft PR #207 / issue #138 remains at its published polymorphism
checkpoint, with 51 provider-free tests and prior existing-environment lifecycle
evidence. Its authorized bounded fresh bootstrap creation/native validation is
still pending the explicit serialized slot. It is not abandoned or closed.
