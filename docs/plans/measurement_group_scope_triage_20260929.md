# Measurement group-scope compile incident (#204 / PR205)

Owner: Zeno. Classification: invalid authored grouping, not a missing backend
scope projection. This technical triage adds regression evidence to PR205; it
does not close #204's separate paired-channel runtime/live acceptance.

## Actual request provenance

- Frozen installed harness: `main` at `283b21275`, unchanged by this worker.
- Server 5793, job `4f8e1d55-07f0-4bde-9f37-d24c0ea398f9`, terminal failure
  2026-09-29 20:24:35 UTC (16:24:35 in the local log).
- Authorized log:
  `/home/ts/wt/openhcs-h003-uncoached-20260929/output/runtime/xdg-data/openhcs/logs/openhcs_zmq_server_port_5793_1790712796745242.log`.
  Request line 799 records `compile_only=True`, seven steps,
  `pipeline_sha=5fb62ebed47d`, `request_sig=48d0e5ebf4c4`; lines 845–846
  record the terminal compile error, before measurement execution.
- Original technical request source:
  `/home/ts/wt/openhcs-h003-uncoached-20260929/output/trial03/PipelineDocument.py`.
  Its SHA256 is
  `5fb62ebed47d9ed0f11f4499c26a96ac7107e655f47df64c7a51124cdf03f88d`,
  matching the original server request. AST inspection extracted only declaration
  identities and processing scopes, not scientific settings or outputs.
- Global scope declares `GroupBy.CHANNEL` and variable `SITE`. `Cells` is
  explicitly produced under group `"2"`; `MeasureCells` explicitly dispatches
  `measure_object_size_shape` under group `"1"`, selecting exact `"Cells"`
  through the existing `select_object_sets_to_measure` binding.
- The separately saved `trial04/rejected-grouping.PipelineDocument.py` has hash
  `09c3b345c49f...`, matching later job
  `c5005087-f638-4a85-a8fb-abe4149e9df6`, not the original request. Its technical
  compile receipt preserves the same error. It is corroboration, not a substitute
  for the original request identity.

## Owner and projection evidence

`ObjectLabelDrivenPrimaryImageInputPolicy.invocation_domain_inputs` makes the
exact selected labels input the size/shape invocation domain.
`MeasurementArtifactOutputModule.measurement_output_relations` already emits
`GroupLineageSourceRelation(Cells input ref)`; `ObjectMeasurementInputModule`
also emits the object measurement subject. No declaration field is missing.

`ArtifactProducer.has_explicit_invocation_group_ownership` preserves authored
grouped dispatch. `PathPlannerArtifactStage.output_groups_from_declared_relations`
therefore preserves output group `"1"`. The exact labels source has compiled
group `"2"`, so `output_group_scope_sources_by_group` correctly rejects it with:

```text
MeasureCells_4_measurements ... group '1' has no declared group-scope source.
```

The relevant planner, producer, module-contract, module-relation and primary-image
policy files are unchanged from frozen `283b21275`. No backend scope relaxation,
new selector, registry, adapter exemption, or global channel exception is needed.
The separate #204 secondary-input runtime repair remains intact.

## Focused regression and acceptance boundary

`test_real_object_measurement_preserves_selected_labels_group_scope` reconstructs
the real `MeasureObjectSizeShapeModule` public invocation, canonical module
numbering and declaration contract, then runs actual artifact graph extraction,
planner map compilation and `compile_function_pattern`. The tiny synthetic
producer uses the exact `Cells` identity and channel group `"2"`:

- Explicit measurement group `"1"` reproduces the original terminal error.
- Changing only that authored group to `"2"` compiles, preserving the exact label
  input, object subject and output-to-label group-scope mapping.
- A non-dict invocation derives group `"2"` from the declaration-owned labels
  domain. Its exact selector is consumed, not forwarded as a runtime kwarg.

Three cases passed (99 deselected), 1.99 seconds. Combined with the output-policy
review regressions, **23 passed**, 1.87 seconds, after normal main integration
`21c15ad41` over `de23449a4`. All nine OpenHCS/dependency imports resolved into
this worktree using the existing shared venv and recorded submodule src paths.
The resource guard reported 10.2 GiB available RAM and a historical-swap warning;
only lightweight provider-free checks proceeded. No replay, MCP/JVM/GUI startup,
installation change, held-out/reference inspection or author message occurred.

NRA/refactor-audit coverage is focused, not a complete semantic/proof scan:
IDEN-1/7 keeps authored dispatch, selected producer and measurement subject
distinct; BOUND-2 uses the existing typed owners; MEMB-1/2 introduces no roster;
IMPL-4/10 preserves declaration-driven compile rejection before execution.
The three new cases require **zero production edits**. Tests and this receipt
are the only new scope-specific changes. Actual installed paired-channel and GUI
acceptance remains pending the coordinator's serialized validation handoff after
Confucius releases the frozen runtime. No new issue is needed for this authored
contract error; the case is retained on existing #204 / PR205.
