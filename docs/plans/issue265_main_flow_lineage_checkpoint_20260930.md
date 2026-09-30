# #265: chained callable lineage binding

Owner: Zeno. Integration/live owner: parent. This is a new follow-up, not a
continuation of closed PR205. Base normally integrated: `bd1ef8d11` (main).
Socrates owns #257/#264, `runtime_image_values`, source projection and
materialization; Lovelace owns R0. None of those implementation files changed.

## Original failure and owning fact

The retained MCP receipt is
`/home/ts/wt/openhcs-issue-batch-20260929/source-live-publication-262-20260930/journey.json`.
Execution `2f15f508-d405-48f1-9ce3-35ae1ae314e1` compiled and completed the first
canonical public `inspect_label_fixture` step, then failed at the second step's
`FunctionCoreExecutor.load_artifact_inputs`: a storage-backed lineage edge had
no callable parameter. Original pipeline/reference/input/outputs remain untouched;
the original job was not replayed. Both original process identities were closed
by the integration owner.

`MainFlowStackOutputSpec.bind_main_flow_source`, through
`MainFlowArtifactContractProvider`, declares exact input-qualified output lineage.
`CallableContract.output_group_scope_sources` derives its group-source identities
from those relations. `PathPlannerArtifactStage.compile_invocation_input_edges`
previously let producer storage turn that current-primary-payload source into an
extra stored callable argument. Storage location and argument role are different
facts. The runtime guard correctly rejected the resulting edge.

The planner now intersects the existing output-relation projection with the
current main-flow identities before selecting input storage. Only that exact
intersection takes the existing unstored source-edge path. Unrelated storage,
including an input that merely appears in the fallback group-scope projection
without an output relation, retains its original authority.

The existing `InvocationArtifactInputEdgePlan` now owns source-edge construction
and the complete-payload versus declared-source-image projection. The planner's
former constructor/projection block is deleted, not retained as a second reader.
Its stage shrinks from 1,439 to 1,430 lines; the edge declaration grows from 55 to
88 lines. No runtime loader, binding guard, source compatibility, kind roster,
registry, adapter switch or selector store changes.

## Focused ownership audit / new case

- **IDEN-1 / IDEN-6:** storage presence no longer answers the primary-lineage
  question. Selection uses `ArtifactSpecRef` intersections from the actual
  declaration owners, not names, filename parsing or artifact-type matching.
- **BOUND-2 / IMPL-4:** source projection uses the existing typed edge owner.
  Complete versus selected-source projection moves with its construction;
  the planner's replacement calls that owner instead of copying its procedure.
- **IDEN-5 / IMPL-5 / IMPL-13:** no second lineage store or loader mechanism;
  the relation view is invocation-local and derived. Existing source-binding
  and exact-storage paths remain distinct capabilities.
- **IMPL-10 / IMPL-14:** neither edge invariants nor the runtime missing-parameter
  guard is weakened. Their old/current methods compare equal by AST. No extra
  anonymous validation chain, concrete type switch or string dispatch is added.

New-case experiment: a chained image producer declaring a
`MainFlowStackOutputSpec` requires **zero** new consumer/registry/loader cases.
Changing its exact input source changes the derived intersection. A source absent
from current main flow, or a stored secondary source not declared by the output
relation, remains storage-backed. Existing
`test_storage_backed_input_keeps_exact_runtime_authority` and
`test_compiled_producer_edge_overrides_matching_source_binding` are preserved,
not rewritten to accept broader main-flow precedence.

## Actual evidence at this source-only checkpoint

Required interpreter:
`/home/ts/code/projects/openhcs/.venv/bin/python`; own worktree and recorded
submodule `src` directories on `PYTHONPATH`. All nine package import locations
were verified inside this worktree. Recorded submodules are initialized.
No package/environment/installed-source changes.

- `git diff --check`: passed.
- Standard-library AST parsing: all four changed Python files passed.
- Execution of the **actual extracted planner assignments and source-edge factory
  body**: eight storage/current-main-flow/declared-relation combinations passed.
  Exactly one case changes from the original storage-first behavior: a stored,
  explicitly declared source present in current main flow.
- Additional actual-source factory case: multiple main-flow identities retain
  `DECLARED_SOURCE_IMAGE`, rather than widening to the complete payload.
- AST equality of `InvocationArtifactInputEdgePlan.__post_init__` and
  `FunctionCoreExecutor.load_artifact_inputs` against integrated main: passed.
- AST caller inventory: one production caller and 26 unit/helper call sites
  identified. Production supplies `step_context.main_flow_artifacts`; no caller
  signatures changed. This is an inventory, not execution of all those callers.
- Existing packaged `agent_comms.debt_ratchet` source at `dbd0965d`, invoked
  read-only with `--root openhcs --base bd1ef8d11 --head 3c4805473`: exit 0.
  It covers seven measure families, including the complete class inventory;
  it predates C0's string-dispatch/type-switch measures at the newly published
  workflow pin. This is not a claim that the full current R0 suite passed.

These are focused source checks, **not** a complete NRA/R1 scan, native proof,
pytest compiler/runtime pass, numerical parity or installed/live acceptance.
Importing the planner for source pytest currently stops at missing own-worktree
`openhcs.core._tabular_native`; no donor binary or installed-source fallback was
used. Parent reviewed `3c4805473` and integrated it into its own current-main plus
PR262 `5c0` tree with native extensions built there. The own-worker missing-native
blocker does not block that integration. Parent owns the finite unit/compiler/
orchestrator then full dotted-source native MCP gate; results await actual
receipts. No native, MCP, JVM, GUI or surviving test handle exists for this worker.

Published draft: <https://github.com/OpenHCSDev/openhcs/pull/267>.
Production/test source checkpoint: `3c4805473`. Later receipt-only updates do
not change the source tested by the focused checks. All worker check/publish
commands are terminal; no slot/lock ownership is retained by this worker.

## Prepared behavioral regressions and remaining acceptance

`test_compiled_source_edges_only_consume_relation_owned_main_flow` now covers
four combinations of stored primary and stored named secondary. The secondary
keeps its exact storage plan/projection/parameter; the declared primary has no
storage-loading edge. Existing exact occurrence, mismatch, ambiguity and source
projection controls stay unchanged.

`tests/integration/test_chained_callable_lineage_journey.py` reuses the canonical
public reference fixture, rather than copying its declaration/callable. It writes
a fresh 8x8 uint16 input, round-trips the complete two-step document, compiles via
the real inspection gateway, checks the second step's producer storage and typed
main-flow edge, then executes the real orchestrator. Assertions cover both exact
step-addressed image/label/measurement records, label subject, 16-pixel rows,
saved CSV/ROI and checkpoint TIFF readback. Publication remains enabled. This
test is **prepared, not yet executed**.

Prepared focused command (not a result):

```sh
/home/ts/code/projects/openhcs/.venv/bin/python -m pytest -q \
  tests/unit/test_path_planner_materialization.py::test_compiled_source_edges_only_consume_relation_owned_main_flow \
  tests/unit/test_invocation_input_source_context_identity.py \
  tests/unit/test_artifact_input_edge_cardinality.py \
  tests/unit/test_function_patterns.py \
  tests/integration/test_chained_callable_lineage_journey.py
```

Run only in the authorized native-built source tree with verified submodule
`PYTHONPATH`, bounded threads, nonblocking validation lock and fresh resource
guard. Parent currently has next-start authority; this worker remains source-only.

The unchanged base lacks Socrates' pending #264 publication repair. A full
publication journey may reach that separate boundary before reaching the new
second-step case. Do not deselect/xfail publication or absorb that implementation;
parent integration will combine the reviewed checkpoints and require exact
filenames, typed addresses and complete saved inventory through fresh MCP.
Installed/live readiness and #265 closure are not claimed at this checkpoint.

## Persisted formats / resources

No persisted format changes. User-authored pipeline source/config, names, TIFF,
CSV and ROI formats are unchanged. Internal compiled edge state is regenerated
on compile; no legacy reader, migration or compatibility alias.

Persistent source: `/home/ts/wt/openhcs-chained-lineage-edge-20260930`.
Owned disposable cache root:
`/home/ts/.cache/agent-scratch/openhcs-chained-lineage-edge-20260930` (Zeno,
future bounded source build/tests only). Retain receipts before cleaning owned
disposable caches after terminal validation. No heavy startup was performed.
