# Callable reference lineage checkpoint

Implementation/integration owner: OpenHCS coordinator. Issue254.
Base33ec405e1ec3ca1a11e285f821754715a90b5290; branch
fix/callable-reference-lineage-20260930, persistent isolated worktree.

## Reproducer and ownership

Executing the exact public callable-artifact-reference code and querying the
actual installed CallableContract.group_scope_inputs raises ValueError:
fixture_image is an OUTPUT reference, not a declared INPUT scope owner.
The former ABI/function-pattern tests did not exercise this compiler boundary.

The corrected reference uses existing MainFlowStackOutputSpec for image,
labels and rows. MainFlowArtifactContractProvider binds their scope/stack to
the actual current image input. ObjectMeasurementSubjectRelation still refers
to the exact labels output and row dataclass still owns schema/emptiness.
No compiler guard, output format, runtime implementation or registry changed.
No copied source identity or new subject/group inference is introduced.
This preserves nominal ownership (BOUND-1, IMPL-1): use existing declaration
hooks rather than author a competing lineage mechanism or relax consumers.

The stale registration name/functions-return paragraph now points to the actual
registration capability and canonical workflow, then contract reflection.
Diataxis: repair the existing working reference rather than duplicate a how-to.

## Focused evidence and limits

Shared Python3.12 /home/ts/code/projects/openhcs/.venv/bin/python imports the
FROZEN installed compiler86a99f33c; tests extract the updated worktree document
directly. Source dependencies are not initialized/built in this small tree.
No installation, MCP/JVM/GUI/native scientific execution or source change in
the active run. Canonical compiler semantics are unchanged by source250.

First test attempt:4failed/3passed in4.32s. One knowledge-path assertion compared
the explicit document root with the default installed manifest; the test now
selects its actual manifest through the existing API. One old manager fixture
did not accept the owner-added create=False argument; it now asserts that exact
non-creating lookup. Two new checks incorrectly equated all main-flow artifact
outputs with the first return position; the checks now assert the actual
canonical/trailing ABI separately, retaining exact stack-source assertions.
The original failures are not presented as runtime defects or hidden.

Corrected focused file:7passed in4.41s, including both pipeline-start and
preceding-image owner bindings, direct/empty ABI, real custom namespace,
native CSV/ROI files, and packaged knowledge bytes. No assertions disabled or
deselected. git diff --check passes. This is focused evidence, not a full audit
or installed/live acceptance. Ordinary MCP registration/compile/execute/persisted
artifact acceptance remains pending the serial slot after blind freeze.

Scratch owner coordinator: /home/ts/.cache/agent-scratch/openhcs-callable-reference-20260930,
purpose tiny pytest/cache outputs, no source/session/reference data. Remove after
retaining results. Worktree and committed receipt remain persistent.
