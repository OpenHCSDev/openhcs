Explicit source-projection fixture ownership
============================================

Issue294; parent OpenHCS coordinator owns implementation/integration.
Base main4eded35fe, source correctiond9bcaf50c, isolated persistent worktree
``/home/ts/wt/openhcs-source-projection-fixtures-20260930``. Production, public
formats, dependency pins and the installed blind harness are unchanged.

The unchanged-main PR291 evidence already records the original two failures:
``benchmark/results/perf_runtime_producer_path_index_20260930/validation/``
``perf-runtime-context-independent-main-baseline-failures-20260930.log``.
Fresh source counterexample gives the SAME two failures:2 failed/2.64s tests,
3.15s process/189840KiB RSS/exit1. Original before.log/XML remain in the durable
parent ledger ``/home/ts/wt/openhcs-issue-batch-20260929/``
``source-projection-fixtures-20260930/``. No source inference was added to pass.

The bundle fixture previously expected extension consensus without declaring
an extension on either input plane. It now tests absent, TIFF and PNG metadata
with unchanged TIFF source paths. Each case asserts exact original source paths,
every per-plane component and exact common-component metadata. The absence
case forbids filename-derived invention; the PNG case proves the declaration
rather than the filename owns this field. No assertion was removed or loosened.

The ordered-source measurement fixture now supplies the existing
ArtifactMeasurementSubjectRelation to its aggregate output. Original ordered
group-filter assertions are unchanged; group-lineage inputs remain intact.
Existing output-ownership checks still reject missing subjects under both
native and adapter-recorded policies, reject conflicting subjects, and preserve
the CellProfiler provider's distinct recording contract. BOUND-2: original
provenance and measurement declarations own semantics; no mirrored default,
filename parser, registry, compatibility route or compiler weakening.

Full relevant check executes the actual source owners, including real synthetic
plate initialization/compilation and the native tabular extension:

* tests/unit/test_function_runtime_source_projection.py
* tests/unit/test_function_patterns.py
* tests/unit/test_artifact_output_ownership.py

**181 passed**, zero skips/deselections,10.88s tests/12.08s process,
412516KiB peak RSS/exit0 under the original30s bound. Two warnings are disabled
asyncio plugin settings. initialized.log/XML retain source/import and metadata
owner receipts. Source native extensions built from existing declarations:
3.55s/147248KiB/exit0; no package installation or download.

Parent harness's earlier wider command had179 passes/2 OTHER failures because
``--noconftest`` skipped application bootstrap, letting PolyStore's metadata
owner initialize before OpenHCS configured its filename. That original
after.log/XML is preserved separately, not credited as green. Corrected launcher
imports OpenHCS FIRST then calls pytest.main; no hard-coded metadata override.
It asserts actual OpenHCS source and native2c68 source paths before the suite.
Explicit source root plus existing installed dependencies, existing Python3.12,
thread limits1, isolated persistent XDG/pytest scratch, shared Fiji bundle root
and downloadfalse. This does not certify all submodule source builds or global
NRA/refactor completion. Production diff is empty, so no production ratchet
rerun is needed for these test-only edits.

No GUI/MCP/native endpoint, JVM, paid provider, biological/held-out data or blind
candidate allocation; the current Erdos freeze/deadline/harness is unchanged.
The affected check entrypoint passed. No product activation or biological
accuracy claim is made, and no optional hosted-CI waiting gate is introduced.
Original failures and generated native binaries are retained; disposable build
and test scratch can be retired only after terminal handles/empty lsof checks.
