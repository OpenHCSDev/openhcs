S1: MCP development-client result ownership
===========================================

Source owner: Codex S1. Integration owner: parent. Audited canonical main:
e690c3bfc0f2042dcc2c75e6205d03fffe8aa603. Branch:
refactor/mcp-result-owners-s1-20261001. Worktree:
/home/ts/wt/openhcs-mcp-result-owners-s1-20261001.

Binding instructions read completely before decisions: S1-DISPATCH-20261001.rst,
GOAL-SCOPE-REFRACTOR-20260930.md, canonical 00-RULES.md and 01-INDEX.md,
OWNER-OVERRIDES.md, both NRA/refactor-audit SKILL.md files, the authoritative
NRA skills/refactor-audit.skill archive SKILL.md, patterns README, complete
boundaries, implementation, membership, identity and over-time patterns,
surface-receipt instructions and NRA batching instructions.

Before-source measurement and antipattern review
------------------------------------------------

Original debt_census.py, existing Python 3.14.7, snapshot at the audited head:
8 renderer modules, 6068 code lines; literal_key_get 166.61/1000 (1011 reads),
isinstance_call 20.60/1000 (125), none_identity 27.03/1000 (164).
pipeline.py has 502 code lines and weighted debt 100. Snapshot, not a zero diff.

Explicit antipattern review confirmed from current source:

* BOUND-2: pipeline.py:207 declares ArtifactPlanInspection, while :216-241
  read its fields as raw keys and :247-289 read SourceWorkspaceSummary and
  SourceWorkspaceFileRecord as raw records. execution.py DTO declarations own
  these fields, including nested materialization and streaming owners.
* BOUND-1/IMPL-12/IMPL-13: draft :27-43 and execution :534-543 repeatedly
  project tool envelopes through raw helpers; field validation differs among
  nested_mapping, optional_bool/int and sequence_of_mappings. The existing
  python_introspect/dataclass_projection.py codec already performs recursive
  annotation-owned reconstruction and strict rejection. Reuse it, not copies.
* MEMB-1/2/4: dev_client_rendering.py:129-209 and capability declarations own
  renderer/output membership through AutoRegisterMeta and render_bindings.
  Extend that owner; do not introduce a decoder catalog or name/type switches.
* MEMB-5/TIME-9: McpDevToolResult and McpDevToolBatchResponse already own framing
  at dev_client_core.py:393 and :670. No replacement envelope or DTO facade.
  Their single payload sequence must carry decoded values, not a parallel store.
* IDEN-1/3/5: absent tool, missing payload, malformed contract and agent failure
  are distinct observations. Keep transport/agent diagnostics and original
  malformed receipt, not an empty successful record. No duplicated payload cache.
* IMPL-14: strict field validation belongs in the existing generic codec, not
  new anonymous field/key conditions in renderers. Errors identify their path.
* BOUND-4: draft repair guidance currently parses a human missing-kwargs message
  (:156-192). Preserve current user guidance; do not claim it is structured proof.

Producer/consumer trace and required relation
---------------------------------------------

Stdio/socket JSON RPC request -> _content_payloads (structuredContent or MCP
text content) -> McpDevToolResult.from_payload -> command run_session -> batch ->
compact command rendering / external JSON serialization. Native source producer
DTOs -> to_jsonable -> MCP content are unchanged. Existing capability output
declarations select the renderer binding; that binding owns payload reconstruction
through the existing codec. Typed renderer members read actual DTO fields.

ExecutionJobRecord.status at execution_session_service.py:537-558 returns the
existing richer ExecutionJobStatus. _submit_job at :1210-1265 returns
ExecutionJobRef or ExecutionJobStatus (wait and submission failure), despite
capabilities.py:2712/:2743 advertising only ExecutionJobRef. S1 owns a reproducer
and full-receipt decoding for this source presentation mismatch. The implemented
ExecutionSubmissionResult union belongs to the existing execution declaration;
AgentResultFamilyContract extends existing capability output declarations with
that actual family and keeps the original advertised ExecutionJobRef metadata.
No presentation-only alternatives or replacement submission DTO. Native producer
bytes and advertised metadata remain unchanged. Both real siblings render through
ExecutionJobRenderer's ExecutionJobIdentity-owned common procedure.

Initial coherent checkpoint
----------------------------

Migrate pipeline draft, validation, rendered source, artifact plan and execution
as one command family. Extend existing renderer binding and framing owners;
preserve one JSON serialization path. Delete this family's old raw projections,
per-field checks and nested record readers in place. Real command consumers use
the same decoded values as ingress; serialized command input is decoded at its
boundary, not via an old reader. Diagnostics retain full receipts; compact
display limits do not modify the stored result. Genuine JSON extension metadata
and native execution response bags remain mappings.

No stored format changes, migrations, numeric processing or scientific artifacts.
MCP text/structured content and existing native DTO serialization remain external
and unchanged. No package, configured-skill or managed-blind instruction changes.

New-case decisions
------------------

Before: a new nested source/plan fact requires a DTO declaration plus another
raw reader and validation at each consumer. After: fields decode from their true
owner; a renderer adds presentation only. A new capability returning a registered
output contract needs no decoder or caller change. Test that extension through
AutoRegisterMeta. Compose MI only for demonstrated overlapping capabilities;
there is no evidence requiring new MI in the initial pipeline family.

Current source checkpoint
-------------------------

Parent's three concrete pre-checkpoint ownership risks were reviewed against
source, not treated as a completed parent review. The presentation-only Status
retry binding was deleted; producer union membership is now the capability fact.
Status no longer inherits the Ref renderer. Both share the actual identity owner.
has_errors/agent_error_codes no longer convert typed results to JSON and rescan
raw records: one declaration-driven diagnostic traversal handles typed AgentError
identity, typed dataclass fields and genuine external JSON extension metadata.
Malformed ingress retains one original receipt with typed boundary diagnoses.

Deleted mechanisms: pipeline family's literal-key field roster and type checks;
its repeated nested workspace/artifact/materialization readers; draft/session
consumers' raw extraction; duplicate renderer-membership tuple and registration
store; copied raw diagnostic scans; cross-family source truncation procedure.
Shared source clipping now belongs to CodeDocumentRenderOptions. Composite
command rendering belongs to TypedCompositeCommandSpec; per-case presentation
belongs to actual declared output renderers. Existing generic dataclass codec and
existing AutoRegisterMeta registry are the only reconstruction/membership owners.
The registry key inheritance defect is fixed at its existing nominal owner:
subclass registration projects only its declaration, not its parent's assigned
key. MRO lookup reuses ancestor behavior without pretending sibling DTO subtyping.

New-case evidence: ExtendedInspection adds one DTO declaration and inherits
ArtifactPlanInspection behavior with its extra fact retained. A declared Diamond
renderer composes two independent cooperative presentation capabilities; each
executes once, identity occurs once in the hierarchy view, and AutoRegisterMeta
contains its declared output key. No consumer, dispatcher or field roster edits.

Validation and resource ownership
---------------------------------

Run original packaged R0 and unchanged scripts/check_refactor_r1.py, no exceptions
or changed guard inputs. Provider-free family tests must drive production command
rendering and transport-content reconstruction with real nested DTOs, diagnostics,
progress, malformed/missing/not-run and a declaration extension. Preserve original
failed shard results before splitting or repairing incomplete internal fixtures.
Existing interpreters/dependencies only; serial shards <=512 MiB, one CPU, 60s.

Initial new production-path shard: 14 passed, 5.28s wall, 250284 KiB RSS.
Combined coherent pipeline checkpoint: 25 passed (18 new, seven existing),
11.14s wall, 312636 KiB RSS, one CPU. New coverage drives real run_session,
call_mcp_tool framing and command rendering; text/structured content, nested
diagnostics/hints, source limits, native Ref/Status branches, progress, extension
metadata, malformed nested/missing/undeclared/bool-as-int shapes, absent/not-run,
transport/MCP failures, exact malformed receipt retention and actual CLI main's
compact/JSON entrypoints with a controlled wire response, no runtime launch.
Native server metadata remains exactly openhcs/outputContract=ExecutionJobRef.
Typed error interpretation is tested with serialization forbidden.

After normal integration of parent main b31807d9de067e18d212bdf9353d05099757fc74:
29 passed (22 new, seven existing), 17.17s wall, 310812 KiB RSS. Single-declaration
extension now also exercises real capability ingress and generated command
rendering. Four nullable-fact cases prove false, zero and empty strings are not
silently omitted as absence. Original R0 found eight repeated foreign optional
probes; replaced all nine nullable composition sites with the typed ancestor's
shared optional_lines policy, not local variable rebinding or guard exceptions.
Leaf owners format present facts; the native None absence fact is unchanged.

Original R0 at agent-comms 3b03785f45df2ef5dc62ba6aed99294192ecbb01,
head 018caf90c, base b31807d9: openhcs PASS, 26.53s/87592 KiB. No increased
measure. Original failed R0 remains archived. Syntax/correctness Ruff subset
E9/F63/F7/F82 passes; broad inherited lint debt was not mass-edited.
Whole renderer snapshot after pipeline: 5962 code lines, literal_key_get
157.33/1000 (938 reads), isinstance_call 19.96/1000 (119), None 26.00/1000
(155). Pipeline weighted debt 100 -> 11; 502 -> 400 code lines. This measures
remaining family debt honestly and does not count shuffling as closure.

Unchanged R1, authoritative NRA source 0844525ecaba93e090a064a4ae4914466b2dae60,
base b31807d9, current source head c47b1f6a9: INCOMPLETE, not PASS. First bounded
attempt could not mmap Git's pack under a 512 MiB address-space limit. Retried
the same roots/revisions/tool with bounded Git mapping windows (8m/128m), not
changed detector inputs: materialized recorded source/dependency context, then
ScanDeadlineExceeded during parse_python_module at 55.000s. Wall 56.20s,
263856 KiB RSS. No comparison or descent/proof result returned. Roots remain
openhcs, scripts, benchmark plus all recorded external submodule Python context;
report scope remains changed surviving production files. No exception/waiver,
no substituted scoped result, no full-package/global NRA proof claim. Continuing
source progress does not repair or claim completion of this independent tool.
Owned persistent source snapshot scratch: worktree/.s1-r1-scratch; original tool
TemporaryDirectory cleaned its snapshots on the caught deadline exit.

R0 scripts and benchmark also PASS unchanged (empty changed Python scope).
Shared-owner regression shard: 29 existing knowledge/architecture/function/
authoring/tool-list/code-document command cases PASS, 28.04s/284140 KiB,
provider-free, no runtime. These are behavior checks, not full remaining-family
descent closure. Evidence archive: receipts/S1-pipeline-20261001.tar.gz contains
original failures, subsequent passing logs/XML, full guard outputs and census.
It excludes compiler/build products. Regenerate it after further owned checks;
owned terminal scratch is disposable once the archive is verified.

Original failures remain in the owned output archive: source-first import order
collection failure; JsonValue annotation namespace failure; scoped registry/MRO
failures; five existing fixture failures. Existing fixture updates supply missing
real server/schema/config/ref/source-identity/output-dir fields, remove nonexistent
errors on PipelineSpec/RenderedSource and replace nonexistent base_path with
shared_output_stem. No behavior assertion was removed or weakened. Two actual
presentation regressions (Validate errors label and None group text) were fixed.

Source imports needed the checkout's declared C++ extensions. Built only this
worktree's extensions with existing setup.py, compiler and dependency objects,
one build worker: 3.29s/143740 KiB. No interpreter/package/install changes.
Recorded submodules initialized only here at existing gitlinks; no gitlink edits.
Own compiler/build-lib scratch and two local abi3 binaries are disposable and
must be cleaned after evidence is archived. No application native launch.

Resource helper before work reports warning/exit 2: swap used 14.2 GiB, available
RAM 20.0 GiB, /home free 23.1 GiB. No extra agents or large tests authorized while
this persists; use only serial bounded focused checks. Owned disposable output:
/home/ts/.cache/agent-scratch/openhcs-mcp-result-owners-s1-20261001, purpose source
census/guard/test logs, owner Codex S1. Archive useful receipts in this worktree,
then remove that exact owned run directory after termination. No volatile source.

Source-context scan must include OpenHCS production and recorded dependency
sources where safe. Any budget/tool limitation is incomplete coverage, not global
proof or a blocker to independent implementation. No held-out/reference/science
data is read. No native/MCP/JVM/viewer launches.

Remaining S1 and installed acceptance
-------------------------------------

Codex S1 retains plate, viewer/runtime, UI/code-document/state-surface,
object-state, knowledge/function/authoring and config families after the initial
pipeline checkpoint. XML329, runtime/BaSiCPy217/326 and canonical skill references
remain with their existing owners. Current PR331 core admission is also disjoint.
No parent/foreign/main worktree edits. Parent merges useful locally verified draft
checkpoints with CI deferred. Parent owns affected installed CLI/MCP user journeys
after the scientific lock release. A source import/help/render check is not
installed or live acceptance. Neither this checkpoint nor a partial NRA scan
closes S1, the full ZIP or the parent's scientific goal.
