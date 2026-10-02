S1 issue339: declared typed input projection
===========================================

Implementation owner: Arendt. Integration/installed acceptance owner: parent.
Persistent worktree: /home/ts/wt/openhcs-mcp-generated-input-contracts-339-20261001.
Branch: fix/mcp-generated-input-contracts-339-20261001. Base is fetched canonical
main7b0ec3f5ab5a35a586d77c480fb7d5d6b1c85ba0, merged343. Its reviewed shared
unavailable_summary and absent_text hooks are inherited unchanged, not copied.
No edits to parent343 config leaf/tests/receipt,338 handlers or Darwin344 runtime.
Parent owned the live338 slot and now owns next344 acceptance. This work remains
source-only, no native/MCP/viewer.

Current source checkpoint: c166a4a0a43893c335825387b9686d778df137bd, normally
integrated parent-merged338 main05c3cf2883fb2ce75c14961264dabad633e639ee at
227df0a1e73862c19fcb3f3a054a7037f2ee1663.338 installed gate/merge is parent
evidence in its separate receipt; this branch did not launch or own that slot.
Source acceptance62PASS/R0PASS. Installed339 acceptance remains parent-owned.
Historical sections below preserve original attempts; final limits are explicit.

Before edits: actual antipattern review
-------------------------------------

Read complete S1 dispatch, binding GOAL-SCOPE, current canonical00-RULES/01-INDEX,
full NRA/refactor-audit skills and batching, authoritative refactor-audit.skill
SKILL/catalog README/complete BOUND/IMPL/MEMB/identity/surface-receipt examples.
Archive SHA256:100fbe8ef89664b866777e87b2c8640a3432e8a10e9188dff81c97942d551bf6.
This is actual source-backed antipattern review, not a global analyzer proof.

BOUND-2/IMPL-4: capabilities.py:1953/1968/1985 advertise the actual existing
ExecutionConnectionSpec and FunctionCatalogPreparationHandle. GeneratedSingle-
ToolCommandSpec.configure_parser:617 and tool_arguments:646 only project the
existing AgentCliRequest nominal capability or a scalar transport declaration.
These three generated catalog commands consequently expose no owned inputs.
ExecutionConnectionSpec at dto/execution_connection.py:20 already owns host,
port, transport_mode and persistent, constrained validation, credential-free
projection and actual execution-client construction. FunctionCatalogPreparation-
Handle at dto/functions.py:107 already owns connection plus ProcessIdentity;
it rejects stale owners. Neither record is to be mirrored in a CLI facade.

IMPL-12/13: a reusable dataclass CLI capability belongs below the existing
AgentCliRequest ABC, not separate from_fields/as_tool_arguments copies on both
DTOs. Reflect its real constructor signature; decode through existing
python_introspect.dataclass_from_mapping, encode with existing to_jsonable.
Preserve ExecutionConnectionSpec.public_connection as the explicit credential
boundary; generic input serialization is not that runtime projection.

MEMB-1/2/5,IDEN-5: use existing capability registration and CLI profile projection.
No command/type-name cases, duplicate registry, field roster, DTO mirror or codec.
Existing consumer distinction between scalar wire input and nominal request
types is not a catalog-subtype roster; extend declarations, not those cases.
Shared CLI text parsing must preserve typed booleans/enums/nested handles and
Annotated constraints without new field-name decisions or runtime coercion.

Measurements and resource ownership
----------------------------------

Before census: original debt_census.py, existing Python3.14, full openhcs/mcp and
openhcs/agent/dto roots at this base:19864 and7358 code lines respectively,
with no parse failures. Exact coverage/counts/logs are retained in
/home/ts/.cache/agent-scratch/openhcs-mcp-generated-input-contracts-339-20261001.
Purpose: bounded census, original source CLI reproducer, focused tests and original
guard logs. Archive before cleaning this exact owned disposable output. Persistent
source remains. Resource helper warns swap14.2GiB/home15.8GiB; no extra workers,
downloads, interpreters, global installs, agents or scientific/reference inputs.
Use existing Python/dependency objects, one CPU,60s shards, measured <=512MiB RSS.

Original R0 and pinned NRA084 R1 remain unchanged. Full production/dependency
context is required for R1 where safe; retain incomplete55s deadline and actual
failures, never substitute a focused certificate or claim global proof.

Behavior and extension acceptance
---------------------------------

Dedicated tests exercise unchanged _build_parser/_calls_from_args production
consumers: generated start inputs, exact status/cancel connection+incarnation
handle, JSON ingress once, enum/boolean behavior, missing/malformed/invalid fields
and unknown nested fields before any server launch. Existing generated config,
knowledge/runtime requests retain their custom factories/arguments.

A new declared typed request subtype must acquire fields through the existing
capability/profile generation without caller/registry/dispatcher edits. Independent
behavior hooks compose via cooperative super/MRO in both diamond orders; owning
ancestor and identity execute once. Test declarations are removed on teardown.

Persisted formats: NONE changed. MCP/native routing and external advertised DTO
identities/bytes are unchanged. No runtime state store or alternate reader added.
Parent must separately validate installed generated start/status/cancel and
generic-call equivalence on one fresh authorized endpoint, including exact owner
handle lifecycle. Source checks cannot establish that installed/live gate.

Named remaining S1: plate/function/knowledge/object-state/viewer/runtime/UI/code-
document/state-surface renderers.343 config closure is merged;334 pipeline
checkpoint remains complete.338 installed acceptance belongs to parent.339 is
one coherent input-boundary defect, not completion of S1/ZIP.

First coherent working source checkpoint
---------------------------------------

23 dedicated production-consumer cases PASS,4.69s,253016KiB RSS, CPU0/timeout60.
The actual generated start command accepts port/host/transport/persistence;
generated status and cancel preserve the exact nested connection/incarnation
handle and equal generic-call JSON arguments. Both independent host-normalizing
and ephemeral-connection capability orders execute once, construct the new DTO
subtype once through the shared ancestor and retain its newly declared field.
No edits to dev_client_commanding.py, capability declarations, dispatcher,
registry, renderers, tests/unit/agent/test_mcp_server.py or runtime owners.

The existing generated-consumer scalar-vs-nominal-request distinction remains
unchanged: this defect is closed by declaring the existing capability on actual
input owners, not by expanding its consumer type/name cases. New code adds one
behavior-owning, field-free ancestor; no DTO or shape duplication. Existing
factory annotation resolution now follows inspect.unwrap and the established
signature-analysis owner. Nested fields use existing parse_json_object then the
existing dataclass decoder; boolean CLI flags derive from the actual annotation.

Original failures retained: initial fresh-WT imports lacked compiled tabular
extension; two help attempts stopped before MCP launch. A first factory reflection
attempt did not unwrap decorated annotation globals; it failed before argparse
dispatch and was corrected through the real signature owner. First test run:
16PASS/7FAIL from a test-only missing get- in the real status command spelling;
all cases rerun unchanged after correcting the fixture command, no product alias.
Source native extensions built locally for import only,3.44s/143688KiB, no native
server launch. Recorded source gitlinks initialized with --init/--recursive/
--no-fetch; Git printed Cloning for eight dependency repositories. Do not infer
that --no-fetch forbids clone transfers. No Python/package/data/provider install
or download occurred; initialized recorded source checkouts persist in this WT.

Ruff correctness E9/F63/F7/F82 and git diff --check PASS. Original R0/full-context
R1, existing generated request regressions and actual source CLI help receipt
remain pending at publication. This draft is a working source checkpoint,
not installed/live acceptance or global S1 completion.

Declaration-policy correction after first publication
----------------------------------------------------

Original packaged R0 at3b03785 failed one StringSubscript increase from writing
the argparse action keyword in the shared consumer. Original log is retained.
Boolean argument behavior now belongs on the existing AgentCliArgumentSpec
declaration: its external argparse action contract accepts action classes as well
as strings. AgentDataclassCliRequest derives those specs from actual dataclass
boolean annotations and composes inherited specs through super(). The existing
consumer already applies these specs; the added raw keyword write is deleted,
not renamed, waived or hidden. This avoids duplicate option-configuration logic.
The new-case experiment now also declares a fresh boolean field and exercises
its generated negative flag through the unchanged consumer, both MRO orders.

60 combined new-input/config/pipeline source cases PASS5.97s/259176KiB RSS.
An earlier11-case selected existing config/knowledge/runtime/profile shard
PASS13.12s/317028KiB; an initial shell-runner SyntaxError is retained separately.
No original tests were edited. Pinned NRA084 full-context R1 at d24bff236 is
INCOMPLETE: original openhcs/scripts/benchmark roots plus all recorded dependency
Python,55s parse_python_module deadline, wall57.30s/264084KiB RSS, AS512MiB/CPU0.
Materialization completed, parsing did not. No counts, descent certificate,
global pass or silent source exclusion is inferred. Guard reruns at the corrected
source remain pending; timeout is not a blocker for independent source delivery.

Final checkpoint, guard limits and cleanup
------------------------------------------

New-case extension found a real shared-owner defect: an omitted dataclass
default_factory value reached typed reconstruction as Python's constructor
marker. The original one-fail/one-pass reproducer is retained. The owning CLI
ancestor now recognizes that marker through the actual dataclass Field and
constructor Signature; it omits only that marker before the existing codec.
The declared factory runs once inside typed construction, never while generating
the parser; explicit negative boolean input does not run it. No factory/default
roster, private sentinel name, mirror, new codec or per-caller case was added.
This behavior is on the real ancestor, not duplicated across the two actual DTOs.

Final combined62 cases PASS6.11s/258808KiB RSS, CPU0/timeout60:25 new inputs,
existing config and pipeline behavior. Both diamond orders also verify the
distinct existing credential-free runtime projection remains base-only while
the CLI retains new subtype fields. Two selected existing generated-profile/
knowledge server tests PASS20.75s/280668KiB at6ed; this is separately scoped,
not relabelled as a current full server run. No original test assertions changed.
Normal338 merge has zero diff in the four339 production files at6ed; its focused
60-case sanity PASS10.80s/257744KiB before the default-factory extension fix.

Source-only real command: start-function-catalog-preparation --help exits0,
4.82s/248880KiB, declares host/port/transport-mode/persistent/no-persistent.
--port true exits2 at local argparse,4.73s/248908KiB, before MCP launch. Working
generated status/cancel nested arguments are exercised through real consumers,
not help-only or regex proof. These command observations precede the factory-only
correction; their exact original logs and provenance remain retained.

Unchanged original packaged R0 at3b03785, main05 ->c166:PASS15.27s/87356KiB,
zero increases/exceptions. Earlier corrected main7b ->6ed PASS41.59s/87476KiB;
scripts/benchmark roots exit0, no changed Python, not extra behavioral coverage.
The earlier original failure is retained; no guard changes or metric aliasing.
Correctness Ruff E9/F63/F7/F82 and git diff --check PASS. Production diff versus
main05:13 lines deleted,82 added in four files; one field-free owning ancestor.
Earlier census at6ed shows zero debt increases in every measured category and
one added class; its +47 code-lines observation precedes the factory fix.

Pinned NRA084 full original R1 main7b ->6ed:INCOMPLETE,55.000s deadline during
parse_python_module, wall57.42s/264124KiB, AS512MiB/CPU0. Source scope requested
unchanged openhcs/scripts/benchmark plus ALL recorded dependency Python context.
The policy materializes and scans revisions sequentially: BASE materialization
completed, its analysis did not, HEAD analysis was never reached. No before/after
counts, omitted-detector certification, descent certificate or global pass exists.
The final main05/default-factory source was not broadly rescanned, per owner's
explicit no-duplicate-broad-audit instruction. This omission is deliberate and
stated, not hidden behind focused source tests or the old timeout.

Archive: receipts/S1-generated-input-contracts-339-20261001.tar.gz contains all
original/current logs, XML, before/delta census, source integration and local
native binary hashes. Fresh extraction and comparison precede cleanup. Owned
verification scratch:
/home/ts/.cache/agent-scratch/openhcs-mcp-generated-input-contracts-339-verify-ZuCETp.
Named5.7MiB validation scratch, verification extraction, own pytest cache and two
own compiled import extensions are moved to recoverable trash after archival.
Persistent worktree/source and all versioned receipts remain. No other worktree,
installed package, configured skill, frozen environment or runtime is modified.

Done source checkpoint, NOT installed339/S1/ZIP completion. Parent must next
qualify the installed generated start/status/cancel and generic-call route on a
fresh exact candidate: explicit routing, exact returned incarnation-bound handle,
preparation lifecycle, native/external JSON semantics, original missing/invalid
receipts, and exact owned process close. Parent344 currently owns the live slot;
this branch takes none. Remaining raw renderer families and existing other CLI
profiles are not declared globally clean. Existing scalar-vs-request and Python
annotation-kind boundary distinctions remain; no catalog leaf switch was added.
