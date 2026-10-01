S1 issue339: declared typed input projection
===========================================

Implementation owner: Arendt. Integration/installed acceptance owner: parent.
Persistent worktree: /home/ts/wt/openhcs-mcp-generated-input-contracts-339-20261001.
Branch: fix/mcp-generated-input-contracts-339-20261001. Base is fetched canonical
main7b0ec3f5ab5a35a586d77c480fb7d5d6b1c85ba0, merged343. Its reviewed shared
unavailable_summary and absent_text hooks are inherited unchanged, not copied.
No edits to parent343 config leaf/tests/receipt,338 handlers or Darwin344 runtime.
Parent owns the next live338 slot. This work is source-only, no native/MCP/viewer.

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
