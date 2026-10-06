# Compile reuse with runtime observation exports

Owner: OpenHCS blind-analysis integration coordinator. Issue #179.
Audited main ac2e10e9a190e877f6dab4964dae1e051d159ac9.

The installed public MCP accepted compilation but rejected reuse of the same
session when execution requested an observation export. The export-only path
and scope entered the full request hash. The rejected reuse also consumed the
valid compile artifact before compatibility validation.

## Admitted answers and determining owners

The authorized compile -> execute -> preserve inspectable evidence workflow
requires observation destination and values/outcomes retention to vary without
changing compilation compatibility. Source identity, pipeline source, global
configuration, workload axes, debug compile inputs, and unknown transport inputs
must still distinguish compilation. Full submission identity remains distinct.

ZMQAuxiliaryExecutionParams already determines observation options and validates
them. Its observation projection now drives both wire emission and the excluded
compilation fields. No mirror exclusion roster is introduced. The projection
contains defaults too, so explicit values scope and absent export path do not
invalidate reuse. Scope is emitted explicitly with requested observation output.
The existing transport Enum remains a value-only boundary vocabulary; it does
not acquire a behavior dispatch table.

ZMQExecutionRequestPayload owns full request identity and derives the narrower
compilation identity through the existing canonical signature algorithm.
DebugExecutionConfig retains ownership of debug replay normalization; it receives
the same observation-free compilation inputs. ZMQExecutionContext is a derived
server view. ZMQCompilationRequest and ZMQCompileArtifactRecord name and consume
compilation_signature, not the wider request_signature. No compatibility aliases.

Required: auxiliary observation declaration -> wire projection and compilation
projection; request payload -> compile-record/reuse identity; valid artifact ->
worker bundle. Forbidden: observation destination -> compile incompatibility;
rejected compatibility -> artifact consumption. Distinct roles: complete request
logs, debug replay policy, output writers, UI history and biological acceptance.

## Source coverage, counterevidence and proof limits

Original NRA syntax census covers execution_signature.py, compilation.py and
execution_server.py at the pinned main: 13 original ClassDef rows. Preserve every
row and unique compact-family join, including alternative owners. External Enum,
ExecutionServer and imported runtime behavior are not proved by this bounded
projection. Full global detector/raw-record/R1 and authored effect-equivalence
proof remain OPEN. This is a scoped behavioral repair, not an equivalence claim
or complete architecture audit.

IDEN-1 and IDEN-7: a full request signature answered a narrower compile question.
BOUND-2: derive the observation projection from its existing typed owner rather
than adding another string-key filter in the compiler. A future observation-only
field belongs to that owner's wire projection; compilation exclusion is derived,
not another handwritten membership list.

Runtime compile caches reset on process restart. No durable science, saved
session, reference answer or installed shared application is rewritten.
PR #157 owns outcome-export paths; #180 owns lazy catalog preparation; #183 owns
completion polling. Their shared-file hunks are separate and were communicated.

## Acceptance

Focused tests preserve full request differences while accepting values/outcomes
destination changes and defaults; reject source, pipeline, config, axis, debug
and unknown changes; reject invalid observation scope. Reuse rejects signature,
plate and missing-context differences without consuming either ordinary or
debug-retained artifacts, and consumes ordinary artifacts only after validation.
Installed public MCP must compile a bounded source-backed pipeline, execute
with each observation scope using the returned artifact, and reopen actual typed
retained observations/output files. Report installed, live and biological
evidence separately. No timeout increase or repeated uncertain execution.
