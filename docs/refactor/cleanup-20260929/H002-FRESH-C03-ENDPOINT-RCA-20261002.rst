Fresh H002 candidate03 endpoint diagnosis
=========================================

Scope and disposition
---------------------
Planck owns this bounded engineering review; parent retains integration.
No author thread was read or messaged. No health request, runtime, compile,
scientific execution, model attachment, or uncertain operation was replayed.
Retained old H002 viewer5690 and retinal viewers were not contacted.
Only original journals/source, GitHub owner claims, and an in-process synthetic
argument-decoder control were inspected. This is NOT a third scientific author.

Determining cause
-----------------
Candidate02 sent flat host/port/transport_mode/persistent fields to
openhcs_create_orchestrator_session_from_pipeline_source. Candidate03 instead
put those fields under an unadvertised top-level "connection" object.

The generated MCP input schema advertises flat fields only. FastMCP's actual
ArgModelBase uses Pydantic's default extra-ignore policy: "connection" is removed
before the OpenHCS binding runs. Its from_fields defaults then select
host="localhost", port=None, transport_mode=None, persistent=True.
OpenHCSZMQConfig.client_endpoint resolves these to default port7777 and, on this
Linux host, IPC. The selected data route is therefore the source-derived
ipc:///home/ts/.openhcs/ipc/openhcs-zmq-7777.sock, not TCP127.0.0.1:6014.
Host is ignored by the IPC declaration. This route is derived from installed
source and the actual decoder control, not a newly observed socket connection.

The original submit receipt observed OpenHCS0.8.6 at the selected endpoint and
refused compatibility against expected0.8.7. It returned submit_error with
server_execution_id=null. There was no accepted candidate03 compile job.
The peer PID, source checkout, and process incarnation are NOT recorded by the
retained failed response; they remain unknown. No claim that native6014 was
running0.8.6 is justified.

Exact retained evidence
-----------------------
Author output root:
 /home/ts/wt/openhcs-issue-batch-20260929/blind-sol3-phase01-20261002/H002/author-workspace/output

* runtime/mcp.stdin:140 — candidate02 flat route to6014.
* runtime/mcp.stdin:177 — candidate03 nested connection; no flat route fields.
* runtime/mcp.stdin:178 — submit session-2, wait=false.
* runtime/mcp.stdout:14614..14761 — original advertised flat input schema;
  the schema has no connection property (line range approximate enclosing
  schema; determining owner is the named tool within that original response).
* runtime/mcp.stdout:18784..18840 — exact nested request/session-2/job-3 failure.
* receipts/061-openhcs_submit_compile.json — job-3 submit_error,
  EndpointApplicationCompatibilityError, null server_execution_id.
* receipts/001-openhcs_health_check.json — original MCP PID741605, version0.8.7,
  installed463 source; receipts/062 confirms same generation after the failure.
* receipts/005-openhcs_start_owned_runtime.json — exact owned native
  PID743143/create_time1790975224.3, TCP6014/control7014.
* receipts/063-openhcs_observe_owned_runtime.json — that original native still
  alive/ready after the mismatch.
* receipts/058-openhcs_close_viewer_window.json — viewerPID745483,
  create_time1790975307.67; ACK/process_exited/endpoint_terminated/succeeded true.
* receipts/064-openhcs_close_owned_runtime.json — original native identity
  positively closed, ACK/process_exited/endpoint_terminated/succeeded true.

Native original log:
 runtime/scratch/data/openhcs/logs/openhcs_zmq_server_port_6014_1790975225101024469.log
Lines55 and86..170 identify TCP6014 and prior accepted compile
a0898d4c-0761-46b6-891f-92403f292d4c / execute
9384a069-fc30-47d8-90ca-de97373d7b8c. It has only these two queued/request
identities, prior execution terminal1252, and shutdown1259. It contains no
candidate03 request. The null submit identity is authoritative; absence from
this log is supporting evidence, not proof of every remote side effect.

Source generation and causal consumer chain
-------------------------------------------
Original program.json source_install and historical health server_source_path:
 /home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering463-installed/target

Original operations/mcp-client.sh derives PYTHONPATH from that program owner,
uses the paired interpreter, and admits declared6014/6015 locks.
Candidate03's pipeline viewer setting6015 is not the compile connection.

Relative installed-source sites:
* agent/capabilities.py:2679 — CreateOrchestratorSessionFromPipelineSourceCapability
  owns PipelineSourceOrchestratorSessionRequest + AgentFromFieldsServiceInvocation.
* mcp/server.py:1553..1683 — original generated FromFields binding derives
  signature/schema from request.from_fields; no source-session-specific UI
  connection binding. The unrelated UI binder's connection parameter is NOT
  the path used here.
* agent/dto/execution.py:168..202 — flat from_fields defaults and construction
  of the existing ExecutionConnectionSpec owner.
* agent/services/execution_session_service.py:455..483,906..919,1010..1042 —
  request.connection retained without alternate endpoint selection.
* same service:729..750 — ExecutionClientGateway takes record.session.connection;
  ZMQExecutionClientFactory:413..424 calls its execution_client.
* agent/dto/execution_connection.py:91..109 — constructs the original client.
* runtime/zmq_execution_client.py:678..700 / runtime/zmq_config.py:101..120 —
  original configuration resolves absent port/mode.
* paired zmqruntime/config.py:89..93 — default_port7777.
* paired zmqruntime/transport_modes.py:373..417 — Linux IPC priority0 and
  namespace-derived original socket path.
* actual paired MCP dependency comes from
  /home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages/mcp:
  server/fastmcp/utilities/func_metadata.py:47..99,258..262 —
  ArgModelBase configuration, validation, declared-fields dump;
  server/fastmcp/tools/base.py:53..83,100..120 — same decoder used on calls.

Bounded decoder control
-----------------------
H002-FRESH-C03-DECODER-REPRO.py derives the actual installed from_fields
signature via AST (no import of OpenHCS, no source/session invocation).
Using the actual paired FastMCP dependency, flat fields retain6014/TCP;
the nested object yields localhost/null/null/true. Direct original-signature
binding would reject "connection"; dependency model filtering hides that error.
Original invocation: paired python -B helper, external timeout20s.
Terminal0 in under one second, no server/session/tool dispatch. This qualifies
the decoder mechanism, not an installed live fix.

Product gap, ownership, and acceptance
-------------------------------------
Author API misuse is established; product silently accepting/dropping endpoint
intent is also concrete. The compatibility guard behaved correctly and must
not be weakened. No need to patch source materialization or scientific code.

Owner review: open PR394 head619468b998482b6e0cbcf212f8f8e1e02a9fbef6,
updated2026-10-02T21:19:28Z, is Root's source/runtime plumbing. Current open
PRs472/468/404/394/207/160/125/110 showed no connection-decoder fix. Remote
main6849d09b1305ee3583c3483059350d56be04e18d retains the same FromFields binder.
Dewey previously owns MCP/endpoint boundaries (#465); that does not establish
an active claim on this newly identified decoder defect. Parent must assign
implementation or explicitly extend Dewey's owner scope. Planck owns diagnosis
and evidence-only publication, not competing production changes.

Required repair belongs to the original MCP argument-decoding/registration
owner: reject undeclared keys using the declaration-generated schema/model
before session creation, rather than adding a nested-connection compatibility
alias, a hand-maintained key set, a second endpoint registry, or auto-retry.
Applicable audit principle: BOUND-1 strict boundary decoding, BOUND-3 derive
allowed fields from the owner. No structural production refactor was attempted;
full-family AST and installed live verification remain implementation duties.

Acceptance: malformed nested connection must fail BEFORE creating a session
or touching any endpoint; correct flat TCP route must be retained in
get_orchestrator_session; intentional omitted defaults must remain explicit
and verifiable; same-version foreign endpoints must not make malformed input
silently successful. Qualify sibling generated bindings through their common
owner. Then perform one tiny separately authorized installed public journey.
Do not replay the frozen scientific candidate or relax version compatibility.
