Closed-journal MCP shell exit1 investigation
==========================================

Singer owns OpenHCS response/JSON diagnostic receiving; python-introspect's
declaration decoder is a shared dependency seam being coordinated with Dewey.
Root394/541 source/units and merged567 native semantics remain independent.

Pinned currentmain2df0918353b47fa07d19fe4b6cc8b52b5e4c1695. Existing checkout
was reused on a new branch after567 closed; six foreign dirty gitlinks and all
untracked originals remain untouched. Open PRs394/404/472/494/518/522/541/468
have no active dev-client shell/result implementation claim. Current394 file
census has no dev_client, dto/functions or serialization/json crossing.

Original engineering567/public94-attempt01/mcp.stdout records eight public
operation receipts with empty visible errors; original shell ends terminal1.
No new client/native process or request was used to determine the cause.

Actual original qualified target8513 decoder applied offline to all eight closed
receipts: seven decode without error; registration-status becomes
McpDevPayloadFailure with mcp_payload_invalid/ValueError:
CustomFunctionRegistrationObservation received undeclared field(s): outcome.

Original python-introspect.dataclass_from_mapping only admits init=True fields.
Observation.outcome is declared init=False and derived from publication/saved
proofs in __post_init__; original to_jsonable emits all dataclass fields.
The same nominal declaration therefore serializes a field its decoder rejects.
McpDevToolResult.has_errors correctly sees the rejection; persistent shell
aggregates that returncode. The custom McpDevPayloadFailure JSON projector emits
only receipt, deleting rejection diagnostics from visible JSON. This explains
the exit1 without alleging native registration/status/close failure.

Original read-only diagnostic script/logs remain under engineering567/
public94-attempt01/DIAGNOSE-CLOSED-RESULTS01.py/.stdout/.stderr: terminal0,
4.12s,236672KiB peakRSS,Swap0; no sockets or source/image execution.
Actual original dev_client_core.py SHA256
2aaaffec501e901352192ed35016caa6ce00122b429e41b3f7c8683eb3fd1aed;
target01/python_introspect/dataclass_projection.py SHA256
82662ff8eaa4f2aeb3b33edd61abae57020a7f139c3aa396d82dcecf8b801160.

Required relation and owner destination
---------------------------------------

One declaration must drive encode/decode of derived fields. Constructor inputs
remain constructor-owned; supplied derived wire values must be checked against
the actual constructed result, not dropped, assigned or allowed to override it.
Unknown fields and mismatched derived proofs must fail closed. Reuse the original
python-introspect decoder, not a consumer-specific outcome pop/type switch or
alternative codec. BOUND-1/2/8 apply at this declaration boundary.

The existing McpDevToolResult/McpDevPayloadFailure owns failed-decode diagnostics
and original receipt. JSON, formatted output, returncode and persistent aggregate
must project that same owned failure, not silently serialize success while
retaining hidden exit1. No error suppression/--allow-error-payloads workaround.

Acceptance after coherent implementation: original closed status receipt decodes
to the declared observation with exact matching proofs, shell returns0 for those
unchanged successful receipts; genuinely malformed/mismatched/new declaration
cases retain original receipt and visible typed diagnostics with nonzero exit.
Use complete relevant AST/dependency/consumer evidence before production edits;
focused original user entrypoint verification last, no mutation replay/new client.
