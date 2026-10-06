Recorded evidence1027 owner checkpoint
=====================================

Dewey owns integration. Parent issue1027 is the only matching current claim;
open source PRs959 and160 do not implement this boundary. Reused finished
basicpy-readiness checkout on fix/recorded-evidence-references-1027-20261006,
normal merge of current main; all foreign submodule worktrees preserved.

The current recorder is scripts/blind_analysis/operations/recorded-mcp.sh:
util-linux script retains exact mcp.stdin/stdout/timing. Existing nominal
response owner is McpDevToolBatchResponse/McpDevToolResult in dev_client_core;
rendering belongs to McpDevCommandSpec. No existing byte-addressed recorded
response-reference abstraction was found in that production family. The frozen
BBBC013 build_evidence_manifest.py is authored run evidence, not this owner.

Future correction belongs to the existing recorded-client family: one offline
reader of its original stdout, decoding through the existing tool-result codec;
indexes store original journal prefix hash/length plus response byte span and
result index, not result bodies. Capture evidence stores resource identity/hash
and references to original snapshot/state/intervening records. No copied viewer
state authority or new recorder. Packet directs authors to the shared reader,
not another independently authored manifest parser. Frozen ad-hoc code unchanged.

Implementation and retained-record acceptance
-------------------------------------------

openhcs.mcp.recorded_evidence extends this family with a journal prefix descriptor,
exact response span/result references, capture resource references and one offline
index reader. McpDevToolResult and ViewerWindowSnapshotResult own decoding; tool
names derive from the existing capability declarations. Response references reject
addresses outside the indexed prefix. A nearest state is historical evidence only,
never synthesized capture-time state; intervening controls resolve independently.
The future AUTHOR-PACKET routes indexing to this shared reader. Frozen packets and
the original ad-hoc script were not changed.

Real acceptance used the original BBBC013_FRESH23_96 output/runtime/mcp.stdout
under next-bbbc013-retina-fresh23-after-terminals-20261006, plus its existing
mcp-event-index.json and qa-evidence-manifest.json. verify_retained.py resolved all
1479 tool results byte-for-byte equivalent to the frozen decoded results; 28 other
envelopes remain referenced. All241 capture receipts and native PNG hashes match.
The original FIRST-A01-pair raw/result/combined triplet resolves with its original
states and intervening controls. Both original index hashes remained unchanged.
The new index is364018 bytes for104451389 journal-prefix bytes. It contains no
result bodies, state dictionaries or copied control payloads. CLI/non-JSON/UNKNOWN
evidence stays in the original journal identified by the complete prefix hash.

Original index creation handle30971 and real retained verifier81936 both terminal0.
Focused tests: five passed (multiple results, UTF8 byte offsets, nested JSON,
round-trip index, append-only growth, truncation/mutation rejection, failed snapshot
without invented resource). Original test collection failed because this standalone
installed-owner run did not expose the checkout tests plugin; an explicit isolated
pytest configuration then ran the focused file, without source/dependency mutation.

Qualification is candidate source over the existing receiving28 installed owners,
not a newly built/installed wheel. The first source-package attempt61530 failed
before reader execution on foreign old PolyStore TiffPhotometric; a direct-file
attempt also hit socket.py shadowing the standard socket module. Neither created
an index. The supported module entrypoint and runpy source qualification avoid that
script-directory shadowing. No submodule, installed prefix or environment changed.
The initial AST pass used the existing refactor-audit overlay for the MCP family;
this is structural evidence, not a substitute for retained-record acceptance.

No native/client, scientific rerun, package build, cap, truncation or frozen rewrite.
Small disposable indexes live only in the named recorded-evidence1027 scratch and
are removed after qualification; acceptance prints counts, not repeated payloads.

Parent architecture correction, qualified checkpoint
---------------------------------------------------

IMPL-1/MEMB-1: removed the manual command roster and args.command branches.
RecordedEvidenceCommand follows the existing BenchmarkCliCommand declaration
pattern with AutoRegisterMeta, declaration-derived registered_commands and
parser.set_defaults(cli_command=self). Each operation owns its arguments and run;
IndexedRecordedEvidenceCommand owns the common index argument. Adding an operation
needs one declaration, not edits to a second parser or dispatch roster.

BOUND-2/MEMB-5: removed the separate journal field mapping and asdict/Path patch.
RecordedMcpEvidenceIndex.read decodes the whole index through dataclass_from_mapping;
to_dict and the writer project the whole index through to_jsonable. The existing
codec's declared Path handling owns conversion, and nested undeclared fields fail.

Inspected McpDevToolBatchResponse.for_rendering (not from_response): its ingress is
dataclass_from_mapping of the whole batch, followed by selected DTO projection.
Indexing and result readback now use that whole-batch ingress directly, rather than
manually consuming result dictionaries. Only snapshot resource extraction asks the
existing result owner for its typed DTO; historical payloads are not all rendered
through current schemas. Non-tool envelopes stay exact response references, including
all28 originals in the real acceptance. Non-JSON/UNKNOWN bytes stay in the unchanged
104451389-byte original prefix. No converter or alternate batch schema was added.

After the coherent correction: index CLI45807 terminal0; retained verifier21684
terminal0 with1479 exact results/241 exact captures, unchanged frozen indexes and
the original matched triplet; verify CLI79261 terminal0; resolve CLI24237 terminal0
and exact original response agreement (event337, no payload store written).
Focused suite24735 terminal0: eight passed, including declaration-driven extension,
whole-index Path roundtrip/undeclared-field rejection and non-tool resolution.
Existing refactor-audit AST overlay91322 terminal0 over the MCP family: no new
string-dispatch, literal-roster or hand-mapped record site in recorded_evidence.py.
Other pre-existing family findings remain outside this correction.

Review handoff scratch, owner Dewey:
/home/ts/.cache/agent-scratch/recorded-evidence1027-review/index01.json (364018B).
Retain this reference-only index until parent readback/review, then remove the named
scratch. No payload copies, original journal edits or package installs are involved.
