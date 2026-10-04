Runtime observation retention: issue131
=======================================

The previous flat MCP health/context measurements do not establish native
execution retention. The original BBBC013 five-GiB family OOM remains a retained
failure, not a clean reproduction of the original MCP query report.

Source ownership
----------------

Previously default analysis consolidation selected full parent observation whenever
there is a persistent exported artifact. Full observation returns every record;
worker image-cache release does not release the runtime value store. Parent
consolidation rerenders CSV text from those records although its final typed
inputs are table text, scope identity and compiled persistent destinations.

This change projects those existing typed inputs at context completion,
retain independently declared PLATE inputs or explicitly requested full values,
and release completed worker payloads. It must preserve the original writer,
filemanager, backend, source identities and configured table exclusions. No
parallel registry, filename identity, forced collection or restart policy.

The native server attaches the execution orchestrator for active cancellation.
The paired original ZMQRuntime ExecutionServer.run_execution already pops that
reference in its terminal finally block. That inherited lifecycle is preserved;
no duplicate OpenHCS cleanup or unproved cross-request leak is introduced.

Verification scope
------------------

NRA/refactor-audit owner-family AST evidence covers declarations, reads, writes,
imports and related consumers before edits. Proportionate controls then cover
table equality, excluded exports, richer-payload CSV, PLATE inputs, transport,
completed-image release and error/cancellation. Installed controls passed all147
affected cases across two preserved attempts: first141PASS/6 authored-fixture
failures, then6 corrected fixture passes. No production guards were weakened.
Ordinary target01 matches815 packaged source files,90 assets and13 skill files.

Public native receiving completed the synthetic eight-well/sixteen-field job
and a separate one-well explicit VALUES export. Original public readers verify
all16 rectangle ROI areas/bounds, two correctly scoped measurement rows per
well, consolidated eight-well totals and source/output bounded pixel equality.
The public measured-run finalizer validates the separate value export against
its original compile/job/endpoint identities. PLATE semantics are covered by
installed controls, not a new public PLATE execution in this case.

The same installed MCP/native family stayed within4GiB/Swap0/oneCPU, with
1787359232B recorded peak. Native3907958 acknowledged typed shutdown and exact
process exit; MCP3901290 and its original scope are also gone. No forcedGC,
restart, biological input or cap increase was used. Shared runtime hunks remain
coordinated with Root394; current482573173 has no determining family change.

The original issue additionally concerns repeated health, function catalog,
knowledge, artifact-plan and custom-registration requests in a long-lived MCP.
Thirty repeated health/catalog/knowledge rounds plus five artifact-plan queries
were recorded separately from cold imports and the intentional VALUES export.
Post-first-job MCP RSS377836KiB; after ten warm rounds377868KiB; final382976KiB
includes subsequent validation, registration and pixel-reader imports. Native
final RSS1490992KiB is below its post-first-job1500528KiB. These short mixed
measurements do not establish a long-session leak slope. Registration revision
two returned an uncertain outcome; it remains preserved and unreplayed, not
counted as successful revision validation. Issue131 therefore remains open;
this verified default-consolidation fix does not assert the cause of the old
biological OOM or claim the complete original mixed-MCP problem resolved.

Original evidence: issue131-memory/QUALIFICATION01.rst and
issue131-memory/public94-attempt01/PUBLIC-ACCEPTANCE01.rst under the persistent
issue-batch root, with original stdin/stdout/timing, native logs and outputs.
