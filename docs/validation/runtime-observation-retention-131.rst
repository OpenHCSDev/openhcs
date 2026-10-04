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
completed-image release and error/cancellation. Real installed public synthetic
receiving will measure per-process/family RSS, PSS, private dirty and swap over
repeated bounded complete native executions, idle and typed lifecycle closure.

Status: coherent source implementation, controls not yet executed and no installed
or public memory acceptance claimed. Shared runtime hunks are coordinated with
Root394; current482573173 has no determining change to this owner family.

The original issue additionally concerns repeated health, function catalog,
knowledge, artifact-plan and custom-registration requests in a long-lived MCP.
That mixed route needs its own per-process growth measurement, including source
revisions. Warm baseline is not growth. This native consolidation fix does not
by itself close that scope, and no unverified native OOM cause is asserted.
