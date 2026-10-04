Runtime observation retention: issue131
=======================================

The previous flat MCP health/context measurements do not establish native
execution retention. The original BBBC013 five-GiB family OOM remains a retained
failure, not a clean reproduction of the original MCP query report.

Source ownership
----------------

Default analysis consolidation selects full parent runtime observation whenever
there is a persistent exported artifact. Full observation returns every record;
worker image-cache release does not release the runtime value store. Parent
consolidation rerenders CSV text from those records although its final typed
inputs are table text, scope identity and compiled persistent destinations.

This change will project those existing typed inputs at context completion,
retain independently declared PLATE inputs or explicitly requested full values,
and release completed worker payloads. It must preserve the original writer,
filemanager, backend, source identities and configured table exclusions. No
parallel registry, filename identity, forced collection or restart policy.

The native server also attaches the execution orchestrator to execution-history
metadata for cancellation. Terminal history needs its separate typed output-plate
and execution extras, not the live orchestrator's compiled context graph. Its
original run lifecycle must retire that reference after output exports and
summary enrichment, preserving active cancellation and compile-artifact custody.

Verification scope
------------------

NRA/refactor-audit owner-family AST evidence covers declarations, reads, writes,
imports and related consumers before edits. Proportionate controls then cover
table equality, excluded exports, richer-payload CSV, PLATE inputs, transport,
completed-image release and error/cancellation. Real installed public synthetic
receiving will measure per-process/family RSS, PSS, private dirty and swap over
repeated bounded complete native executions, idle and typed lifecycle closure.

Status: initial source-owner checkpoint; implementation and actual receiving
are not yet claimed. Shared runtime hunks are coordinated with Root394.
