## Behavior and owning declaration

Which declaration owns the changed behavior? For a bug fix, name the violated
contract, its original reproducer, and the owner corrected here. If the same
file has required repeated fixes, identify its planned refactor surface.

## Persisted formats

For EACH changed store, choose and explain one disposition:

- internal / reset at cutover;
- internal / one-shot migration tool (name it; no permanent dual reader);
- external / versioned contract (name its owner and migration).

If none changed, say so explicitly. Preserve user-written pipelines, registered
function names, user config schemas, persisted results, and third-party formats.

## Evidence and remaining boundaries

Record actual commands, results, and the tested commit. Distinguish scoped
ratchet/R1 evidence, applicable numerical parity, source tests, and affected
installed/live journeys. Include before/after evidence for performance claims.
Preserve uncertain original requests; do not replay them to obtain a green run.

Hosted CI waiting is deferred by owner instruction. This does not waive local
parity, ownership review, live acceptance, or enforced repository merge rules.

## Maintenance closure

Name deleted/replaced code and tests. Explain the new-case edit experiment and
applicable catalog pattern IDs; tooling is not exempt. Do not introduce internal
compatibility readers, aliases, duplicate registries, or shape/type switches.
