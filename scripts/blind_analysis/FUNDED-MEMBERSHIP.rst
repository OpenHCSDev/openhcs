NEXT funded-programme owner: publication checkpoint
==================================================

The original programme projector now has a parent-only publication transition
at ONE fixed funding root. It atomically replaces that owner's program.json
with the reviewed proposal, whose membership and full retained ledger are
derived together by the original successor JQ. No per-author ignore list,
PID-discovered roster, current-head pointer, second registry or polling loop.
Each run root stays separate and immutable; its package, helpers, limits and
clock must not become current funding state. The shared lock resolves a real
publication/admission race; consumers will hold it shared for one admission.

Working checkpoint scope: original prepare mechanism plus authenticated,
parent-released atomic publication and preserved prior-state receipt. It checks
every removed run is explicitly replaced/retired and has original terminal
custody, never treating failed/UNKNOWN client state as closure. It is not yet a
complete consumer cutover or live acceptance. No current/frozen packet changed.

Remaining closure: original slot/ledger owner must read this same funding root
for current reservations and full history, while caps/identity/helpers/config/
source/deadline come from each immutable run owner. Sum each funded run's own
output/scratch allowance, not one newest uniform cap. Launch/recorder/client and
generic author packet must use that ownership end to end. Delete the original
snapshot-authority reads in those NEXT consumers in the same completed patch.

Concrete borrower: the historical next-recorded-admission operations symlink
recorded-mcp.sh/mcp-client.sh into this checkout. Parent asked to detach/preserve
those historical dependencies before changing these two tracked source files.
No borrowed/frozen bytes were edited; this checkpoint only adds NEXT owners.

Skills: current NRA/refactor-audit and authoritative packaged archive read.
IDEN-1 separates run permission from current funding; MEMB-1 rejects repeated
membership; IMPL-12/13 reject copied admission and lifecycle implementations.
Complete related original Bash/JQ family read (projector, member/helper/writer,
resource, launch, recorder, client, packet). Python/NRA AST cannot parse these
shell/JQ owners; no Python structural edit or global AST closure claimed.
Open PR roster checked on mainf7de9efad, no competing funding owner. Existing
Python/runtime/dependency owners are not modified. Focused source publication
controls and actual future parent entrypoint qualification remain to follow.
