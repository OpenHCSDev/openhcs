Recorded scientific-client startup
==================================

These are the NEXT versions of the existing blind-analysis recorder and
installed-client performers, published from the operational harness. Use them
through a future programme's operation_owner_root alongside the unchanged
original slot-env.sh and resource-check.sh. There is no new admission algorithm.
Do not replace any live/frozen programme's symlinks or installed package.

Start the recorded interactive entrypoint with an outer PTY and a caller-owned
unique observation name::

  FLEET_PARENT_RELEASED=1 bash "$FLEET_OPERATIONS/recorded-mcp.sh" "$FLEET_ROOT" "$FLEET_SLOT" startup01

In tools.exec_command specify tty=true and retain the returned session_id.
The recorder checks existing journal/startup custody, verifies predecessor
writer release and invokes the original resource guard ONCE before script
creates mcp.stdin/stdout/timing. A known pre-dispatch rejection preserves its
unique resource receipts and exact exit status without consuming those logs.
Only at a later authorized operational checkpoint may a new observation name
be submitted, subject to the same deadline and original resource policy.

After recording begins there is one retained handle/journal. Existing logs or
the first-mcp marker refuse another start before admission. Child failure or
UNKNOWN is not converted into pre-dispatch rejection; never replay it. The
internal mcp-client performer no longer performs a second startup admission.
It retains installed environment/path policy, WM check, original first-start
clock and systemd scope launch, including the original10s client idle policy.

Original witness: next-three-after498-20261003 H001_REPEAT01/mcp.stdout records
COMMAND_EXIT_CODE76 before any first-mcp-started.epoch; H003's gate also failed
before that marker. The recorder already created logs, so subsequent starts
failed its no-overwrite checks. The two original author terminal reports,
resources and journals remain unchanged. H002's continuing handle is untouched.

Ownership review: the complete related recorder -> client -> resource/ledger
-> slot/helper/writer family and author-packet entrypoint was read, including
historical phase03 and the current fourth-family sources. Startup admission
moves from the client leaf to the recording performer; its former client call,
writer check and redundant helper check are deleted from this NEXT leaf.
No second decision, polling loop, counter, permit store or receipt decoder.
IMPL-12/13 caution against copying the admission/child mechanism; IDEN-1
separates admission-attempt identity from one actual retained client lifetime.
NRA/refactor-audit guidance informed that ownership, not a new Python family.
These owners are Bash/JQ, not Python AST: no NRA full Python/engine audit or
dynamic-global resolution is claimed. Preserved frozen historical versions
are evidence, not an alternate future compatibility path.

Source controls exercise the real util-linux script PTY with controlled guard
and client leaves, not a live installed scientific MCP. Parent owns the next
installed user-path qualification and future author release. No provider,
native, viewer, catalogue or scientific execution is needed for these controls.
