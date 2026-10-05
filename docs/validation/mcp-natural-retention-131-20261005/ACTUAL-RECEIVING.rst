MCP diagnostic repair: issue131 / PR654
======================================

Delivery scope
--------------

The existing diagnostic no longer vetoes calls at an invented 8-GiB host floor,
2-GiB process RSS ceiling, ten-round maximum or 180-second overall quota.
Caller-selected finite rounds/cadence and per-call timeout retain a bounded
workload. Linux availability, swap usage and full PSI are observations on
ProcessMemoryReceipt, not a second admission policy or automatic stop.

Natural end-of-round samples determine the retention slopes. Python's ordinary
automatic GC remains enabled; no explicit GC precedes or interrupts these
samples. Optional final --gc-at-end records separate signed sensitivity deltas.
RetentionMetric annotations own both calculations, including inherited/new
metrics. The strict read-only request admission remains unchanged. Declared
health results are consumed through McpDevToolResult.decoded_payload_as, not
decoded a second time as mappings.

Source and ownership
--------------------

Production pin: 283c2378a, following initial checkpoint bcde628d0. Latest main
49322f10b was normally integrated afterward; neither the diagnostic module nor
its inherited launch module changed. The installed target is honestly pinned to
283c2378a, not relabelled as later main. Foreign gitlinks/keepers were untouched.

Existing audit Package/Repository AST: 710 MCP/runtime/unit modules, zero parse
omissions; related declarations, imports, inherited launch and calls recorded.
Git caller closure names only the existing diagnostic, launch, ownership guard
and unit family as active consumers. Literal Linux accounting is decoded once
inside ProcessMemoryReceipt.capture (BOUND-1/BOUND-2). DiagnosticServerSpec keeps
the original McpDevServerSpec/import-authority lifecycle (IMPL-13); no replacement
launcher, metric roster, codec, quota or runtime store was added.

Original controls and failures
------------------------------

ownership02.log: existing focused AST ownership guard PASS.
controls02.log/time: 13 PASS, 6.76 seconds, peak323940KiB, swaps0. Includes inherited
metric eligibility, strict unknown/bool rejection, read-only mutation rejection,
exact-source child launch, separate natural/GC calculations and acceptance of a
synthetic4-GiB RSS sample with512-MiB available host memory as observation rather
than a veto. Those last figures are a controlled sample, not actual host load.

controls01 failed before collection because repository pytest addopts requested
an unavailable tests plugin. The corrected invocation selected the isolated
installed target and explicit pytest configuration; two cache warnings were
nonfatal. No production guard or assertion was weakened.

live01 failed before any memory sample: the diagnostic's old health reader tried
dataclass_from_mapping on an already-typed result. Original client1720561 and
MCP1720693 exited; JSON/log/time remain unchanged. The owning consumer was fixed
before the explicitly new live02 attempt. No UNKNOWN input was replayed.

Ordinary installation and real MCP
----------------------------------

Private receiving02 ordinary wheel/build/install uses the retained interpreter
and five qualified dependency wheels, no downloads/new environment/shared
installation changes. Build01 terminal0,139.46seconds, peak443660KiB, swaps0.
BYTE-QUALIFICATION.json PASS:920 wheel RECORD entries,817 exact tracked source
files,792 Python files,13 packaged skill files and complete installed RECORD
accounting. Existing ordinary CLI synchronized only the private skills directory.
Wheel SHA256:b967b610dfa8c51f2880c4766505fb07f4ed77a393ebc6898e828dfb387b01bb.

live02 used the real installed diagnostic CLI, DiagnosticServerSpec and MCP
transport: health, first_use and capability search, one warm-up plus three
repeated rounds at0.2-second cadence, followed by one explicit final GC.
Original tool handle94550 terminal0;18.95seconds, time-reported peak396100KiB,
swaps0. All30 typed samples came from MCP1737168 and the exact receiving02
import root. The original session context closed it; /proc1737168 is absent.
No diagnostic client remains, and no native/viewer/science process was adopted.

Natural end RSS:396696,397128,397444KiB. Declaration-derived RSS/PSS/private-dirty
slopes:374KiB/round; process swap slope0. Final explicit GC delta0 for each
declared metric. Minimum observed host availability9190232KiB; maximum full PSI
avg10=1.17. These measurements were recorded, not converted into an invented
pressure cutoff. LIVE-ACCEPTANCE02.json verifies exact natural/GC separation,
source/PID identity, declared calculations and actual process exit.

Remaining original acceptance
-----------------------------

This useful tool repair is not a no-leak finding, a causal explanation of the
stable P0013.78-GB MCP sample, or completion of the original38-minute mixed
request/revision workload. A new synthetic registration must use the ordinary
typed registration path with an actually owned execution endpoint and prepared
native catalog; none was borrowed or launched for this read-only qualification.
No source revision was submitted. The old UNCERTAIN revision remains immutable
and must never be replayed. Planck retains #131 follow-through; Dewey owns any
future actual lane custody. #132/#169 remain separate unfinished obligations.

Original evidence root
----------------------

/home/ts/wt/openhcs-issue-batch-20260929/engineering-mcp-retention-131-20261005

Keep live01/live02 JSON/log/time, controls01/02, AST/caller closure and both
receiving source origins/wheel proofs. receiving19 and every scientific frozen
installation are unchanged. This receipt is source qualification plus the
specified installed diagnostic path, not biological or whole-session acceptance.
