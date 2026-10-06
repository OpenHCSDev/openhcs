Existing-client QA and startup admission
=======================================

Owner decision at main a3e6a15d4, 2026-10-04
------------------------------------------

resource-check.sh applied the startup HOME reserve to every ongoing read/QA.
This is IDEN-7 (a check wider than its question). AgentCapabilitySpec already
owns read_only/mutating/side_effects; it does not promise a memory or disk cost.
No tool-name roster or duplicate resource declaration is appropriate. Existing
operation modes are the harness capability boundary: ongoing is recorded-client
bounded work; full/replacement/bootstrap admit potentially large/new work.

The same resource owner now declares warning/reject disk policy alongside PSI
policy in its existing mode projection. slot-env.sh owns recorded-client custody:
three recorder journals, original first-start clock, active MCP InvocationID and
common-slice identity. Ongoing cannot bootstrap a missing/ended client. The
author launcher changes its existing call from ongoing to replacement. Recorder
startup remains replacement before journals and one retained handle afterward.
Full allocation checks remain strict; no thresholds, clocks or original input
authority are changed. Free-space exhaustion, bad telemetry, real RAM pressure,
expired deadlines, unknown membership and receipt reuse still fail closed.

No per-operation byte requirement can be inferred just from read_only. The
existing packet directs bounded reads/small QA to ongoing and large buffer,
execution/export requests to full, using declared effects and actual request
size. A warning is not an allocation guarantee. Native write failures/UNKNOWNs
remain original evidence. Actual service/path ownership is not weakened.

Source evidence and acceptance boundary
---------------------------------------

Read original slot/projector/JQ/launch/recorder/client/resource consumers and
AgentCapabilitySpec declaration/registry before editing. Existing refactor-audit
AST overlay covered the OpenHCS Python package at 7fb3c09b; no Python production
file is changed. Normal main integration preserved all foreign Gitlinks. Python
AST does not parse Bash or JQ: shell/JQ coverage is semantic reads, caller search,
bash -n and existing whole-family shell controls, not an AST proof of Bash.

Existing resource-family controls exercise below-reserve ongoing QA, dead/missing
recorded clients, startup/full refusal, zero disk, actual RAM failure, malformed
PSI, expired clock, immutable journals and known receipt collisions. They control
external host observations only; no provider/native/viewer is launched. Actual
canonical-FUND admission against a live owned incarnation is the next affected
entrypoint check, not biological acceptance. Original scientific protocols and
frozen source/receipts remain preserved. Any current operational deployment is
a separately recorded intervention, never an unchanged-harness autonomy claim.
