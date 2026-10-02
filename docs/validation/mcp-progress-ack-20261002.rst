MCP request-scoped progress acknowledgements
==========================================

Integration owner: parent agent. Base: main25d56ae3fb9b80acda80f3cf4e1c8667939147eb.
The owner delegates compilation/catalog/kernel placement to the agent on the
other machine. This change owns only MCP declarations and shared client wait.
No compiler, registry preparation, server launcher or kernel location changes.

Existing EndpointStartupStatus callback_scope and MCP
_await_with_declared_progress already relay actual startup phases. Existing
McpDevStdioSession.request is inherited by resident socket sessions. Preserve
these owners, JSON-RPC framing, public progressToken and cancellation/error
disposition; do not add another startup observer, job store or polling loop.

Concrete witnesses: FunctionCatalogCapability and worker-safe submit leaves
declare5s heartbeats, equal to DEFAULT_CALL_TIMEOUT_SECONDS5s. Silence until
that boundary races the reader's idle expiration. Client request currently
starts a full read budget after every message, including unrelated IDs/tokens.
Progress acknowledgements must reach the client before its idle deadline and
renew only their original request. Silence, unrelated traffic and malformed
progress are not acknowledgements. Never replay an uncertain tool request.

Ownership: one declaration capability carries the shared responsive interval;
existing catalog/plate/submission capabilities compose it via their existing
declaration MRO. Existing generated binding keeps its relay algorithm. Decode
progress once into the original SDK ProgressNotification, not a mirrored DTO.
Use the standard asyncio reschedulable timeout around the existing shared
request loop, renewing only a matching progressToken. Existing stdio/socket
reader and response handling remain shared. Do not increase any timeout.
Pattern witnesses: IMPL-12 repeated interval declarations; BOUND-1 repeated
raw progress fields; BOUND-2 original external protocol type already exists.

Acceptance: real server binding emits original phase and subsequent heartbeat;
the actual MCP client survives total duration longer than its idle allowance
while receiving matching acknowledgements. Matching terminal reply/error ends
the original attempt. Wrong-token/unrelated traffic cannot extend silence;
malformed progress rejects at the SDK boundary. Stdio and resident socket
inherit one request wait. Add a new progress-capable declaration without a
consumer change. Preserve all backend operation/compile/cancellation budgets,
affinity restrictions, saved scientific context and held-out boundaries.

Installed/live qualification is separate from source controls. The installed
external SDK inspected here uses a total anyio.fail_after even when callbacks
receive progress. A server notification cannot rewrite a third-party client's
timeout policy. This acceptance concerns the existing OpenHCS dev-client wait;
do not claim arbitrary external clients automatically renew their timeouts.

Executed checkpoint
-------------------

Three original regressions failed: wrong-token progress and wrong-response-ID
traffic renewed the idle allowance; missing progress fields silently succeeded.
Original red6.08s/250.21MiB is retained. The shared client repair uses SDK
ProgressNotification at ingress and asyncio.timeout.reschedule on the matching
token. Its six focused controls pass5.20s/276.35MiB. The legacy persistent-client
fixture returned an incomplete health record, rejected by current declared
output decoding even though its call succeeded. Use the original health binding
to generate that fixture; do not loosen production decoding.

Existing startup/MRO/concurrency/cancellation controls:13 pass6.25s/280.17MiB.
Real generated FastMCP binding, actual endpoint callback scope, SDK Context and
unchanged wire transports now cover initialize/list-tools, cold success,
original terminal failure and warm reuse on one session. Controlled service
work lasts2.4s per cold call while the client idle allowance is1.6s. Real socket
journey passes10.31s/277.75MiB; fresh stdio child journey passes13.62s/552.41MiB
including child teardown. The original stdio fixture imported ZMQ before source
activation and failed the genuine stale-external guard; importing OpenHCS first
repairs the fixture, preserving that original failed receipt.

An initial combined test invocation exceeded its512MiB RSS budget7.07s; serial
shards replace that resource-heavy invocation, not its assertions. All original
logs and command receipts remain under the parent's persistent
s1-installed-20261001/mcp421-* evidence directory. Two pre-existing pytest
configuration warnings remain when plugin auto-discovery is disabled.

ProgressAcknowledgedCapability owns the1s interval once, composed by the five
existing worker-safe catalog/plate/submission families. The original generated
consumer, endpoint lifecycle callback, JSON-RPC framing and socket inheritance
are unchanged. The main-thread-affine source-session leaf remains unchanged;
this patch does not make its blocking work thread-safe. No timeout increased,
new poller, alternate startup observer, job store or transport schema added.
Compilation and kernel placement remain with the other machine's owner.
