## Working source checkpoint for #251

Adds explicit typed owned-runtime bootstrap and read-only handle observation
through existing declaration-derived MCP/CLI and RuntimeServerService. Extends
the canonical native client startup owner, never `connect()` attach/replacement.
Native launch plan path admission precedes spawn; returned PID+creation-time
handle survives pending/uncertain observation. Startup does not warm catalogues
or submit source. First-use/custom guidance is coherent and QA/bounds preserved.

Paired dependency drafts: [ZMQRuntime9](https://github.com/OpenHCSDev/ZMQRuntime/pull/9)
exclusive startup/process identity, and [metaclass-registry1](https://github.com/OpenHCSDev/metaclass-registry/pull/1)
non-creating cache path projection at448cdf0. Exact gitlinks are committed.
Parent remains integration/install/live owner; frozen source/skill/runtime untouched.

Source evidence: **66 passed, 2 actual MCP cases deselected, 11.85s, exit0**,
peak280400KiB. Initial62-pass checkpoint receipts retained.
Verified source imports and focused nested handle/path/foreign/uncertainty/native
readiness/declaration projection plus unchanged complete QA/context bounds.
No native/MCP/GUI/JVM was launched. No installed/live/performance proof claimed.
Receipt, actual pattern review and focused census:
[runtime_bootstrap_20260930.md](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930.md).

Source hardening includes both-address pre-bind reservations, post-spawn
uncertainty handles, expired-deadline no-spawn, real offline CLI projection and
authoring/core exposure. Normally integrated current main32d070c26.
Exact dependency pins: ZMQb7f6f5d22 and metaclass-registry448cdf07.
Scoped candidate census: no string/type dispatch/arms, raw-key, codec or foreign
absence-probe growth. Native reservation JSON decode/uncertainty catch/long
startup method are reviewed leads, not a global clean claim.

Remaining: paired review, cross-process native endpoint-pair/uncertainty evidence,
released serial slot for full synthetic startup -> prep -> registration ->
compile/execute -> supported owned cleanup, then parent installed entrypoint
acceptance. References #251; **not Closes** pending actual acceptance.
