## Working source checkpoint for #251

Adds explicit typed owned-runtime bootstrap and read-only handle observation
through existing declaration-derived MCP/CLI and RuntimeServerService. Extends
the canonical native client startup owner, never `connect()` attach/replacement.
Native launch plan path admission precedes spawn; returned PID+creation-time
handle survives pending/uncertain observation. Startup does not warm catalogues
or submit source. First-use/custom guidance is coherent and QA/bounds preserved.

Paired dependency drafts: [ZMQRuntime9](https://github.com/OpenHCSDev/ZMQRuntime/pull/9)
exclusive startup/process identity at729e890, and metaclass-registry non-creating
cache path projection at448cdf0 (link added on publication).
Parent remains integration/install/live owner; frozen source/skill/runtime untouched.

Source evidence: **62 passed, 2 actual MCP cases deselected, 12.02s, exit0**.
Verified source imports and focused nested handle/path/foreign/uncertainty/native
readiness/declaration projection plus unchanged complete QA/context bounds.
No native/MCP/GUI/JVM was launched. No installed/live/performance proof claimed.
Receipt and actual pattern review: [runtime_bootstrap_20260930.md](runtime_bootstrap_20260930.md).

Remaining: paired review/pins, endpoint-pair concurrency/uncertainty hardening,
released serial slot for full synthetic startup -> prep -> registration ->
compile/execute -> supported owned cleanup, then parent installed entrypoint
acceptance. References #251; **not Closes** pending actual acceptance.
