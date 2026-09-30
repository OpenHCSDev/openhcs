# Execution progress annotation dependency checkpoint

Issue: https://github.com/OpenHCSDev/openhcs/issues/243
Dependency fix: https://github.com/OpenHCSDev/ZMQRuntime/pull/8

Pin the merged ZMQRuntime `0f9e840a9ed526f0a2b87a660393f5b7c34fc9eb`.
The progress declaration imports its existing recursive `WireValue` type so
ordinary annotation evaluation and nested OpenHCS job-status decoding work.
There is no alternate decoder, schema, protocol or runtime store.

The dependency owner retained the original failures: seven regressions failed
with `NameError: WireValue` before the fix. Thirteen focused tests passed after
it, including real OpenHCS nested status DTOs, serialization round trips and
immutable/detached progress observations. Coordinator reviewed the production
diff and regressions. This is focused source evidence, not a global proof.

The actual existing installed OpenHCS entrypoint, from outside source with
ordinary imports, resolves OpenHCS and ZMQRuntime into this checkout and its
bundled dependency. `get_type_hints(ExecutionProgressObservation,
include_extras=True)` now succeeds. Existing ZMQRuntime distribution metadata
remains 0.2.24; no standalone distribution downgrade or registry publication
is part of this change.

Installed attempt06's original compile was independently observed COMPLETE;
its decoding failure and receipt remain preserved. No original operation was
replayed. Full installed registration/compile/execute/delayed-receipt acceptance
is a new bounded attempt07 and remains pending at this checkpoint. Blind
scientific authoring remains unstarted until that acceptance passes.
