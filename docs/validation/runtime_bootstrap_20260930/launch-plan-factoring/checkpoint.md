# PR256 source-only launch-plan owner continuation

Implementation/test commit: `1f332d1616a5eab4acdd9ebf17f929befb5addc5`.
Normally integrates main `546edd57a0112e406ff8b59c8f938bf4cc01e642`.
ZMQRuntime stays `28d9ed6a0121ebb524ae37fd97de5355308bda7f`; metaclass-registry
stays `448cdf07e0a0b513a9c9a8f67e896f601da11771`. No dependency cutover.

## Owner move and crossings

The existing ExecutionRuntimeLaunchPlan now resolves its own destination fields.
The former resolver body is deleted from ZMQExecutionClient. Its existing cache
still retains the same plan for path admission and canonical spawn; the existing
spawn reset/consumption and process lifecycle remain unchanged. This is an owner
relocation with a bounded new-case improvement, not whole-class decomposition:
adding a launch destination previously changed the plan's fields/writable-path
projection AND the client's resolver; now those edits belong to one declaration.
It does not consolidate several launchers or eliminate every large-class cause.

Current edit set: `openhcs/runtime/zmq_execution_client.py`,
`tests/unit/agent/test_owned_runtime_bootstrap.py`, and these receipts.
RuntimeServerService is READ-ONLY for this checkpoint. Parent owns integration
and gitlink cutover; Dirac owns ACK/viewer transport/config work. No crossing
edit or agreement with an unidentified broader archive author is claimed.
Parent's R0/L0/experimental-analysis claims are disjoint. BLOCKED S1 is unchanged.

## Actual bounded checks

Explicit worktree plus all eight recorded submodule src directories in
PYTHONPATH; `/home/ts/code/projects/openhcs/.venv/bin/python` only. Verified
actual imported openhcs, zmqruntime, polystore, metaclass_registry and
python_introspect paths are under this tree. CPU-only, thread limits1,
Fiji shared existing root and downloads false; no install/environment change.

Command tail (30s shell bound):

```sh
python -B -m pytest --noconftest -o addopts= -q \
  tests/unit/agent/test_owned_runtime_bootstrap.py \
  --basetemp=docs/validation/runtime_bootstrap_20260930/launch-plan-factoring/pytest-b \
  --junitxml=docs/validation/runtime_bootstrap_20260930/launch-plan-factoring/source-tests-b.xml
```

PYTEST_DISABLE_PLUGIN_AUTOLOAD=1. Result: **25 passed, 0 skips/deselections,
3.16s; process3.72s, peak246212KiB, exit0**. Two warnings are disabled
asyncio plugin configuration. Spawn and endpoint probes intercepted by existing
source fixtures; no native/MCP/GUI/JVM/provider/scientific dispatch.
The first run failed before fixture setup because the basetemp parent did not
exist:4 passed/21 setup errors/2.71s, process6.19s/409816KiB/exit1. Its original
`source-tests.xml` remains unchanged; the passing result uses a separate XML.
No production or assertion workaround was needed for that allocation error.

## Pattern review and new-case witnesses

- IMPL-12/IMPL-13: exactly one destination-resolution procedure, now on the
  existing launch-plan declaration. No second launcher/cache/startup store;
  startup reservations and process lifecycle retain original native ownership.
- BOUND-2/TIME-7: resolve the real TransportEndpoint.port_pair and transport
  declaration, original XDG functions, CustomFunctionManager storage and
  metaclass cache path. No copied default/path registry or consumer mode switch.
  TCP and IPC tests change namespace, control offset1700 and IPC naming through
  the existing configuration. Every projected path matches those original
  owners; the fixture directory remains empty and spawn is never called.
- IDEN-8: existing bootstrap/close/changed-incarnation/uncertainty cases still
  pass. This edit does not change ProcessIdentity, lifecycle requests or fields.
- AGENT-4/AGENT-6: class size reduction is not an architecture completion claim.
  Existing plan caching test proves resolution occurs once and returns the same
  admitted object; no mixin extraction sharing a giant self was introduced.

Focused original packaged GodClassExcess.snapshot/align on ONLY the two owner
modules below, authenticated byte-for-byte against ratchet commit
`3b03785f45df2ef5dc62ba6aed99294192ecbb01`. Imported from the existing
`/home/ts/wt/comms-presentation-source-revision-20260930/src` with already
available Python3.14.2. No copied detector, tool installation or whole-repo scan.

| Declaration | main546 excess | prior local excess | current excess | growth vs main |
| --- | ---: | ---: | ---: | ---: |
| ZMQExecutionClient |181|213|190|+9|
| RuntimeServerService |0|15|15|+15|
| ExecutionRuntimeLaunchPlan |0|0|0|0|

The original complete ratchet failure (+32/+15) is preserved. This scoped
measurement is NOT a passing full ratchet, R1 scan, all-detector NRA audit,
installed check or native acceptance. RuntimeServerService and residual client
growth remain owned archive L0/S-surface work; shared-service extraction needs
crossing coordination, not a superficial move to evade the measure.

## Resource and live boundary

Fresh guard:critical, swap16.4GiB, RAM18.3GiB, /home25.5GiB. It did NOT pass.
Only the provider-free bounded source checks above ran; no heavy allocation or
validation slot was taken. Attempts01/02/03 retain their original inputs and
dispositions. Attempt03 is terminal accepted=false, exact-owned cleanup proved;
no fourth attempt, source-bearing replay, installation or managed skill change.
Full valid 3D compile/execute/readback and installed acceptance remain pending
noncritical resource admission and a distinct authorized finite live journey.
