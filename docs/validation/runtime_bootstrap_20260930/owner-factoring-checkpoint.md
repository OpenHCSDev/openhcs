# PR256 existing-owner behavior closure

Production/test head `9cb7703d2`, based on normally integrated main
`7d0ce5e68b8263346849ddb7ac82fdbef3876a0b`. Paired native PR9 remains
`28d9ed6a0121ebb524ae37fd97de5355308bda7f`; metaclass PR1 remains448cdf07.
Dirac's independently merged ACK checkpoint is not adopted by a worker pin.
Parent owns coherent dependency integration, installation and native acceptance.

## Owners, deletion and new cases

The admitted ExecutionRuntimeLaunchPlan previously declared native destinations
and write admission, but ZMQExecutionClient still independently constructed and
consumed the launch command, runtime directory, log and journal. The plan now
owns materialization and the existing process-policy invocation. Deleted the
client's procedure in place; its required native spawn hook only consumes the
exact admitted plan and retains the existing journal/cache lifecycle.

This is not a second launcher or process supervisor. BackgroundProcessLaunchPolicy
still owns platform launch flags, MemoryType the inherited environment,
OpenHCSRuntimeImportAuthority the interpreter/module source, ConfigDocumentAuthority
the configuration source, and the original native ExecutionClient the held-lock
reservations, child incarnation and post-spawn uncertainty. No new fields/store,
copied defaults, retry or native lifecycle implementation was introduced.

New-case witness: adding another owned launch destination formerly required
the plan's declaration/admission plus client-side materialization/command use
(two behavior owners). Those edits now belong to the existing plan alone.
TCP/IPC x persistent/nonpersistent cases prove selected paths, exact child config,
interpreter/module flags and launch-policy selection through that declaration.
The native spawn hook has no directory/log/argv/config knowledge to update.

RuntimeBootstrapState previously declared correlated progress/readiness/aliveness
fields, while RuntimeServerService constructed their relationship from native
journal and heartbeat facts. The existing result declaration now owns that pure
projection through from_observation. Deleted the service's decision body; it
retains path admission, exact-incarnation liveness, canonical journal reading
and the bounded heartbeat, and passes already-typed observations to the owner.
The result factory performs no I/O, warming, spawn, shutdown or raw decode.

New-case witness: an additional public derivation from the existing journal/
heartbeat facts previously required edits to the result declaration and service
decision body (two owners). It now changes the result owner only. Acquiring a
genuinely new external observation would still require the I/O owner; no claim
that every future feature needs one edit. Tests derive all native startup phases
from the existing enum and prove they remain activity, not readiness. Exact
incarnation/role proof remains necessary; lost heartbeat retains pending identity,
and a proven terminal child is distinct from unknown process state.

Applicable catalog: IMPL-13/IDEN-8 preserve canonical process and incarnation
ownership; BOUND-2 uses existing typed observations rather than raw records;
IMPL-12 deletes the replaced procedures; AGENT-6 distinguishes these owner
decisions from arbitrary service/mixin extraction. No new capability family,
forwarding service, registry, codec, string/type switch or compatibility path.
Wire fields, native timeouts, transport resolution and handle identity unchanged.

Crossings: only three owned production files (runtime/zmq_execution_client.py,
agent/dto/execution.py, agent/services/runtime_server_service.py) plus bootstrap
tests and the existing launch-contract test. No shared native config/client,
ACK/viewer files, parent R0/L0 files, projection fixture or installed skill edits.
The older process-contract assertion omitted the already-existing -B interpreter
flag; it now checks that exact flag too, rather than weakening interpreter proof.
The separate archive author is still unidentified; BLOCKED S1 is not resumed.

## Actual source checks

Verified imports: openhcs, zmqruntime, polystore, metaclass_registry and
python_introspect all under this isolated tree. Existing Python3.12 executable
/home/ts/code/projects/openhcs/.venv/bin/python, -B, explicit PYTHONPATH root plus
all eight recorded child src directories, thread1/CPU-only, shared Fiji cache,
downloads false, pytest plugin autoload disabled. No new environment or install.

Within a30s shell bound:

```sh
python -B -m pytest --noconftest -o addopts= -q \
 tests/unit/agent/test_owned_runtime_bootstrap.py \
 tests/unit/test_zmq_execution_server_process.py \
 tests/unit/agent/test_agent_services.py::test_execution_connection_spec_owns_zmq_endpoint_projection \
 --basetemp=docs/validation/runtime_bootstrap_20260930/owner-factoring-pytest-b \
 --junitxml=docs/validation/runtime_bootstrap_20260930/owner-factoring-source-tests-b.xml
```

**100 passed, 0 skips/deselections,4.74s; process5.39s/257852KiB RSS/exit0.**
Initial72-case checkpoint4.41s/process5.01s/259080KiB/exit0 separately retained
in owner-factoring-source-tests.xml before all-phase and failed-Popen closure.
Two warnings are disabled asyncio plugin configuration. Ruff formatting and
undefined-name checks and git diff --check pass.

Popen, network probes and shutdown are intercepted; no actual native/socket,
MCP/JVM/GUI/provider launch. Actual native startup reservation code is exercised
by retained source controls, including locality/path denial before any spawn,
same-route start/observe/close and post-spawn uncertainty. Failed plan consumption
does not resolve another plan, retry Popen or drop the original journal identity;
the materialized log stream closes even on child-creation failure.

## Original packaged structural ratchet

Authenticated original debt_ratchet.py from agent-comms commit
3b03785f45df2ef5dc62ba6aed99294192ecbb01, SHA256
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562.
Used the existing package from comms-presentation-source-revision-20260930/src,
not a copied detector/CLI. Existing Python3.14,30s shell bound:

```sh
python3.14 -B -m agent_comms.debt_ratchet --root openhcs \
 --base 7d0ce5e68b8263346849ddb7ac82fdbef3876a0b --head 9cb7703d2
```

**PASS, exit0,15.83s/87520KiB RSS;5,159 projected metrics, zero positive deltas.**
The tool's ordinary changed-production comparison includes all ten PR256 source
paths and its original complete-root GodClass inventory. Full JSON and resources
in owner-factoring-ratchet.json and owner-factoring-ratchet-resources.txt.
Client GodClass excess181 ->139 (delta-42); service0 ->0. Existing plan and result
declarations remain below the500-line threshold. All other deltas are zero.
This closes the own-PR +8/+15 structural growth remainder, not existing client
debt or complete class decomposition. Original failed +32/+15, intermediate
+9/+15 and +8/+15 receipts remain unchanged. Not an R1/global/all-detector NRA
proof, installed validation or scientific correctness claim.

## Limits and resource disposition

Guard criticalswap16.3GiB, RAM18.3GiB, /home24.4GiB. No waiver, native/heavy
allocation, parallel fleet or validation-slot claim. Only bounded serial
provider-free source checks and the87MiB original structural script ran.
After both pytest processes terminal and lsof empty, removed only owned generated
test directories owner-factoring-pytest (892KiB) and owner-factoring-pytest-b
(1.5MiB). Rebuildable; both XML files retained. Original attempts01/02/03,
registered sources, uncertain dispositions and frozen installed source untouched.

Remaining: successful valid3D compile/execute/full strict durable readback and
parent installed entrypoint acceptance after noncritical headroom. No new live
attempt, guard exception, shutdown replay, global clean claim or issue closure.
