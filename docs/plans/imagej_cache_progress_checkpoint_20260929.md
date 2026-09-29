# Issue224 cache/progress integration checkpoint

Owner: Lovelace implementation; parent review/integration/installation/live gate.
Fresh distinct source task after lost backend handles, not Retry of an uncertain
call. Read-only verification found original remote206=`6bc71ee5c` and16=`9e205fee`
exactly matching their persistent worktree heads. Only intentional old parent
gitlink difference present. Both original branches and all receipts preserved.

## Exact pair and scope

Parent base current remote main `213439a04ec7e47694cb0aec2127a0e9ca2790c2`
(includes merged218). Child base current/recorded main
`f94bbbe8631a4c78f7ceaec72fb99671b58c9a18`.
Worktree `/home/ts/wt/openhcs-imagej-cache-progress-20260929`, parent branch
`fix/imagej-cache-progress-20260929`, child branch `fix/imagej-cache-root-20260929`.
Eight recorded dependencies initialized locally using the existing source as
object references; no shared environment/source change. Child source commit
`c16b8fc99a07f17e92e5fbf46f312d73cc9c46d7` is published and the exact parent gitlink.

Original cache commits5e656f8/101a6a4 were cherry-picked without unrelated ROI,
Java probe or source selection changes. The policy extension adds first-class
download prohibition; no additional materializer/runtime owner. Broad206/16 stay
open for those remaining changes; the small pair is their authorized integration
checkpoint, not competing implementation. Update originals by normal integration
after the parent merges the small pair, never rebase/reset/force-push.

## Bootstrap and reproducible native admission

Before importing OpenHCS/PolyStore or launching the MCP child, set:

```sh
export POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej
export POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
```

Keep each run's XDG_CACHE_HOME and log roots independent. The existing
OpenHCSProcessEnvironment child projection derives both keys from their PolyStore
owners; McpDevServerSpec.environment already consumes that projection.
Unset root retains existing platformdirs default. Unset download permission keeps
existing policy defaults; explicit permission accepts only true/false.
No copy/archive/download needed on this host. An absent/invalid bundle with false
fails before creating the cache root/lock/staging or deleting any directory.

Source validation uses `/home/ts/code/projects/openhcs/.venv/bin/python`,
OPENHCS_CPU_ONLY=true, PYTHONDONTWRITEBYTECODE=1 and PYTHONPATH to this worktree,
then these recorded dependency src directories: ObjectState, PolyStore,
arraybridge, metaclass-registry, pycodify, pyqt-reactive, python-introspect,
zmqruntime. All are under this same worktree's external directory.

With that explicit source environment, run twice (each new process) with distinct
XDG_CACHE_HOME and the two bootstrap variables above:

```sh
timeout 15 /home/ts/code/projects/openhcs/.venv/bin/python scripts/verify_existing_imagej_bundle.py
```

Executed first/second XDG values were `/home/ts/.cache/agent-scratch/openhcs-cache-proof-first-20260929`
and `.../openhcs-cache-proof-second-20260929`. Neither directory existed or was
created. Both returned the same actual runtime:

- Fiji: `/home/ts/.cache/polystore/imagej/fiji-20260718-0417-linux_x86_64-eb5d70b3ffb6/Fiji`
- Java: that Fiji root plus `java/linux64/zulu21.42.19-ca-jdk21.0.7-linux_x64`
- Source: this worktree's external/PolyStore/src/polystore/imagej_distribution.py
- download_allowed=false, new_cache_entries=0, jvm_started=false.

This is real native bundle materialization/admission, not JVM/MCP/installed proof.
The production policy is used directly, without DownloadForbidden override.
Before/after recursive path inventory unchanged; jpype.isJVMStarted false both
before/after. No bundle contents copied/hashed/archived/downloaded. Shared bundle,
foreign caches, frozen installation and blind receipts remain untouched.

## Executed focused tests and bounds

Guard: RAM14.4GiB available, swap11.1GiB warning, home20.6GiB, root8.6GiB.
No heavy runtime permitted or started. Small provider-free source shard only.
Assert available RAM>=8GiB before imports. Verified OpenHCS, distribution,
ObjectState and metaclass_registry resolve to the new assigned checkpoint tree.
Import OpenHCS before pytest collection. PYTEST_DISABLE_PLUGIN_AUTOLOAD=1;
shell timeout45; pytest.main argv:

```text
--noconftest --import-mode=importlib -p no:cacheprovider -o addopts= -q --tb=short
external/PolyStore/tests/test_imagej_cache_environment.py
external/PolyStore/tests/test_imagej_distribution.py
tests/unit/agent/test_plate_inspection_cold_runtime.py
```

**36 passed,2 warnings in5.14s**, driver peakRSS277712KiB (~271.2MiB), final
RAM13.964GiB. Warnings are unused asyncio configuration with plugins disabled.
14 cache/policy +17 existing distribution +5 parent launch/progress/binding cases.
The fixture-only tests use tiny local verified ZIP responses; the actual shared
bundle proof above is separate and does not use those fixtures.
Existing real in-process FastMCP binding invokes controlled blocking inspection
on the declared worker while canonical capability discovery completes. Existing
heartbeat helper covers terminal success/error without swallowing exceptions.
No real stdio process, listen socket, JVM, GUI or scientific execution in this
shard. All test children reaped; commands terminal. No shared lock taken.
Ruff passes child source/tests and parent tests/proof; both diff checks pass.

## Essential changed-surface catalog review

BOUND-1/2/6: FijiArchiveDistribution.cache_root_from_environment owns bundle-only
boundary decode; ImageJArchiveDownloadPolicy.from_environment owns permission.
Canonical FIJI construction projects both once. Consumer reads typed constructors,
not repeated environment maps. New root input: one existing owner decision, zero
BioFormats/viewer edits. Download permission: one policy decoder/admission method,
shared by missing-bundle preparation and archive/overlay download; no caller fork.

MEMB-2/3: OpenHCSProcessEnvironment derives both dependency-owned key spellings,
McpDevServerSpec already consumes the projection. No independent filename roster,
runtime/default registry or XDG alias. Strict external two-value boolean decoding
is not new runtime-kind dispatch.

IMPL-6/12/13: InspectPlatePathCapability declares heartbeat/thread-safety and
truthful optional runtime mutations. Existing generic binding owns thread offload
and progress; no tool-name switch, job/progress store, polling runner or timeout
inflation. Another suitable synchronous capability needs only its declaration,
not a copied worker. Side effects require mutating=True under existing registry
validation; the prior declaration error was fixed, not the validator weakened.

Coverage: focused changed source/consumer trace, catalog and executed behavioral
checks, no full NRA scan/global proof. No source preparation/ROI semantic delta
in this pair and no claim of Java lifecycle/biological fidelity.

## Remaining acceptance and original receipts

Parent owns merge/install of the exact small pair, then resource-coordinated real
installed stdio plate inspection plus concurrent discovery/heartbeat. No JVM
until that slot; no source/skill/environment installation by this worker. Issue224
remains open until actual affected installed journey passes.
Original206/16 combined **141 passed/26 failed37.12s** remains explicit. Candidate
cause is metadata bootstrap/import order, not proved repaired. After-ROI profile
did not run. Native warm admission and36 source cases do not erase that evidence
or claim preservation/live readiness. Broader source/ROI and real Java/CZI gates
continue in the original drafts. No uncertain calls or scientific input replayed.
