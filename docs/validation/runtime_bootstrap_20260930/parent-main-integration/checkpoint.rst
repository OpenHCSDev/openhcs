PR256 parent integration with current main
=========================================

Parent is the integration owner. Existing feature head
19b647f30c4ee515615aa20a03bf594e9801f7ea was normally merged with main
992a479b118e7054b3137445bb6ec7af4ce0b571 in a fresh persistent detached worktree
``/home/ts/wt/openhcs-bootstrap-integration-20260930``. Merge commit
ac9456f80bdeed67a81ac74d2b7b4801ec5b8e94 has no source conflicts. Publish to
the same existing PR256; no competing implementation or orphan feature branch.
Original Lovelace checkout and all three native attempt directories are retained.

Paired pins and ownership
------------------------

Native PR9 remains at published112c240464df6e81c25b0f97d2b1376d43bbbbc8;
it contains main2c68a114. Metaclass448cdf07 contains mainca0a87e8. The remaining six
dependency declarations are unchanged. Tests use the fresh parent root and
read-only exact child source roots in the original checkout; all nine imports
are independently asserted and printed in both test logs. These are explicit
source imports, not the installed ordinary-import harness.

The review traces connection resolution through OpenHCSZMQConfig, native pair
admission/reservation through TransportEndpoint, process identity through the
original ProcessIdentity, shutdown through its existing operation/mode, and
native writes/spawn through ExecutionRuntimeLaunchPlan. Existing shared
capability declarations generate the MCP routes; no second dispatch catalog.
Applicable NRA/refactor-audit patterns reviewed: IMPL-12/13, IDEN-8, BOUND-2
and TIME-7. This review does not certify the unfinished global ZIP/NRA audit.

Actual source checks and retained failure
----------------------------------------

First command failed at collection because a new source checkout has no compiled
``openhcs.core._tabular_native``. Original source-tests.log/XML are preserved:
exit4,2.37s process,98400KiB RSS. No test passed or runtime was started by it.
Build the two existing declared native extensions with the existing Python3.12
and ``setup.py build_ext --inplace``; no environment/package install or download.
Build completed exit0,3.37s,146744KiB RSS; native-build.log retains the command.

Same source shard, original30s shell bound: **197 passed**, zero skips or
deselections,6.51s tests/7.30s process,265044KiB peak RSS,exit0. Both warnings
are disabled asyncio plugin settings. The readable run-source-check.sh records
exact source paths, plugin/thread limits, Fiji download refusal and
isolated persistent XDG scratch. Collection and corrected outcomes are separate.
Real fixture records and portalocker locks execute; subprocess/network/process
signals and visualizers are controlled. No MCP/native endpoint, JVM, science,
GUI, paid provider or validation-slot allocation occurs in this shard.

Post-test recipe review found that its Fiji root was pinned after isolating
XDG_CACHE_HOME, so that test invocation selected owned disposable cache, NOT
the shared bundle cache. No materialization/download/Java occurred. Preserve
those original receipts and do not claim shared-cache runtime acceptance.
The published recipe now explicitly selects /home/ts/.cache/polystore/imagej
and downloadfalse before isolation. This future resource-only recipe correction
does not change any production source or test assertion; no re-run claimed.

Original authenticated installed agent-comms-ratchet, source SHA256
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562:
main992 -> integrationac9456f80, whole ``openhcs`` root, **5187 metrics, no
positive deltas**,exit0,15.91s/86820KiB. ratchet.json and resource receipt are
retained. It is a changed-path structural ratchet, not a complete global NRA/R1
or biological/live proof. No guard exception or legacy fallback was added.
The native pin is unchanged from the original published188-metric passing
receipt; do not relabel that old receipt as a fresh native run.

Resources, cleanup and delivery boundary
---------------------------------------

20GiB is the owner's warning margin, NOT a hard admission gate. Before these
bounded source checks disk19.5GiB/RAM15.3GiB; after disk19.4GiB/RAM14.6GiB.
Historical swap9.5GiB remains a warning, not an inferred leak or pressure cause.
All build/test/guard handles are terminal. After empty recursive lsof checks,
retired exactly3236KiB owned build-temp/build-lib/test-scratch. Rebuildable
native extension outputs, readable recipe, original failed and passing receipts
remain persistent. No foreign scratch/worktrees/history or active cache changed.

This checkpoint is source-reviewed and ready for serialized parent live
acceptance, NOT merged, installed or live-verified. Erdos's current main992
blind development repeat retains its original deadline and frozen installation,
skill and inputs. Do not install or take its native slot while it runs. No
scientific coaching or candidate replay was supplied. After terminal freeze,
run the actual paired bootstrap/observe/same-handle-close and corrected
valid-volume journey. Preserve first/chained full/reorder/reduced/singleton,
durable images/labels/CSV/source addresses/ROI/projection readback and uncertain
attempt disposition. No optional hosted-CI waiting gate. Full R0/L0/S1-S8 and
the active goal remain unfinished; original BLOCKED S1 is not silently resumed.
