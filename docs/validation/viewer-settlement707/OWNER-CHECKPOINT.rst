Viewer settlement707: original-owner integration checkpoint
==========================================================

Integration owner: Dewey. Singer contributes read-only engineering diagnosis
to this same issue and branch, not another settlement implementation.
Branch: fix/707-settlement-custody-20261005, based on merged c808c0f667.
This checkpoint is investigation, not an implemented or accepted runtime fix.

Original witness remains immutable
----------------------------------

BBBC013_FRESH20_88 uses receiving20 source396383e443d9b9513ddf624943ea1cb7de39ded6.
Its original output root is
/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-fresh20-88-after-retina19-20261005/BBBC013_FRESH20_88/author-workspace/output.
Native log runtime/data/openhcs/logs/openhcs_zmq_server_port_6020_1791239386809358017.log
lines1923-1953 records execution f357d84e-f786-47be-9a91-c130776a313a FAILED
at settlement after six well tables and two PLATE summaries materialized.
runtime/mcp.stdout records the subsequent selective-retirement refusal at99850:
Cannot retire layers during active settlement.
runtime/t04_viewer_state.json has154 mounted routes and no state errors.
Per-route pending_update=false does not establish settlement terminality:
begin_settlement drains pending updates into the settlement's retained tuple.
No original client, job, request, scene, package or receipt is changed here.

Additional read-only evidence
----------------------------

The exact retained viewer PID1944030 has a command bound to receiving20 and
the original6021 viewer log; ps start time is2026-10-05 18:36:54 local.
A single py-spy dump --pid1944030 --native succeeded without a new viewer
client or callback injection. MainThread was idle in the Qt5 event loop at
napari_viewer_server.py6947. Control thread1944160 was polling at6359;
data thread1944163 was polling at6279. Neither an executing display mutation
nor a blocked control response was on that instantaneous stack. This does
not establish their earlier state or identify the stranded claimed route.
The viewer log contains acknowledgement send failures but no determining
settlement callback traceback. Old707 control-pump starvation remains a
source risk, not the proven cause of this receiving20 witness.

Existing ownership and consumers
-------------------------------

NapariLayerRouteStateStore owns the transition from queued updates to the
settlement and serializes intake/retirement on its original lock.
NapariLayerSettlementState owns the claimed route, native work-unit entry,
progress, completion and failure. Its require_terminal protects retirement.
NapariLayerDisplayPipeline claims and schedules each Qt callback, advances
handler-owned NapariLayerDisplayWork and calls the settlement completion or
failure owner. NapariSettleControlMessageAction projects existing progress
from the transport thread, or starts settlement on Qt when absent.
NapariControlTransportPump owns socket replies and accepted Qt requests.
ManagedViewerLifecycleMixin consumes the typed progress; the compiled plate
execution converts settlement refusal into the original execution failure.
NapariLayerRetirementControlMessageAction delegates to the existing component
coordinator and route retirement boundary. Those protections remain intact.

Next implementation and acceptance
---------------------------------

Resolve the claimed-callback scheduling/completion/failure lifecycle across
these existing owners, including ordinary debounced work handed into a
settlement. Do not infer completion from mounted layers or empty queues.
The patch must remove any lost/competing lifecycle decision in place; it must
not clear claims from a timeout, relax require_terminal, increase timeouts,
introduce another progress store or install into active scientists.

After coherent source changes, batch controls for callback handoff, bounded
multi-unit work, callback failure and a genuinely executing mutation. Run a
bounded installed Qt/control-path case with concurrent progress and state
observations, followed by exact selective retirement of terminal routes.
Verify retained survivor source/producer identities and successful buffer
release. Keep original707 failures and current T06 streaming-disabled science
distinct. No scientific replay, restart or biological guidance is authorized
by this engineering checkpoint.

Fleet and checkout custody
-------------------------

All four original science author scopes were active at this readback:
BBBC013_FRESH20_88, H003_FRESH20_89, BBBC007_FRESH19_95, P001_FRESH20_96.
Host availability was6.6GiB, memory PSI some/full avg10 .22 and avg60 .56;
no additional native runtime, build or author was started.
The owned finished909 checkout was reused on the branch above. Eight foreign
gitlinks and four retained untracked validation directories were preserved.
Current-main runtime and operations sources match the preceding checkout;
no active operations backer was edited or installed package changed.
