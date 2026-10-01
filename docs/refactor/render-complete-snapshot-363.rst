Managed render-complete snapshots, issue363
==========================================

Integration owner: Codex render-complete snapshot sidecar. Source base791650087.
Persistent source: /home/ts/wt/openhcs-render-complete-snapshot-20261001 and
/home/ts/wt/pyqt-reactive-render-complete-snapshot-20261001, dependency3437d1c.

Required relation
-----------------

A successful mutation acknowledgement and a nonempty immediate capture do not
prove completion of the requested native canvas render. A render-complete
capture must arm before requesting a new native frame and capture only after
the renderer's own completion event, or fail with its bounded observation
evidence. The timeout is a failure bound, never a settling heuristic.

Original parent evidence
------------------------

Installed OpenHCS3d58912, manualraw STACK ch1+2 and registrygamma1identity
streamed LAYER in the same viewer. Transcript/input under
/home/ts/wt/openhcs-issue-batch-20260929/paired350-installed-20261001.
Black immediate frames: captures/identity/ch1/result/20261001T114832886256Z_
napari_5992_OpenHCS_Napari_Visualization.png and ch2/result/114833354026Z.
Valid later same-coordinate frame: ch1/result-settled/114930892910Z.
Original failures and artifacts stay untouched. No scientific rerun.

Ownership and crossings
-----------------------

BOUND-2: extend WindowSnapshotCaptureSpec and WindowSnapshotFrameCondition,
not a second DTO or caller-owned readiness flag. IMPL-12/13: the common
observation lifecycle belongs to QtWindowSnapshotService and its owning
observation ancestor. Renderer leaves supply native completion/request hooks.
No concrete-consumer switches, event-loop replicas or painter implementations.

PR358 startup/connect excluded. Dewey owns general DTO/pipeline/render
authoring; snapshot-only changes require an explicit claim. PR351 files remain
frozen. Parent owns any narrow Napari snapshot integration in its shared file.
Installed/native acceptance remains exclusively parent-owned.

Validation and resources
------------------------

One source shard at a time, oneCPU/thread pools1, combined RSS512MiB,60s,
plugin/provider-free. Existing real Qt fixture mandatory. No runtime launches,
installations, downloads, scientific execution, heavy locks or live processes.
Resource check: warning only, RAM18.3GiB, home8.9GiB, swap13.6GiB used.
No parallel fleet or large test is started. Owned disposable scratch will be
/home/ts/.cache/agent-scratch/render-complete-snapshot-363-20261001;
archive evidence here before removing that exact owned directory.

Status
------

Draft source-only work. Not merged, installed or live-verified.
