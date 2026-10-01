Managed render-complete snapshots and spatial QA, issues363/366
==============================================================

Integration owner: Singer/Codex managed-viewer QA sidecar. Source base791650087.
Persistent source: /home/ts/wt/openhcs-render-complete-snapshot-20261001 and
/home/ts/wt/pyqt-reactive-render-complete-snapshot-20261001. Paired dependency
a9e6745 (draft PyQT-reactive10), extended from the original3437d1c gitlink.
OpenHCS draft364 closes363 and366; neither draft is installed or live accepted.
Closes #363. Closes #366. Paired PR: https://github.com/OpenHCSDev/PyQT-reactive/pull/10.

Required relation
-----------------

A successful mutation acknowledgement and a nonempty immediate capture do not
prove completion of the requested native canvas render. A render-complete
capture must arm before requesting a new native frame and capture only after
the renderer's own completion event, or fail with its bounded observation
evidence. The timeout is a failure bound, never a settling heuristic.

Semantic image Y/X bounds must address the axes declared by the original
ImagePayloadMetadata.spatial_axes_yx(source_data), projected through the
existing leading aggregate selection. The generic raw-array-slice contract
continues to address trailing array dimensions. Nonspatial/color dimensions
remain full, and the original max_array_elements omission bound still applies.

Original parent evidence
------------------------

Installed OpenHCS3d58912, manualraw STACK ch1+2 and registrygamma1identity
streamed LAYER in the same viewer. Transcript/input under
/home/ts/wt/openhcs-issue-batch-20260929/paired350-installed-20261001.
Black immediate frames: captures/identity/ch1/result/20261001T114832886256Z_
napari_5992_OpenHCS_Napari_Visualization.png and ch2/result/114833354026Z.
Valid later same-coordinate frame: ch1/result-settled/114930892910Z.
Original failures and artifacts stay untouched. No scientific rerun.

Additional owner-verified settled Ch2 control: result-settled/
20261001T120404041673Z_napari_5992_OpenHCS_Napari_Visualization.png,
SHA0f75aa42e264d1d6071244861daefe646000eaff1677bf213dce875c363cc5f2:
five dim matching spots at fixed window47..26067, gamma1, unchanged camera.
Route-local channel0 maps to aggregate point1; channel1 was correctly rejected.

Issue366's original RGB witness and acceptance remain at the same parent root,
RGB-SPATIAL-SAMPLE-DEFECT.rst. A64x64x3 image with y16/h16/x0/w64 was wrongly
sampled as64x16x3 with rows0..64, columns16..32, instead of16x64x3.

Ownership and crossings
-----------------------

BOUND-2: extend WindowSnapshotCaptureSpec and WindowSnapshotFrameCondition,
not a second DTO or caller-owned readiness flag. IMPL-12/13: the common
observation lifecycle belongs to QtWindowSnapshotService and its owning
observation ancestor. Renderer leaves supply native completion/request hooks.
No concrete-consumer switches, event-loop replicas or production painters.

IMPL-2: condition members own observation construction/admission; consumers
call the nominal condition. IMPL-12/13: lift the original flash observer's
timer, capture, receipt, error and cleanup into _WindowSnapshotObservation,
then retain small flash/render hooks. This removes the independent flash
lifecycle in place, not a second loop beside it. A late renderer signal cannot
overtake its queued timeout: admission checks the same original deadline.

The original NapariViewerPayloadProjection.array_value_sample remains the one
clipped slicing algorithm. ViewerPayloadControlOptions supplies raw axis
selection; ViewerImageSpatialSampleControls supplies only a metadata-driven
axis hook and cooperative ancestor validation. BOUND-2: no rank/size-based RGB
guess bypasses ImagePayloadMetadata. There is no new sampler or layout roster.

Genuine MI: NapariScreenshotControlMessageAction composes registered control
dispatch with ViewerWindowSnapshotService -> QtWindowSnapshotService; its
super() chain reaches the original capture algorithm. The Qt render-owner
fixture composes independent widget-access, completion and request capabilities
with cooperative initialization. These bases supply behavior, not markers.
MEMB-1/2/5: existing AutoRegisterMeta owns control discovery and the existing
capability input_contract owns MCP discovery; capture-field projections derive
from dataclass declarations rather than enumerated field copies.
The failure reply inherits ControlErrorResponse's fields and canonical wire
projection, extending it via cooperative super() with the typed observation.
It replaces raw error-record mutation rather than hiding it behind a facade.

PR358 startup/connect excluded. Dewey's PR365 owns general DTO serialization,
pipeline and render authoring; server.py and those files are untouched.
The owner's explicit 2026-10-01 reassignment authorizes this sidecar to own
narrow snapshot/payload-sampling integration in napari_viewer_server.py on its
isolated branch. This supersedes the earlier parent-only snapshot sentence.
PR351 production source is frozen; parent writes its acceptance docs/archive
and guards only, with no competing Napari patch expected. No axis/source-binding,
startup, navigation or display-settlement implementation changes are included.
Installed/native acceptance remains exclusively parent-owned, after351.

New-case behavior
-----------------

An independently composed native paint owner plus a counting request capability
requires only its own hooks/MRO declaration: unchanged observation consumers
capture exact painted pixels once. A new control action requires only its own
registered message declaration and handle hook: the unchanged accepted queue
delivers its reply. MiddleColorMetadata declares spatial_axes_yx=(0,2): the
unchanged sampler crops8x3x10 to3x3x5 and preserves the middle color axis.
Each experiment executes behavior; inheritance alone is not acceptance.

Changed source paths
--------------------

OpenHCS: agent/dto/viewer.py; agent/services/viewer_window_service.py;
runtime/viewer_controls.py; runtime/viewer_snapshot.py;
runtime/napari_viewer_server.py; external/pyqt-reactive gitlink.
Tests: unit/agent/test_viewer_render_snapshot.py; unit/agent/test_agent_services.py
(the original fake immediate contract now requests immediate explicitly);
unit/test_napari_render_snapshot.py; unit/test_viewer_spatial_sample.py.
PyQT-reactive: services/window_snapshot.py; tests/test_window_snapshot.py;
docs/architecture/window_snapshot.rst.

Validation and resources
------------------------

One source shard at a time, oneCPU/thread pools1, combined RSS512MiB,60s,
plugin/provider-free. Existing real Qt fixture mandatory. No runtime launches,
installations, downloads, scientific execution, heavy locks or live processes.
Resource check: warning only, RAM18.3GiB, home8.9GiB, swap13.6GiB used.
No parallel fleet or large test is started. Owned disposable scratch will be
/home/ts/.cache/agent-scratch/render-complete-snapshot-363-20261001;
archive evidence here before removing that exact owned directory.

Latest bounded shards, all plugin/provider-free with CPU0 affinity, CPUQuota100%,
MemoryMax512M and MemorySwapMax0, shell timeout60s:

* qt-final-selected.log:13 passed,1.45s elapsed,127876KiB peak. Existing real
  qapp/rendered_canvas and observed_form fixtures, including original flash
  painter, late native completion, deadline, destruction and MI/new-case.
* spatial-final.log:16 passed,8.90s elapsed,482548KiB peak. Real ViewerModel,
  asymmetric nonzero gray/RGB crops, clipping/empty bounds, original two
  streaming-handler sampling tests, missing layout, color-axis retention and
  max bound. Semantic expected16x64x3; raw expected64x16x3.
* queued-final.log:4 passed,7.16s elapsed,502964KiB peak. Original accepted
  control queue, canonical pickle serializer, registered action, real Qt paint
  and ViewerModel; no socket or server/application startup.
* contracts-schema.log:14 passed,5.43s elapsed,289568KiB peak. Nominal MCP
  input contract/signature, capture-field projection, missing/stale/foreign
  receipt rejection, error receipt retention, DTO roundtrip, real Qt managed
  reply, original immediate/malformed service contracts, and strict original
  AgentResourceRef schema decoding (wrong types and unknown fields rejected).

First failures are archived, not overwritten: contracts-first (missing reused
native extension), contracts-checkpoint (wrong source dependency import path),
spatial-first (factory default validation and missing fixture title), queued
first/second/third (fixture endpoint initialization and teardown), qt-final
(overbroad selector included four qtbot cases without the forbidden plugin).
The explicit plugin-free selector passes; those qtbot cases remain unexecuted.
An early pair of small shards overlapped on CPU0; their conservative summed
peak395MiB stayed below512MiB. Subsequent shards ran sequentially.

R0's first committed-source review (r0-final.log,23.76s/87632KiB) found one
new raw string-key subscript at error-receipt mutation and five added lines in
the already-large ViewerWindowService. The replacement for the raw mutation is a
nominal ControlErrorResponse subclass with declaration-derived inherited
fields and cooperative wire projection; the actual queued-destruction check
passes through the existing canonical serializer. The repeated snapshot
resource-field hand mapping is removed in favor of dataclass_from_mapping
against the original AgentResourceRef. Receipt shape validation reuses the
existing _optional_typed boundary mechanism, not another bespoke type guard.
The second R0 failure is retained as r0-closed.log; it cleared the raw mutation
but still exposed service growth, which prompted the schema-owned correction.
The pinned original detector is3b03785f45df2ef5dc62ba6aed99294192ecbb01,
with a clean read-only worktree. Full production deltas include all five changed
OpenHCS Python paths and the paired pyqt-reactive source change; no path omitted.

This receipt is a focused source/ownership review, not a completed global NRA
scan or equivalence proof. The user's source-only limits govern validation;
no native application, MCP server, install, build, download or scientific run.
OpenHCS root conftest is intentionally excluded because it owns runtime cleanup.
Installed acceptance must repeat the original channel isolation/navigation and
same-coordinate snapshot journey, inspect render receipts and exact RGB samples
through the actual MCP entrypoint, retaining the original immediate failures.

Status
------

Draft source-only checkpoint. Native OpenGL swap/composition and installed MCP
acceptance are parent-owned and outstanding; no source check claims them.
