Managed render-complete snapshots and spatial QA, issues363/366
==============================================================

Integration owner: Singer/Codex managed-viewer QA sidecar. Source base791650087.
Persistent source: /home/ts/wt/openhcs-render-complete-snapshot-20261001 and
/home/ts/wt/pyqt-reactive-render-complete-snapshot-20261001. Paired dependency
ad49487 (draft PyQT-reactive10), extended from the original3437d1c gitlink.
OpenHCS draft364 closes363 and366. Parent installed0585bf5/2de6bc0 and found
snapshot acceptance FAILED; the receiving-binding repair is source-only.
Closes #363. Closes #366. Paired PR: https://github.com/OpenHCSDev/PyQT-reactive/pull/10.

Required relation
-----------------

A successful mutation acknowledgement and a nonempty immediate capture do not
prove completion of the requested native canvas render. A render-complete
capture must arm before requesting a new native frame and capture only after
the renderer's own completion event, or fail with its bounded observation
evidence. The timeout is a failure bound, never a settling heuristic.

The original operation deadline also bounds dispatch, observation and artifact
publication. The old5s observation/5000ms transport equality was contradictory:
the socket poll started before Qt dispatch. Snapshot defaults now derive the
native upper bound (2.5s at5000ms) from the capture owner's declared equal phase
budget, not a guessed renderer settling delay. Explicit observation>=transport
is rejected once at ViewerWindowSnapshotRequest construction. The gateway
arms the original ZMQRuntime OperationDeadline before transport and the request
supplies it polymorphically to Qt; queue time consumes that same deadline.
The one original timer uses min(requested observation, remaining phase budget).
No socket/MCP timeout is increased, no second timer engine is introduced.
The original persistence owner uses QSaveFile and rechecks the same deadline;
late work fails once without retaining a newly created PNG. Receipts preserve
the actual observation budget and original operation deadline. These monotonic
deadline source checks cover managed local processes sharing a clock domain;
cross-host clock transfer is not qualified by this fixture or receipt.

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
unit/test_snapshot_deadline.py covers the original queue/gateway deadline journey.
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

Previous checkpoint shards, plugin/provider-free with CPU0 affinity, CPUQuota100%,
MemoryMax512M and MemorySwapMax0, shell timeout60s:

* qt-operation-final.log:15 passed,1.45s elapsed,127996KiB peak. Existing real
  qapp/rendered_canvas and observed_form fixtures, including original flash
  painter, late native completion, deadline, destruction and MI/new-case;
  expired queued operation and late real PNG commit are rejected without an
  artifact. The declaration-owned phase policy is included in this final run.
* spatial-final.log:16 passed,8.90s elapsed,482548KiB peak. Real ViewerModel,
  asymmetric nonzero gray/RGB crops, clipping/empty bounds, original two
  streaming-handler sampling tests, missing layout, color-axis retention and
  max bound. Semantic expected16x64x3; raw expected64x16x3.
* deadline-final.log:6 passed,7.10s elapsed,503236KiB peak. Original accepted
  control queue, canonical pickle serializer, registered action, real Qt paint
  and ViewerModel; no socket or server/application startup. Source transport
  fixture substitutes only the socket/poller; the original gateway, registered
  Qt queue, Qt timer, serializer and no-frame receipt execute. The receipt
  arrives within the caller bound, and later real painting yields neither
  another reply nor an artifact. Defaults/explicit contradictions are checked.
* contracts-deadline.log:15 passed,11.26s elapsed,289680KiB peak. Nominal MCP
  input contract/signature, capture-field projection, missing/stale/foreign
  receipt rejection, error receipt retention, DTO roundtrip, real Qt managed
  reply, original immediate/malformed service contracts, and strict original
  AgentResourceRef schema decoding (wrong types and unknown fields rejected),
  and original silent gateway teardown bounded by the remaining deadline.

First failures are archived, not overwritten: contracts-first (missing reused
native extension), contracts-checkpoint (wrong source dependency import path),
spatial-first (factory default validation and missing fixture title), queued
first/second/third (fixture endpoint initialization and teardown), qt-final
(overbroad selector included four qtbot cases without the forbidden plugin).
qt-deadline's missing fixture render owner is preserved before its corrected
run; no production code bypassed the required nominal render owner.
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
Both pre-deadline full production ratchets passed: e16575464 OpenHCS against
791650087 in23.27s/87692KiB (r0-openhcs-schema.log), and a9e6745 pyqt against
3437d1c in3.42s/58192KiB (r0-pyqt-first.log). Revised end-to-end deadline
production also passes original pinned R0 without any positive measure:
OpenHCS f7f9af993 against791650087 in24.15s/87744KiB
(r0-openhcs-operation.log), pyqt2de6bc0 against3437d1c in6.11s/58208KiB
(r0-pyqt-operation.log). All five OpenHCS production paths and the actual paired
pyqt production delta are included. No detector copy, omission, raised bound
or waiver. Subsequent archive/receipt commit does not change production bytes.

Byte-exact raw evidence is retained in
docs/validation/issue363-source-checks-20261001.tar.gz. Archive entries preserve
the original log basenames above and full commands/resource footers, including
all original failures. Fresh extraction and byte comparisons precede removal
of the replaced loose versioned copies. No pytest whitespace is rewritten.
Production/docs and whole-PR diff whitespace checks are now separate from the
unchanged evidence bytes inside the archive. The copied source-test native
extension and exact owned agent-scratch directory are disposable and removed
after archival; source worktrees, original parent witnesses and installed
packages remain untouched.

This receipt is a focused source/ownership review, not a completed global NRA
scan or equivalence proof. The user's source-only limits govern validation;
no native application, MCP server, install, build, download or scientific run.
OpenHCS root conftest is intentionally excluded because it owns runtime cleanup.
Installed acceptance must repeat the original channel isolation/navigation and
same-coordinate snapshot journey, inspect render receipts and exact RGB samples
through the actual MCP entrypoint, retaining the original immediate failures.

Installed binding failure and source repair
------------------------------------------

Parent's actual healthy MCP/native trial at :91/5992 used exact OpenHCS0585bf5
and pyqt-reactive2de6bc0 private wheels, with two streamed raw64x64 planes.
Default render_complete returned captured=false, no artifact in captures/initial,
and viewer_window_snapshot_failed with the exact message::

    QTimer(parent: QObject|None = None): argument 1 has unexpected type 'CanvasBackendDesktop'

Original byte-exact mcp.stdin/mcp.stdout and original-runtime-logs.tar.gz remain
under /home/ts/wt/openhcs-issue-batch-20260929/snapshot364-installed-20261001.
At the terminal parent checkpoint the transcripts' SHA256 values are
f164d21999c4f6c567770768fb4b3c6fc3fa465fb3f50cb3778ef1ce912e4b76 (stdin) and
a930cad6b5a0406ddf1cbf0557fafe351a6b4aca37eaf9a514c882e6913095fb (stdout).
Parent archived the runtime and reported process_exited=true/ack/endpoint
terminal, with both original viewer and MCP absent. No process was touched by
this sidecar. Fresh installed acceptance is a new parent-owned incarnation.
Public original checkpoint: https://github.com/OpenHCSDev/openhcs/pull/364#issuecomment-5933497228.
Exact failure is also recorded on issue363 and this draft; no merge requested.

The wrapper diagnosis is withdrawn. Read original installed Vispy _qt.py:
Canvas.native delegates _backend._vispy_get_native_canvas(); CanvasBackendDesktop
inherits QtBaseCanvasBackend and its selected QGLWidget, which is QOpenGLWidget
for these Qt5/Qt6 branches. Napari's VispyCanvas.native returns that native
widget. QtPy's original API_NAME/module contract selects the receiving binding.
Parent process maps contained PyQt5 QtCore/QtWidgets and PyQt6 QtCore. The
lightweight original-source real Vispy fixture independently reproduces the
exact QTimer error at the original line488, and a second QSaveFile overload
error when the original Qt5 pixmap is saved to the Qt6 device. Binding, not
widget unwrapping, is the demonstrated defect.

Required relation: renderer QWidget/QObject, observation QTimer and PNG
QIODevice must belong to the receiving integration's original Qt binding.
BOUND-2: do not bypass QtPy with another backend selector. BOUND-7/IMPL-3:
reject attribute-name probes, type guesses or consumer switches. IMPL-12/13:
keep the one observation/persistence algorithm. QtWindowSnapshotService owns
the qt_core hook, with the original PyQt6 default for reactive forms. The small
NapariScreenshotControlMessageAction hook returns the original QtPy.QtCore.
Shared _WindowSnapshotObservation and _persist use that same authority for
QTimer/PreciseTimer and QSaveFile/QIODevice. No new timer, painter, registry,
binding roster, environment forcing, unwrapping or timeout change is added.
Existing genuine control/capture MI and cooperative dispatch remain intact.
A QtPySnapshotService new case declares only qt_core; original capture/observe
methods are inherited unchanged, with no generic consumer edit.

Reopened production delta is only napari_viewer_server.py's binding hook and
pyqt-reactive services/window_snapshot.py's shared hook/device selection.
Source tests add real Vispy CanvasBackendDesktop coverage at the registered
Napari queue and in tests/test_window_snapshot_bindings.py. The existing
test_napari_render_snapshot.py Qt fixture now uses its receiving QtPy binding,
including QtPy's original isalive lifetime contract. No axis/source-binding,
startup/connect, general DTO or sampling production source was changed.

New source checks run sequentially with the original CPU0/oneCPU,512MiB,60s
limits, plugin/provider-free. QtPy default is unforced PyQt5; PyQt6 is an
explicit test-matrix case, not a launcher/product environment patch. PySide6
is not installed in the read-only validation environment and is unexecuted.
The real Vispy backend is constructed normally, not replaced by a mock canvas.
Its original MRO is logged with the original QtPy binding diagnostic. It stays
hidden, with DISPLAY unset for this offscreen source fixture; no GL frame is
painted or swapped. Emitting its late signal tests cleanup only, not a render
proof. Real QLabel pixmap persistence tests the original atomic writer.

* vispy-original-binding-failure.log: original2de6bc0 source,2 failed/1 passed,
  0.60s/109068KiB; exact QTimer parent and QSaveFile overload failures retained.
* vispy-default-final.log:3 passed,0.53s/104348KiB, real native Qt5 backend,
  matching parented timer, typed no-frame failure, no late artifact/duplicate
  callback, real PNG persistence and declaration-only new binding case.
* vispy-qt6-final.log: same3 passed,0.97s/107252KiB, real native Qt6 backend.
* queue-deadline-default-final.log:7 passed,11.57s/490828KiB; real ViewerModel,
  original registered accepted queue/serializer/gateway, real native Vispy
  ownership plus real Qt painting, default/contradictory bounds, failure receipt
  and no late artifact/duplicate reply. Existing immediate PNG success is kept.
* queue-deadline-qt6-final.log: same7 passed,7.32s/493992KiB under Qt6.
* qt-existing-corrected.log:16 passed,1.56s/127308KiB; existing real qapp,
  native paint, flash observation, cooperative MI/new case, expired queue,
  late PNG commit, headless declaration and capture-field checks.

First binding-original-failure.log is an unsuccessful heavier NapariSceneCanvas
fixture: it stopped during offscreen GLX context creation before reaching the
binding assertion and measured539192KiB RSS, above the allowed524288KiB.
It is not admitted as a passing bounded test. The corrected split uses the
actual Vispy backend at the failing QObject boundary without importing the
heavier Napari render-authoring graph; no bound was raised or assertion waived.
qt-existing-final.log also preserves an overbroad selector's missing qtbot
fixture (16 passed/1 error). The corrected plugin-free selector excludes that
unavailable plugin case, retains the existing real flash fixture and changes
no assertion or production behavior. No passing log replaces a failed log.

Both complete actual production deltas pass the unchanged pinned original R0,
3b03785f45df2ef5dc62ba6aed99294192ecbb01 (clean read-only detector worktree):
OpenHCS8b7b7c4bf against791650087,22.67s/87636KiB, r0-openhcs-binding.log;
pyqtad49487 against3437d1c,3.40s/58180KiB, r0-pyqt-binding.log.
All five changed OpenHCS production Python paths and the complete paired
window_snapshot.py delta are measured; no positive measure, detector copy,
omitted path, increased bound or waiver. Later documentation/archive/gitlink
publication changes no production bytes. This remains a focused ownership
review, not a completed global NRA scan or native equivalence proof.

Owned scratch is /home/ts/.cache/agent-scratch/render-complete-snapshot-363-binding-20261001,
for source fixtures/cache/raw logs only; remove it and the reused source-test
extension only after byte-exact archive/extraction checks. Original archive
issue363-source-checks-20261001.tar.gz and parent logs remain unchanged.
New byte-exact evidence archive is
docs/validation/issue363-binding-source-checks-20261001.tar.gz, including the
two binding failures, resource/GLX fixture failure, unavailable qtbot selector
failure, successful source shards and both complete original R0 logs with
commands/resource footers. Fresh extraction must compare byte-for-byte with
every original raw log before the owned scratch is removed. Whitespace checks
apply to source/docs and whole PR without rewriting raw evidence.
Archive SHA256: e20adeb454127d6f8a2bba945b44ef4a2a2a435f6fbf4e3a396c1bc511091029.

Parent independently reports installed RGB technical PASS through the original
prepared metadata workspace: semantic y16/h16/x0/w64 equals fullRGB[16:32,:,:]
as16x64x3, all3072 values, while raw [[16,32],[0,64]] equals fullRGB[:,16:32,:]
as64x16x3, all3072 values. The initial result_directory request was correctly
refused without source_receipt; parent preserves that original error and is
correcting its validator's DTO route-key location, not product source.
This is read-only numerical/sample acceptance, not a biological or producer
identity claim and not snapshot acceptance.

Status
------

Installed snapshot acceptance FAILED at0585bf5/2de6bc0; no merge/readiness.
Receiving-binding repair is a paired source-tested draft checkpoint only.
Native OpenGL frame completion/composition and fresh installed MCP acceptance
remain parent-owned; no source check claims them.
