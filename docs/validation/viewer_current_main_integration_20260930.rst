Managed viewer checkpoint against current main
=============================================

Integration owner: parent blind-analysis thread, existing OpenHCS PR159 and
paired ZMQRuntime PR7. The isolated persistent integration tree normally merges
main65b2ed101 and the existing159 implementation; no original author tree or
dirty primary edit was changed. The gitlink conflict is resolved to actual
dependency merge2c68a114, descending from both40f9edb and main3374aa8.

The existing atomic acquisition owner admits the new launch declaration before
returning a healthy managed viewer. The existing common lifecycle owns matching
for both Napari and Fiji. Its replaced Napari-only implementation, early manager
return and redundant no-argument matching forwarder are deleted. External
attachment does not acquire launch/rebind authority over the foreign process.
These are IMPL-4 and BOUND-2 corrections, not a second cache or viewer-kind switch.

Current-main review also reproduced a real RGB source-window defect. The
8x9x3 RGB test declares source domain8x9/channel-axis2, but the streaming request
validated trailing dimensions9x3 and rejected the image before dispatch. It now
queries ImagePayloadMetadata.spatial_shape_yx, the existing channel/plane-aware
authority. A payload without Y/X remains rejected. Scalar and crop controls are
retained. Transport errors while reading an external launch declaration now
fail reuse admission rather than escaping as an uncaught zmq.Again.

The compatibility-only fixture now controls the required active launch response
instead of contacting a real foreign endpoint42. The fake native-entrypoint
fixture supplies its orthogonal-widget boundary; the real widget remains enabled
in production. This prevents that fake QApplication from constructing a real
QWidget and aborting the test process. The new dock is explicitly asserted in
the event-order test, not disabled behind a product flag.

Evidence and limits
-------------------

The reviewed candidate was installed serially in the existing Python3.12 venv
using offline shared build cache, no dependencies, new environment, Fiji or JDK
download. Install5.90s/peak147188KiB, only OpenHCS and ZMQRuntime replaced.
Ordinary imports with PYTHONPATH unset resolve this OpenHCS tree and its exact
ZMQ submodule; ArrayBridge remains the installed409 wheel. It is an installed
candidate, not merged-main or live acceptance.

Twenty-six dependency cases pass in2.61s: viewer acquisition, ACK startup and
progress annotation. One hundred thirteen installed core/viewer/Fiji checks
passed in6.80s after the RGB and transport corrections. Three fake native
entrypoint checks pass in5.04s,137 unrelated tests deselected. Two warnings are
disabled pytest-asyncio configuration. XMLs and original failures are retained
under the parent issue-batch ledger. The first invocation failed to find the
project test plugin from another working directory; rerunning from this actual
tree fixed that test discovery issue, without a package/source-path workaround.

The wider Napari suite still reports other failures and its Qt-dependent tests
need separate diagnosis. Its initial process abort was a real QWidget under the
fake QApplication, not an observed crash of the user's X session. No claim that
all tests pass or that the ordinary fresh viewer is accepted.

Original packaged structural screening at407fc3be versus main65 records5145
metrics and two positive GodClassExcess leads: FijiViewerServer+1 and common
ManagedViewerLifecycleMixin+2. No guard waiver/pass or global NRA claim. Deleting
the redundant matching forwarder addresses real duplicate invocation structure;
a fresh committed-head screening and the remaining Fiji lead are still required.
No class is moved to a helper or mixin merely to evade the metric.

Live acceptance uses only a tiny two-channel64x64 synthetic fixture generated
by the existing check_viewer_feature_measurement_live.make_fixture helper.
The isolated :88/5794 slot was vacant before dispatch; snapshots, source-aligned
state, OS listeners and reuse by a second fresh MCP process are required.
Every UI/viewer operation goes through actual MCP. Preserve any uncertain
dispatch without replay. Freeze evidence before closing only the proved test
viewer through its exposed lifecycle capability.

Protected H002 GUI/runtime/viewer and original in-memory undo/history remain
unchanged. Retained5690 still has the separate geometry-source mismatch tracked
in issue280. A synthetic viewer cannot establish biological QA or solve that
protected-state cutover. The full ZIP R0/L0/S1-S8 and blind-analysis goal remain
active and incomplete. Hosted CI waiting is not imposed.

Actual installed live checkpoint
-------------------------------

Frozen source4cfe230f9, exact dependency2c68a114. A fresh nonresident MCP3247237
reports this exact installed source, ready resources and no stale paths, then
discovers the full-surface stream capability and streams two64x64 synthetic
images on isolated display:88. Both real OS listeners belong to viewer3247334
and bind only127.0.0.1:5794 and127.0.0.1:6794. Typed state is observed, image
route and native Y/X axes are present, and the actual opened bitmap shows the
expected gradient and native controls.

A second fresh nonresident MCP3251697 successfully streams the same retained
fixture through external attachment, observes typed state, captures another
bitmap and closes the test viewer through openhcs_close_viewer_window. That
response reports succeeded/endpoint_terminated. Both listeners and all three
owned processes are independently absent after terminal completion; no OS
signal was used. Original protected H002 processes remain unchanged. Both
bitmaps were opened by the parent. Their camera zoom differs1.349 versus
2.529375 with unchanged center/canvas; this is not a matched biological QA set
or a claim of preserving presentation across streaming.

Final installed core/viewer/Fiji regression rerun:113 pass6.45s, zero skips and
deselections, on the committed4cfe source with PYTHONPATH unset. Three fake
native-entrypoint checks pass separately,137 unrelated cases deselected.
The wider Napari suite remains failed; its scope is not exonerated.

Post-correction original screening retains5145metrics and just the Fiji class
+1 lead. Its exact new line is projection of launch_config.process_launch into
the existing control context, not another policy/registry or dispatch. The
common lifecycle's redundant forwarding member is genuinely removed. Paired
dependency screening retains158metrics and one ForeignAbsenceProbe lead on
``not instance.visualizer.is_running``. This queries the original nominal
visualizer health contract, rather than reconstructing another owner's state
from optional/private fields. Neither screening is called a pass and no guard
was weakened. These original report limits remain part of full R0 acceptance;
locally tested installed/live checkpoint shipment is distinct from whole-plan
completion, under the owner's explicit CI-deferral and checkpoint requirements.

The first client batch contained a local JSON quoting error before any stream
dispatch. Its original response is preserved; source confirms argument parsing
precedes tool dispatch. The next batch supplied corrected local input, never
replayed an uncertain mutation. Misclassification as a transport error is now
tracked separately in issue283. The RGB source defect is tracked in issue282,
whose original failing counterexample is retained and now passes.

Durable small fixture, original/fresh client responses and both captures live
under tests/runtime_diagnostics/viewer_admission_live_20260930. No private XDG
configuration/cache is published. Resources after closing the test viewer:
17.5GiB available RAM,14.4GiB swap warning and20.3GiB home free. Removed only
300KiB of older verified disposable build/diagnostic scratch; all source, saved
history and durable receipts remain. No new scientific runtime or agent fleet.

Current-main shipment checkpoint
-------------------------------

Normally merged performance main cad1ed2bd without conflicts. The earlier wider
Napari failures are now diagnosed and fixed in test fixtures, not waived: state,
navigation and native intensity tests supplied incomplete Dims/camera doubles.
They now use Napari's own Dims and Camera models with representative ranges;
the nonzero current_step is assigned through its real setter. All original
assertions remain, plus explicit displayed-axis/order/canvas projections.
Production state projection still trusts the original native contracts directly;
no attribute-default fallback or extra dispatch was added (BOUND-7).

The offscreen Qt run terminated at GLX context creation, with no complete XML.
Its observation is retained separately from the original fake-QApplication
abort. The actual native Qt tests succeed using existing isolated display :88
and software GL. The coherent current-main installed-source shard passes all
253 Napari/core/viewer/Fiji cases in12.77s, zero skips/deselections, with only
two disabled pytest-asyncio configuration warnings. Durable result:
parent ledger viewer-current-main-final-253-20260930.xml. Intermediate failed
XMLs remain there too. No hosted CI wait or full-plan guard-pass claim.

The earlier actual MCP launch/external-attach/state/bitmap/close journey proves
the unchanged viewer implementation; it does not evaluate biological accuracy.
Paired ZMQRuntime PR7 is now merged at2aa6d21c, code-identical to this reviewed
2c68a114 pin. Retained H002 history and issue280 remain protected. The full ZIP
refactors, reference boundaries and autonomous scientific acceptance stay open.
