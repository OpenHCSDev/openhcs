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
