Native composite and detached-window presentation: #451/#452, PR454
=================================================================

Source owner Schrodinger; integration and installed/native acceptance owner
parent. Existing worktree and publication ledger preserved. Production checkpoint
6967c0ea42850666d87d9d367cb39d430abab7c3 is normally merged with parent main
b68029c0c at 3b688b52a; no rebase, reset, competing Root394 work or installed change.
Original failed native evidence remains in parent VIEWER-COMPOSITE-ISSUE.rst,
VIEWER-WINDOW-CONTROL-ISSUE.rst and mcp-449-native.stdout. Issues remain open until
parent's installed two-window and physical C1/C3 acceptance.

Ownership and migration closure
-------------------------------

* Original NapariDisplayConfig remains the sole display schema. Plate stream
  ingress carries it directly; StreamingConfigBehaviorMixin admits a matching
  display declaration and uses original overlay_non_none_dataclass. The inherited
  channel_mode=LAYER reaches original grouping, not a channel/pixel remapper.
* NapariPresentationControlMessageAction owns nominal payload admission, native
  apply/readback and success/error replies for camera, image color and window.
  Leaves supply request type, reply field and the native behavior hook. Color
  genuinely composes that owner with NapariMountedRouteControlMessageAction by
  C3 MRO; exact mounted-route admission is not copied. Native Image/colormap/
  Blending contracts validate external names; no new color-name roster.
* ViewerNativeWindowControlOptions owns optional effect execution/order. Actual
  Qt focus, bounded positioning and readback belong to NapariNativeWindowPresentation.
  The old ROI-table focus sequence now consumes this same focus implementation.
  Geometry is logical client geometry, bounded by the window's current available
  screen and minimum size; actual window-manager results are read back, not cached.
  This is distinct from the unchanged native camera operation.
* ViewerWindowPresentationResult owns readback descent and typed construction.
  Existing viewer service/gateway invoke this family without operation switches.
  Original socket deadline, teardown and missing-endpoint failure remain unchanged.
  Viewport-only service/gateway methods and all their consumers are replaced,
  not kept as forwarding compatibility facades. Viewer service shrinks 16 lines.
* ViewerNativePresentationCapability owns common invocation and exposure metadata.
  New tools are derived from the existing capability registry and MCP generator;
  MCP server code, catalog rosters and launch mechanisms are unchanged.
* ViewerProjectionRecord's cooperative Pydantic hook now descends through its
  ORIGINAL from_wire_mapping/dataclass_from_mapping before original native
  validation. The retained first MCP failure showed direct construction bypassing
  nested geometry descent. No second decoder, schema store or parser is added.
* NapariImagePayloadLayoutRole members own title/default-route facts. Its old
  title dictionary is deleted; source-channel carriers no longer falsely claim
  RGB. Existing route suffixes and scalar titles are unchanged.

Image intensity is intentionally still the original full-state route operation:
it verifies mounted-route/native-state evidence, unlike the three property-only
reply operations. No second intensity implementation or weaker replacement is
introduced. No scientific source metadata, pixels, provenance, physical channel
identity, calibration, compiler/kernel placement or persisted image formats change.

Source reasoning and existing AST evidence
-----------------------------------------

Personally read current NRA/refactor-audit skills, authoritative ZIP SKILL.md and
catalog README/identity/boundaries/implementation, surface receipt and project
rules. Also read the actual OPENHCS-HISTORY.md path and relevant source analyses
for #44/#45/#51/#58/#60: declaration discovery, shared lifecycle hooks, single
model authority and deletion of the competing compiler/runtime lattice.

ownership-before.log uses existing refactor-audit Package/ParsedModule ASTs,
enumerating declarations, imports, assignments, decisions, calls and references
before structural edits across OpenHCS703, PolyStore streaming26, ZMQ32,
python-introspect12 and Qt193 modules. Zero parse omissions; exact dependency
checkout heads are in each ROOT record (these are read-only source context,
not a claim of installed/gitlink equivalence). Relevant native/backend/DTO/service/
MCP/CLI sites were read semantically. The complete current linear AST closure is
ownership-after-linear.log; it additionally records explicit bases/signatures.
merged-main-ast-closure.log repeats the current production closure at integrated
3b688b52a with explicit load/store contexts:703 parsed, zero omissions. Unchanged
dependency identities remain those of ownership-after-linear.log.
An intermediate bounded after-query terminated without output and is retained
as ownership-after.log, not called complete. Queries are one-off inspection of
existing AST owners, not a new scanner/gate/report framework. AST name/attribute
queries do not resolve dynamic bindings; runtime AutoRegisterMeta discovery,
typed schema descent and cooperative hooks are covered by focused behavior,
not a global NRA proof. Historical full-context R1 remains separately incomplete.

After migration, production and all gateway fixtures have no viewer-service
viewport() caller or definition. Existing dev-client viewport requests continue
to project the same public tool arguments. Parent #453 progress mixins and compile
gateway fixtures are retained unchanged by the normal main merge. Root394 roster
excludes these viewer/config/agent files; source seam comments:
https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5951783600
https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5952174462

Applicable antipattern review: IDEN-1/4 (native geometry vs camera vs physical
identity; truthful channel titles), IDEN-5/6 (Qt and mounted-route identities,
no request-state mirror), BOUND-1/8 (original typed config and native operations
stay typed across generated MCP and socket ingress), IMPL-2/4 (member-held title
facts and whole property family migration), IMPL-5/12/13 (one reply/admission,
one exact-route boundary, one focus sequence, original transport and decoder).
No consumer kind/type switch, parallel registry, copied dispatch, fallback or
suppression added. The first R0 +1 foreign optional-geometry probe is retained;
effect execution moved to its declaration owner rather than rewriting the guard.

Behavior and limits
-------------------

All final source checks serial CPU0, CPUQuota100%, MemoryMax512MiB,
MemorySwapMax0, outer60s, numeric pools1, original read-only Python3.12/ABI driver
and original Qt source checkout. No environment/build/download/provider/native/
viewer/installed mutation. Parent owns real socket/window-manager/screenshots.

* qualified-native-controls.log: 12 PASS, 9.17s wall / 508504KiB peak.
  Original LAYER C1/C3 composition shares native world XY, .12353054911059548um
  calibration and independent intensity windows with unchanged pixels/identities.
  Color rejects missing routes, bad names/modes, RGB/RGBA and nonimage layers.
  Window fixture proves readback, isolated focus, restore/order and geometry bounds.
  Independent color capability executes real before/super/after C3 hooks through
  the unedited shared consumer/derived registry; extended display projection also
  runs its cooperative inherited hook without editing admission.
* qualified-public-mcp-controls.log: 2 PASS, 10.08s / 517196KiB.
  Original public generator derives schemas and invokes both new tools; nested
  geometry rejects boolean dimensions before gateway dispatch. Native readback
  differs from prior requested state; missing endpoint fails without launch/adoption.
* original-presentation-controls.log: 40 PASS, 9.76s / 510268KiB, original449
  carrier/RGB/RGBA/calibration plus native camera, acknowledgement and title controls.
* mcp-record-descent.log: 17 PASS (2 public controls plus15 existing typed-record
  controls), 11.08s / 523628KiB before the optional-effect-only refinement.
* final-original-r0.log: original pinned guard3b03785f45df2ef5dc62ba6aed99294192ecbb01,
  original Python3.14/read-only metaclass backing, base4754fbe2b ->6967c0ea4.
  Exit0,28.85s/87772KiB,5278 deltas; zero positive, viewer service GodClassExcess-16.
* merged-main-native-controls.log:12 PASS,10.09s/507068KiB and
  merged-main-public-mcp-controls.log:2 PASS,10.37s/519176KiB on integrated3b688b52a.
* merged-main-original-r0.log: same original guard, exact parent
  b68029c0cfc017c5a4b086bc607bff3c0bec6c01 ->
  3b688b52a20ceb8601edb39ccdc7fe33fbc4e7a0, exit0,28.52s/87944KiB,
  5278 deltas, zero positive; sole nonzero viewer service GodClassExcess-16.

Thus54 distinct focused behavior controls pass (12 new native,2 new generated
public MCP,40 original presentation controls), plus15 existing record controls.
The integrated main check specifically reruns the14 new controls, not another
wide scan. Source-qualified and ready for parent review/install; not live-qualified.

Earlier logs preserve a fixture wrong-method failure, original nested MCP rejection,
R0 foreign-probe rejection, and a broader conftest-free attempt with8 unavailable
qtbot errors. Some earlier passes exceeded512MiB reported RSS despite cgroup limits;
they are not the final resource-qualified shards above. No GUI fixture was launched
to erase those errors. No complete/full-NRA, installed/live, or biological pass claimed.
Named pytest scratch was not materialized, so no scratch data was deleted; source,
original failures, logs and untracked required-runtime-qt-publication ledger remain.

Parent native acceptance route
------------------------------

Use original stream tool with display_config.channel_mode="layer", then set each
exact mounted route via openhcs_set_viewer_image_color(route_key=...,
presentation={colormap,blending}) and existing openhcs_set_viewer_image_intensity(
route_key=...,presentation={contrast_limits,gamma}).
Read a detached window with openhcs_set_viewer_native_window(presentation={});
focus it with presentation={focus:true}; position with its typed complete geometry.
All operations address the original supplied viewer connection. Check actual
readback and opened frames for both windows; no protected-viewer replay by source owner.
