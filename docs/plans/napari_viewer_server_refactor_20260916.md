# Napari viewer server refactor trajectory

Date: 2026-09-16

This is a planning artifact, not an applied refactor. It records the ownership
decisions and the ordered NRA DSL trajectory required to split
`openhcs/runtime/napari_viewer_server.py` without replacing one monolith with a
cycle of mutually importing modules.

## Baseline

The current module contains 5,604 lines, 68 top-level classes, and 312 indexed
functions or methods. The concrete `NapariViewerServer` is only 359 lines. Most
of the size comes from six subsystems accumulated around it:

1. Napari-specific wire and payload declarations.
2. Route construction and layer display.
3. ROI and result-element selection.
4. State and payload projection.
5. Control-message actions.
6. Socket-owning transport pumps and process startup.

An earlier complete exact NRA scan covered all 79 applicable detectors and
reported no nominal-authority finding. A deliberately broader scan with a lower
duplicate-method threshold failed closed at the 60-second deadline while
preparing `closed_parameter_conveyor`. Therefore the refactor is practitioner-
selected from dependency evidence; it is not an automatically synthesized NRA
finding.

## What the DSL probes established

NRA's module-move preflight rejected a direct extraction of the ROI selection
subsystem. Starting from `NapariResultSelectionController` derived a 67-symbol
closure that included payload declarations, display machinery, control actions,
both transport pumps, and `NapariViewerServer` itself. The closure is real, not
just an import-formatting problem.

The main causes are:

- Selection calls `NapariNavigationControlMessageAction` to perform local UI
  navigation, while the navigation action calls the selection controller.
- Helper subsystems name the concrete `NapariViewerServer` rather than a nominal
  viewer-runtime boundary.
- `NapariStreamLayerContext.layer_route()` performs display-title construction,
  and `NapariLayerTitleAuthority` dispatches through
  `NapariLayerDisplayHandler`.
- Both transport pumps independently implement the same thread, readiness,
  polling, shutdown, socket cleanup, and terminal-failure lifecycle.

An exact payload extraction was also rejected. Even after including the payload
types, constants, route record, title authority, and metadata normalizer, the
closure still required `NapariLayerDisplayHandler`. This proves that payload
decoding and display policy are not currently separated.

These failures are useful plan evidence. Raising the closure bound and moving
all 67 symbols would merely rename the monolith.

## Destination ownership

The target dependency direction is:

```text
napari_viewer_runtime.py
        |
        v
napari_viewer_protocol.py
        |
        v
napari_viewer_display.py
        |
        +------------------+
        v                  v
napari_viewer_selection.py napari_viewer_projection.py
        |                  |
        +---------+--------+
                  v
napari_viewer_controls.py
                  |
                  v
napari_viewer_transport.py
                  |
                  v
napari_viewer_server.py
```

`napari_viewer_runtime.py` owns the nominal `NapariViewerRuntimeABC` boundary.
It declares the runtime state and operations that viewer subsystems may consume.
No extracted module may import the concrete server. The concrete server remains
the leaf that supplies that contract and combines the subsystems.

The runtime ABC must not become a parallel state holder or a forwarding facade.
Existing server state remains authoritative. The boundary declares the facts and
operations consumers are entitled to use; extracted consumers access those
declared members directly.

`napari_viewer_protocol.py` owns Napari-specific typed wire decoding, immutable
accepted-message records, stream-layer payloads, and typed replies. It must not
choose layer handlers or construct visible layer titles.

`napari_viewer_display.py` owns route construction, title derivation, variable-
size policy, dimension labels, layer handlers, and the display pipeline.

`napari_viewer_selection.py` owns result-selection state, subject indexing,
native selection synchronization, highlighting, and the ROI manager toolbar.

`napari_viewer_projection.py` owns read-only projections of authoritative live
viewer state. It does not mutate the viewer and does not dispatch control
messages.

`napari_viewer_controls.py` owns the registered control-action family. Leaves
retain only request-specific validation, mutation, and reply fields; common
request extraction and error projection belong on the action ancestor only when
the response contract is genuinely identical.

`napari_viewer_transport.py` contains only Napari request acceptance and the
small hooks required by the generic threaded REP endpoint lifecycle in
`zmqruntime`.

## Ordered DSL trajectory

### Phase 1: break the selection and control cycle

Declare `NapariViewerNavigationAuthority`, make
`NapariNavigationControlMessageAction` derive from it, promote the four existing
navigation-calculation methods without copying their bodies, and redirect native
ROI selection to the authority rather than the transport action leaf.

The corresponding NRA sequence is stored in
`napari_viewer_navigation_authority_20260916.dsl`.

The sequence is structurally expressible with:

1. `insert_before_target`
2. `add_class_base`
3. `promote_class_members_to_ancestor`
4. `patch_target`

Current NRA correctly refuses to certify stage 3 because native object-capture
proof remains open as `unproved_execution_effects`. Do not weaken that guard.
Either finish the applicable NRA native proof or treat this one promotion as an
explicitly reviewed DSL gap with behavior tests.

Validation receipt (2026-09-16): the four-stage document validates against NRA
main at `52b84b74702d0d60f660a596b7cbdbce3ae9de73`. A full-context simulation
against the current OpenHCS package stops before writing source at
`stage-3-promote_class_members_to_ancestor`; the authority-claim preflight
reports `Native class capture remains unproved`. The validated document is
therefore a reproducible trajectory through the first ownership boundary, not
an executable certification of the complete extraction.

### Phase 2: separate payload decoding from display routing

Move route creation out of `NapariStreamLayerContext.layer_route()` and into the
display-owned route authority. The payload retains source facts; the display
authority derives `NapariLayerRoute`, its title, and its handler-dependent
suffix.

NRA currently has no declaration-selected operation for moving a method between
unrelated existing classes. Add that operation to NRA, or use one narrowly
scoped `patch_target` stage whose authored body is explicitly marked unproved.
Do not manufacture an inheritance relationship solely to satisfy the existing
ancestor-promotion operation.

### Phase 3: introduce the nominal runtime boundary

Create `NapariViewerRuntimeABC` and replace subsystem annotations of the
concrete server with the narrow nominal runtime declaration. The concrete
server derives from this ABC. Preserve direct access to guaranteed fields and
methods; do not add `getattr` fallbacks, dictionaries, or string dispatch.

Use `create_file`, `ensure_import`, `replace_class_base` or `add_class_base`, and
targeted `patch_target` operations. Re-run source-index resolution after the new
module is created.

### Phase 4: extract modules in dependency order

Use `extract_symbols_to_new_module` for each complete declaration set after the
seams above are in place:

1. Protocol and payload declarations.
2. Display and route declarations.
3. Selection declarations.
4. Projection declarations.
5. Control-action declarations.
6. Napari transport declarations.

Each extraction must pass module dependency preflight with no source-local
dependency on `napari_viewer_server.py`. Preserve source re-exports only for
actual public compatibility; private internal names should relocate rather than
create a permanent facade.

### Phase 5: factor the generic transport lifecycle in `zmqruntime`

This is a separate submodule transaction. Add a threaded REP endpoint ABC that
owns:

- start-once and stop behavior;
- ready and stop events;
- startup error propagation;
- owner-thread socket creation and cleanup;
- poll-loop termination;
- terminal failure reporting.

The Napari data and control pumps then supply only their endpoint identity,
socket binding, and one-request handling hooks. The generic lifecycle belongs in
`zmqruntime`; it must not be introduced in OpenHCS and copied later.

After validating and publishing the submodule change, update the OpenHCS
submodule revision, use `ensure_import` and `add_class_base` for the two Napari
leaves, then delete the superseded lifecycle methods with residual-use guards.

### Phase 6: shrink the concrete leaf

The final `NapariViewerServer` should retain only:

- endpoint construction;
- ownership of authoritative live runtime state;
- top-level start/stop composition;
- stream acceptance and Qt-thread queue draining;
- the process entry point.

Thin methods that exist only to forward to another owner should be removed once
all declaration-resolved callers use that owner directly.

## Expected result

The refactor should remove approximately 350 to 600 lines of repeated lifecycle
and action scaffolding. Most of the remaining change is relocation, not deletion.
The expected concrete server module is approximately 700 to 1,000 lines, with
the other implementation living under explicit acyclic owners.

Line count is not the acceptance criterion. The trajectory is complete only
when:

- no extracted subsystem imports `NapariViewerServer`;
- selection no longer depends on a control-message action;
- payload decoding no longer chooses display handlers or titles;
- the two pumps inherit one generic lifecycle owned by `zmqruntime`;
- control leaves contain only irreducible action behavior;
- a full NRA scan is complete with zero omitted detectors;
- focused viewer tests, real MCP navigation, ROI selection latency, streaming,
  settlement, screenshots, and shutdown all pass against a fresh viewer process.

## Validation batches

After each coherent applied phase, run the affected unit tests in bounded
parallel shards. After the final sequence, launch a fresh Napari viewer, stream
the current validation plate, select linked ROIs repeatedly through both the
native ROI manager and MCP, and verify state snapshots and screenshots. Syntax
simulation and source-rewrite proof do not establish Qt or ZMQ behavior.
