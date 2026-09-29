# Orthogonal managed-viewer surface receipt

Audited source: `feat/mcp-orthogonal-viewer-20260929` at
`2fb774e35777a6c7d5d3e4ba110d626a38985c56`, based on main
`0c7b898f852a8bedc0e1bc38b93f36088d301808`. Issue #152, draft PR #154.
Status: source investigation and native feasibility only. No Python edits,
complete architectural verdict, behavioural equivalence proof or managed
viewer/MCP acceptance claim.

## Boundary and authority witnesses

- `runtime/viewer_protocol.py:150`: `OpenHCSViewerControlMessageType` owns
  application-specific commands beyond the external ZMQRuntime protocol.
- `runtime/napari_viewer_server.py:2379`: `NapariControlMessageAction` derives
  dispatch from `AutoRegisterMeta`; extend this family, not a command roster.
- `runtime/napari_viewer_server.py:3545`: native state projection reads live
  viewer/layer owners. `NapariViewerStateProjection` does not currently report
  `dims.order`, `ndisplay` or the displayed semantic pair.
- `runtime/napari_viewer_server.py:1693`, `:1872`, `:1944`: existing image,
  Shapes and Points handlers consume `NapariAxisPresentation` and the route's
  `ViewerLayerAxisProjection`. Component coordinates, aggregate bindings,
  local offsets and spatial transforms are already owned there.
- `agent/dto/viewer.py:911`: `ViewerWindowStateResult` owns the agent-facing
  reflected state. `agent/services/viewer_window_service.py:1049` owns its
  transport boundary. `agent/capabilities.py:2997` exemplifies declaration-owned
  DTO/service projection into MCP. Capability imports/regions are a crossing
  with result worker `01a0eb3f-a127-7ba3-bdd7-41b53d94de56`; do not change its
  declarations.
- `pyproject.toml:320` declares `openhcs = "openhcs:napari.yaml"`. The bundled
  manifest currently contributes the SWC reader and `QRoiManager` widget.

Required relation: requested display dimensions must resolve to distinct
spatial axes in the mounted route, mapped through its existing presentation to
the actual viewer dimensions. Rank is not evidence of spatial Z. A local
component index is not a global semantic component value or world coordinate.

## Measurement and classification

At the audited head, the provided census parsed the production package with
zero unparsed files. Across the five assigned production files it reports
11,126 code lines, 8 exact type-identity checks, 45 long-chain terms, 36
string-keyed subscripts and 1 named-attribute probe. These are maintenance leads,
not evidence that each site should change for this task.

The overlay identifies three raw-record sites in `ViewerWindowService`:
`sample_image` reads record keys `array_value_summary/axis_indices/layer_route_key`;
`summarize_rois` consumes the payload's source-domain/shape-bound summary;
`_example_roi` projects external ROI metadata. Source review confirms these
are separate inspection projections, not an existing orthogonal-axis owner.
Do not refactor them as part of the missing control.

Applicable pattern guards: IMPL-5 prohibits independent plugin/service plane
dispatch; MEMB-1/MEMB-2 prohibit copied command/capability membership;
IDEN-1/IDEN-6 prohibit mixing route-local indices, component values and world
positions; BOUND-2 prohibits bypassing the existing route/metadata owners.
A new typed carrier alone does not satisfy these guards.

## Dependency and scan evidence

Python: 3.12.3, read-only interpreter
`/home/ts/code/projects/openhcs/.venv/bin/python`. Explicit owning source
`PYTHONPATH=/home/ts/code/projects/openhcs-orthogonal-viewer-20260929` was verified
by `openhcs.__file__`. Uninitialised worktree submodules retain their recorded
gitlinks; none was initialised, edited or substituted. Installed wheel sources
provide the dependencies: Napari 0.6.1, NumPy 2.1.3, MCP 1.29.0,
ZMQRuntime 0.2.24, PolyStore 0.2.19, pyqt-reactive 0.3.24, ObjectState 1.1.8,
python-introspect 0.1.14, metaclass-registry 0.2.1, ArrayBridge 0.3.4 and
pycodify 0.1.3. Their queried distributions have no editable `direct_url.json`.
The shared environment and installed dependencies were not changed.

NRA source: `/home/ts/code/projects/nominal-refactor-advisor` at
`52fe8b4666a20583f0ddf8ed3b7a9e89857e4809`, using its `.venv/bin/python`.
CLI flags were inspected. Scan positional root was the complete `openhcs`
package. Explicit context included that package and installed source roots for
all eight first-party dependencies plus Napari, Pydantic, QtPy and MCP.
Flags: `--parse-workers 1 --analysis-workers 1 --json --raw-findings
--json-payload full`. The retry also used `--scan-budget-seconds 600`.

Receipts: `/tmp/openhcs-orthogonal-154.w9Q7Hoi3/`.

- `baseline-full.json/log`: default internal 20-second deadline, exit 124,
  `complete=false`, stopped during `parse_python_module`; wall 21.23 seconds,
  maximum RSS 710,932 KiB. A longer shell timeout did not override that deadline.
- `baseline-600-resource.json`: corrected internal budget; owned scan process
  terminated at the 768 MiB ceiling, sampled RSS 789,428 KiB, wall 15.11 seconds.
  Full arguments retained. No completed output, detector-coverage inventory or
  R1 `supporting_raw_findings` evidence was produced.
- `census.json/log`, `overlay.json/log`: baseline debt measurements. Overlay
  leads are not a substitute for NRA R1 records.

Coverage remains unfinished, not `focused_local_partial` global proof and not
a green audit. Resolve the scan resource allowance and complete production
dependency context before authoring Python changes. Do not omit detectors or
dependencies, suppress failures or claim equivalent bodies from syntax replay.

## Native multi-axis experiment

`native-7d-corrected.json/log` records a fresh CPU-only `ViewerModel` diagnostic,
not a GUI process or MCP roundtrip. Public native APIs only; no scientific data.
Axes: `site/channel/z_index/timepoint/well/y/x`. Shapes:
`(2,2,3,2,2,4,5)` and `(1,2,3,1,2,4,5)`. Nonspatial selectors are explicitly
retained, with spatial Z at axis 2 rather than third-last.

Ordered displayed pairs XY `(5,6)`, XZ `(2,6)`, YZ `(2,5)` passed for both
domains: 94 raw/dense-Labels pixel sample pairs and 6 transformed-Points identity
checks. Anisotropic scale `(1,1,2.5,1,1,0.8,0.9)` and translation
`(10,20,17,30,40,-2,4)` were retained. World point, array identities, intensity
gamma and nonspatial coordinates were unchanged. Wall 5.47 seconds; maximum
RSS 464,040 KiB. `native-7d.json/log` retains the first failed diagnostic: its
`get_value` call supplied a tuple instead of the library's list contract.

Not established: OpenHCS route-local component-domain offsets, planar Shapes
validation, rendered canvas/camera orientation, plugin/MCP equivalence,
managed service schema or the required isolated viewer+MCP roundtrip.

## Plugin scope and owner rationale

Use the existing bundled npe2 manifest for a typed sequential-plane widget.
Both widget and MCP must submit the same typed command through the existing
action family. Resolve axes from the mounted route's declaration/presentation,
validate every target and visible representation before any mutation, then
update only native `dims.order`/`ndisplay`. Reflect actual live order, displayed
axes, world position and canvas/camera orientation, including user changes.
No desired-orientation cache, copied arrays, second route map or controller.

Native dense Labels and Points can be tested for transformed orthogonal
alignment. Existing per-Z planar Shapes are not dense volumetric labels; reject
an unsupported cross-section operation truthfully before mutation rather than
fabricating geometry. Keep legal XY review available.

New-case experiment: a new supported display pair is declared once at its
typed semantic owner; UI choices and MCP schema are derived from that owner.
It must not require edits to independent UI, service and runtime plane tables.
The attachment mechanism for a plugin widget in a managed viewer remains to be
proved; an ordinary unbound Napari viewer must not silently infer OpenHCS routes.

Research inspected upstream manager at
`1842f5a167f0cd552bcf791fa7023e7422a41b8f` and 3D widget at
`e6d56314091e9eac9954613efdf161942444c4d0`:

- [Native Dims](https://napari.org/stable/api/napari.components.Dims.html):
  `ndim` is arbitrary; `order` and `ndisplay` select displayed dimensions.
- [napari-orthogonal-views manager](https://github.com/AnniekStok/napari-orthogonal-views/blob/1842f5a167f0cd552bcf791fa7023e7422a41b8f/src/napari_orthogonal_views/ortho_view_manager.py):
  supports more than three dimensions, retaining the prefix of CURRENT order
  and rotating its final three entries. That is not a general ndim restriction.
  In an order ending `well/y/x`, its selected triple is not spatial Z/Y/X.
  It also reparents the canvas using private Qt access. Its
  [README](https://github.com/AnniekStok/napari-orthogonal-views/blob/1842f5a167f0cd552bcf791fa7023e7422a41b8f/README.md)
  documents shared underlying arrays and a temporarily unresponsive canvas caveat.
- [napari-3d-ortho-viewer widget](https://github.com/gatoniel/napari-3d-ortho-viewer/blob/e6d56314091e9eac9954613efdf161942444c4d0/src/napari_3d_ortho_viewer/_dock_widget.py):
  explicitly rejects `ndim != 3`, opens additional viewers and creates auxiliary
  volumetric slicing arrays. That implementation does not meet this task's scope.
- [NAP-9](https://napari.org/stable/naps/9-multiple-canvases.html) is provisionally
  accepted design work, not evidence of a deployed linked multiview API.

Linked simultaneous panels are not implemented by switching planes. Keep them
outside this first sequential-control scope, with any future expansion explicit.

## Acceptance and continuation

Complete scan/R1 evidence first; select declaration-targeted NRA operations and
apply a revision-checked transaction, labelling authored behaviour and proof
gaps. Then implement the command, coherent DTO/service/capability projections,
native state/capture evidence and bundled widget. Tests must cover routed
component offsets, singleton/non-singleton selectors, invalid/nonspatial axes,
planar Shapes rejection, transformed image/Labels/Points, existing navigation,
camera/isolation and plugin/MCP same-owner behaviour.

Finish with an owned isolated offscreen viewer+MCP process and unique endpoints.
No borrowed tools, ports 5690/7890, live viewer changes or analysis execution.
Run one bounded task at a time, shard tests at 60 seconds, monitor RSS and host
memory/PSI. Request main's scan-resource direction before exceeding 768 MiB;
start no heavy work below 8192 MiB available or with sustained full PSI above 1%.
PR #154 stays draft; issue #152 remains open until acceptance evidence exists.
