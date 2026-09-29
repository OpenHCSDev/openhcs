# Input preparation checkpoint

Implementation owner: Lovelace. Integration owner: OpenHCS coordinator.
Branch: `fix/input-preparation-20260929`.
Worktree: `/home/ts/wt/openhcs-input-preparation-20260929`.
Issues: #172 and #132.

## First checkpoint: #172

Zero pixel overlap uses unrestricted cell positions, not empty random ranges.
Zero stage error uses exact grid positions, without consuming jitter draws.
Both layouts share the existing generator's tile-position behavior. Positive
jitter retains the original MT19937 sequence. No parameters are replaced with
nonzero defaults.

Focused generator regressions cover ImageXpress and OperaPhenix, native and
vendor metadata, 1x1 and 2x2 grids, requested counts, deterministic pixels and
subpixel overlap. The existing randomness controls are retained.

The continuous MCP regression uses the current real stdio entrypoint, generates
the issue's 1x1/64px/one-channel/one-Z/four-cell/A01/seed7 plate, inspects it and
samples pixels. It does not replace the transport, services or workspace owners
with mocks. It does not use a GUI, biological input or a paid provider.

## Second checkpoint: #132

`SourceBindingsConfig.discovery_path_matches` applies the declared global
filters and union of binding-local path selections before unrelated store opens.
The existing filter matcher/target-resolver families still own clause behavior.
An unrestricted alias retains discovery; metadata/component-only selectors are
not guessed from filenames. Explicit source URIs use their existing resolver.
Image-file and NGFF adapters use this declaration directly. The Java adapter
only prunes a mismatching entrypoint when Bio-Formats `isSingleFile` declares it
independent. Compound entrypoints remain discoverable; the existing workspace
projector applies global filters to decoded store provenance, including companion
paths, then resolves binding/metadata/axis selections.

The existing polymorphic `MicroscopeHandler.detect` now receives source
declarations, including during AUTO detection. No second detection interface,
filename registry, suffix-to-reader map, or companion-file roster was added.
Controlled-decoder tests use sixteen tiny physical filenames and the real
handler/orchestrator/workspace path: the explicit handler/orchestrator opens only
the selected container once; AUTO opens that selected container twice (detection
and initialization), and never opens the other fifteen. A real TIFF journey
through AUTO orchestrator initialization decodes only the selected file twice,
persists its exact reference, then loads its actual pixels. It has no substituted
decoder, JVM or orchestration implementation.

The 128x128 fragmented fixture has three parent labels (7, 42, 188), with 900
disconnected shapes belonging to label 188. Actual ROI materialization, disk ZIP
encoding and native reopen produce 902 members while preserving parent labels,
area, centroid and translated coordinate bounds. Summaries now say parent labels,
not cells. This demonstrates fragmentation, not duplicate biology. The existing
declared output-path selection can retain an exact int32 label TIFF without
calling the unselected ROI writer; its guard now has a regression witness.

Recorded PolyStore profile: cold extraction 0.292s, warm profiled extraction
0.0195s, standalone member conversion 0.0686s, archive conversion/write 0.129s.
The latter includes its required conversion; standalone conversion isolates a
phase and does not imply production does both. Three contour calls yield 902
members; two `find_objects` calls confirm a repeated whole-mask bbox scan.
These are single bounded observations, not a large-mask speedup claim.

Remaining optimization belongs to PolyStore's
`TwoDimensionalLabeledMaskROIExtractor.extract`: `regionprops` already supplies
the bbox and cached region image, but extraction separately calls `find_objects`
and constructs that binary crop again. Proposed in-place change: reuse those
existing properties, retaining labels, bbox, origin and contour ordering. No
external submodule was changed without coordinator coordination. No parallel
extractor/cache will be added in OpenHCS. The coordinator must authorize/assign
this paired submodule change before implementation and validation resume.

Fidelity limits: this fixture checks disconnected islands, identities, metadata,
coordinates and int32 raster preservation. It does not establish arbitrary
hole/border/topology rasterization equivalence, 3D fidelity, or fidelity of the
private diagnostic archives. No biological inputs or frozen Euler output opened.

## Essential catalog review (changed surface only)

Audited against fetched `openhcsdev/main` at `98d9b9d23` and the working #206
checkpoint, using the owner's current archived catalog. This is source/AST and
owner tracing, not a full NRA scan, proof replay or global clean-debt claim.

| Pattern | Concrete owner / witness | New-case check and disposition |
| --- | --- | --- |
| IMPL-12, copied procedure | `synthetic_data.py:827`, `SyntheticMicroscopyGenerator._site_position`; both layout loops call it at 875/881. | A shared positioning change now needs one owner edit, not two copied procedures. Zero jitter/overlap and both layout families have deterministic/count tests. Duplicate layout-position procedure removed. |
| IMPL-1/2/3/4, external family dispatch | `source_matching.py:114`, `SourceFilterMatcher`; `SourceFilterTargetResolver:232`; adapter discovery uses the existing `AutoRegisterMeta` registry (`bioformats_adapter.py:555`). | Directory plus OR-group clauses and a second/unrestricted alias require declarations only, no preparation switch edits. Ordinary numeric geometry and filesystem identity checks are not kind dispatch. The speculative second detection method was deleted; existing `detect` owns extension. |
| MEMB-1/2/3, duplicate rosters | `BioFormatsJavaAdapter._is_single_file` at 828 calls the decoder capability, not a hand-maintained extension/companion list. | A compound decoder response survives a nonmatching entrypoint and selects its decoded companion. A new single-file name uses the same clauses; no new filename registry or roster. |
| BOUND-1/2/6/7, bypassing decoded/config owners | `SourceBindingsConfig` at 1833/1842 owns path decisions; `SourceBindingWorkspaceProjector.candidate_matches_binding` at 966 owns decoded selectors. | Exact-source and metadata-only tests preserve URI resolution and defer unknown metadata. No raw configuration dictionary, `getattr` default, attribute-name switch or metadata mirror was introduced. AST guards verify the declaration matcher and single detection contract. |
| IDEN-2/6, conflated count/identity | ROI writer summary at `materialization/core.py:3047`; existing PolyStore parent-label metadata and archive converter retain identities. | Label 188 remains one parent with 900 fragments after archive reopen, not 900 new parents. New parent values need no relabeling/table edit. Summary ambiguity corrected; stronger topology fidelity remains open. |

Guard results: eleven changed source/test/profile files parse; focused AST checks
verify existing matcher calls/adapter registry, metadata-free `isSingleFile`
instead of `setId` in the prune capability, and absence of a second detection
contract. New tests/profile pass Ruff and `git diff --check` passes. Existing
whole-file debt and PolyStore repeated-work findings remain explicitly scoped.

## Validation and resource boundary

All eight dependency imports were verified under this worktree's recorded
submodule roots, using `/home/ts/code/projects/openhcs/.venv/bin/python` and an
explicit worktree/submodule `PYTHONPATH`. No package installation or shared
source change. Main was fetched and integrated normally before implementation.

First checkpoint: 20 tests passed in 2.32 seconds (zero geometry, randomness,
and initial preparation selections). Second checkpoint: 115 preparation,
Bio-Formats, source-workspace, plane-store and fragmented-materialization tests
passed in 15.54 seconds; the additional real TIFF orchestrator journey passed in
2.79 seconds. These are focused source checks, not a full suite or NRA proof.

Real current-entrypoint evidence: four continuous MCP health, orientation,
generate, inspect and sample journeys passed in 23.19 seconds. Layouts:
ImageXpress and OperaPhenix, each with vendor and native OpenHCS metadata.
Each returns one requested uint16 image and an 8x8 pixel sample; native
metadata records one image and the requested 1x1 grid. This uses source overlays
with verified imports, not a changed installed package or an installed acceptance
claim. New test files pass Ruff; full-file Ruff reports existing source debt.

Guards reported 12.8-14.8 GiB available RAM with a historical swap warning
(11.5-11.7 GiB used). Only small provider-free checks were run under the batch's
nonblocking lock; busy lock meant independent source work, not polling. The last
live TIFF/profile run finished and released the lock for Euler. Per the H003
priority checkpoint, no new test/JVM/GUI run starts until Euler releases validation.

Scratch owner: Lovelace. Purpose: tiny generated regression plates and pytest
fixtures. Path: `/home/ts/.cache/agent-scratch/openhcs-issue-input-20260929`.
Remove only this owned disposable output after preserving results here.
Source, PR body and evidence stay in the persistent worktree.

No merge/install performed. Installed acceptance is reserved to the coordinator.
Do not close either issue solely from source tests.
