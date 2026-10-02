# Input preparation checkpoint

Implementation owner: Lovelace. Integration owner: OpenHCS coordinator.
Branch: `fix/input-preparation-20260929`.
Worktree: `/home/ts/wt/openhcs-input-preparation-20260929`.
Issues: #172, #132 and runtime follow-through #224.

## Bundle-only cache and responsive inspection checkpoint: #224

Issue https://github.com/OpenHCSDev/openhcs/issues/224, implementation owner
Lovelace; existing drafts206/16. Parent owns disk recovery/integration, no
competing code patch. Coordinator reported fresh H001/H002 inspection creating
separate roughly859 MiB Fiji bundles through per-run XDG_CACHE_HOME, blocking
cold MCP and leaving queued10-second reads uncertain before disk-guard shutdown.
These are reported runtime observations, not worker-opened biological receipts.
No replay/restart, author coaching, installation or frozen-source/skill changes.

No old supported application projection was found: cache_root was constructor-
owned but canonical FIJI_IMAGEJ_DISTRIBUTION/FIJI_IMAGEJ_RUNTIME/BioFormats context
had no process entrypoint. Inspection lacked the existing progress declaration,
so its synchronous operation ran on the MCP event-loop thread.
Source commits: OpenHCS `101a6a4b0ec80a8ce970478399fb9527ef2f5b51`, paired
PolyStore `5e656f8c20b0949139fe1273c31390931ea7ef6d`.

- FijiArchiveDistribution declares **POLYSTORE_IMAGEJ_CACHE_ROOT** through
  cache_root_environment_key at imagej_distribution.py:357.
  cache_root_from_environment:368 decodes that owner key once into existing
  cache_root when the canonical distribution is constructed at:520. Unset keeps
  platformdirs policy; invalid explicit/relative settings fail, not fallback to
  another per-run bundle. Release/digest/overlays, checksum, lock/staging and
  runtime-policy authority remain unchanged.
- Existing OpenHCSProcessEnvironment.child_process_environment_keys at:48 derives
  the dependency owner's key, not a copied spelling/default registry. Existing
  McpDevServerSpec.environment at:300 preserves it through platform sanitization,
  independently of per-run XDG_CACHE_HOME and log/cache policy.
- Existing InspectPlatePathCapability at:2036 declares five-second progress and
  worker-thread execution. Existing MCP binding/heartbeat owns offloading and
  observability; no new task/job/progress store or tool-name switch. Optional
  downloads/cache writes/Java startup have truthful side effects and mutating
  metadata; plate contents stay read-only. Artifact-plan/viewer/config owners
  remain untouched.

Exact new entrypoint: set POLYSTORE_IMAGEJ_CACHE_ROOT to an absolute reviewed
bundle directory **before process import/start**, keep per-run XDG_CACHE_HOME,
then use normal `python -m openhcs.mcp --surface full` or McpDevClient. This
requires the reviewed pair; the unchanged frozen installation does not support
the new projection. No real bundle was relocated. Do not configure retroactively
or restart/replay a live/uncertain process. Coordinator owns future startup.

Executed **28 passed in5.07s / peak driver RSS267.4 MiB**:17 existing distribution
cases, six new root cases and five application projection/progress cases.
New files: external/PolyStore/tests/test_imagej_cache_environment.py,
external/PolyStore/tests/imagej_cache_process_fixture.py,
tests/unit/agent/test_plate_inspection_cold_runtime.py.
Two fresh Python processes import actual canonical distribution/runtime with
verified assigned paths. Only external host/artifact response is controlled: a
tiny local ZIP with real SHA-256, no overlays/JVM. Production verification,
lock/staging/discovery/reuse run. Independent XDG/log roots stay distinct;
verified download counts[1,0], one bundle directory, no temporary download
residue. Not a real859 MiB/Fiji/JVM performance claim.

Actual in-process FastMCP binding/service invocation completes canonical
capability discovery while controlled inspection I/O is held on another thread.
Existing progress helper emits started/running and propagates the identical
terminal error. No MCP process/listen startup, JVM, GUI, remote download,
environment creation or paid provider. Not a continuous installed cold journey:
real stdio progress-token/queued reads, Java and live acceptance remain gates.

Retain first10-pass/1-failure run4.91s/280.1 MiB: registry correctly rejected
effects without mutating metadata; fix declaration, not validator/assertions.
Two unused asyncio-option warnings with plugin autoload disabled. New tests,
helper and touched child source pass Ruff; six touched files parse, both diffs
pass whitespace. Whole environment-file Ruff reports untouched S110/BLE001 in
is_headless_mode; no broad clean claim. Driver uses recorded interpreter/explicit
parent and eight submodule src paths, verified imports, OpenHCS bootstrap before
pytest, disabled plugins/conftests and `-q --tb=short --noconftest
--import-mode=importlib -p no:cacheprovider -o addopts=`; shell45s bound.
Guard10.6 GiB available/historical swap11.9 GiB; explicit8 GiB admission,
final10.2 GiB. RSS is this driver, not continuous fleet peak-RAM evidence.

Owned316 KiB tiny ZIP/cache/empty fixtures at the recorded scratch path removed
after results retained. A force-style cleanup was denied before execution; normal
non-force recursive removal of the validated exact owned path completed. No
source, saved sessions or blind data/output removed. All finite handles terminal;
no scientific validation-lock takeover. Original141-pass/26-failure receipt and
**not-run** after-change ROI profile remain open. Recorded gitlink staysf94bbbe;
validated paired adoption, normal main integration, preservation/profile and
installed/live acceptance await the next finite coordinator handoff. No closure.

NRA/catalog receipt: BOUND-2/6 keeps cache_root/canonical distribution as config
authority; process consumers reference its declaration. MEMB-2/3: no second
environment/default registry, companion roster or cache copy/symlink. IMPL-1/4/13:
capability consumes existing generic progress/worker mechanism, not another
dispatch/job store. New root/run-cache values need configuration, not consumer
edits. Focused source/AST/contract checks only, not full NRA/native proof. Existing
ROI ownership and both previous review corrections remain intact.

## Independent review follow-through: physical admission and Java lifecycle

Review: https://github.com/OpenHCSDev/openhcs/pull/206#issuecomment-5897315214.
The complete comment reviewed parent `006361ff2`, recorded child `f94bbbe`, and
ROI source `8c886e7`. Both returned production findings were valid, despite the
earlier scoped review below. Lovelace picked up both; no competing owner/PR.
Current source commits: OpenHCS `32a2b27e22220b28f4a75db1977973aa61384a10`,
paired PolyStore `0aa057bc3b4241d77f5f3905e10e31efe2ee87e4`.

1. IMPL-12 / BOUND-2: `NamedSourceBinding.physical_path_matches` at
   `source_bindings.py:963` owns explicit-source resolution/equality and delegates
   path clauses to `SourceSelector.path_filters_match:706`. That selector calls
   the existing matcher/target-resolver families through `source_filters_match`.
   Discovery (`SourceBindingsConfig.discovery_path_matches:1868`) and final
   projection (`SourceBindingWorkspaceProjector.candidate_matches_binding:965`)
   both invoke the same binding operation. Delete their duplicated exact-path
   procedures and selector-filter loops, plus the projector's unused matcher
   import. Config still owns global filters and alias union; the projector still
   owns decoded metadata/components. A binding path-policy change now needs one
   owner edit instead of synchronized consumer edits. No filename registry,
   companion roster, raw record or metadata mirror.
2. IMPL-13 / BOUND-2: `BioFormatsJavaContext.is_single_file:158` owns the decoder
   capability. Both it and existing `declares_path:153` use context-owned
   `_probe_reader:168` for initialization, construction and unconditional close.
   OpenHCS calls `context.is_single_file` at `bioformats_adapter.py:791`; delete
   its entire `_is_single_file` helper and the fixture's imitation reader lifetime.
   A compound reader remains discoverable when its entrypoint fails path filters;
   decoded companion provenance remains available for final selection. Source
   admission policy stays OpenHCS-owned. No setId/OME metadata open in the probe.
   The existing valid ROI ownership/optimization is unchanged by this follow-up.

Light executed evidence: **28 passed in 0.50s**, peak Python RSS **72.8 MiB**.
`tests/unit/test_source_binding_path_admission.py` has 16 behavior cases plus one
AST guard: relative/absolute/file-URI exact identity, directory-regex/OR-group
clauses, unknown metadata/component deferral, decoded companion filters without
replacing exact entrypoint identity, and unrestricted alias union without erasing
another alias's restrictions. `external/PolyStore/tests/test_bioformats_java.py`
has four existing context cases, six new true/false/failure/retry probe cases and
one AST guard. Controlled external Java responses exercise actual context
initialization and close, not a JVM. Guards prevent the reviewed consumer bypasses
and prevent probe operations from copying construction/close instead of using
their shared context lifetime. New tests and touched child source pass Ruff;
both repository diffs pass whitespace checks. No full NRA scan/global proof.

Driver: recorded interpreter with explicit worktree/eight submodule src paths,
verified actual OpenHCS, SourceBindings/projector, PolyStore Java, ObjectState and
metaclass-registry imports. Import the existing `openhcs` entrypoint first, then
`pytest.main` with `-q --tb=short --noconftest --import-mode=importlib
-p no:cacheprovider -o addopts=` and the two files above. Automatic plugins
disabled; shell bound 45s. No global application fixture/viewer cleanup, MCP,
JVM, GUI, environment creation or shared validation-lock acquisition. Two pytest
warnings report unused asyncio configuration with plugins disabled. Initial
26-case run passed before adding the two ownership guards (0.23s/67.1 MiB).

Resource guard: 11.4 GiB available / historical swap warning 11.9 GiB; explicit
8 GiB admission checked. Final available RAM 11.2 GiB; not a continuous peak-RAM
claim. Confucius's runtime/lock/frozen installation were not touched. Tiny scratch
owner Lovelace, purpose empty source fixtures, path
`/home/ts/.cache/agent-scratch/openhcs-issue-input-20260929`: 92 KiB removed after
retaining results. No source, biological input/output or saved session removed.

These 28 contract/guard passes **do not resolve** the original combined-suite
**141 passed / 26 failed** result. Separate-context application preservation,
the retained sixteen-container/AUTO/real-TIFF controls at this new source pair,
the after-change bounded ROI profile, real Java capability/CZI fidelity and
installed user-path acceptance remain open for a coordinator-handed-off finite
slot. The profile did not run. The recorded gitlink remains `f94bbbe`; the new
OpenHCS call requires the paired context commit before integration. Coordinator
owns validated gitlink adoption, normal main integration, merge/install and live
acceptance. No issue closure or installed readiness is claimed.

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

The paired optimization belongs to PolyStore's
`TwoDimensionalLabeledMaskROIExtractor.extract`: `regionprops` already supplies
the bbox and cached region image, but extraction separately calls `find_objects`
and constructs that binary crop again. The owner authorized the in-place change;
it is published in [PolyStore draft #16](https://github.com/OpenHCSDev/PolyStore/pull/16),
commit `8c886e7`, using those public properties and deleting the replaced scan,
crop/equality construction and cast. No new extractor/cache/registry. Source
pruning and provenance are unchanged. Scope excludes coordinator #211's
execution-session/capability write-authority repair and Zeno's #204 runtime repair.

New child regressions cover holes with nested other-parent islands,
all borders, one-pixel bridges, diagonal contact, disconnected border pixels,
zero/nonzero origins, exact contour vertices/order, parent metadata, archive
reopen, exact full-canvas masks and one bbox scan. Parent raster-only TIFF
materialization now has an additional holes/borders fixture. These new checks
passed source AST/Ruff/diff guards. At the handed-off finite validation slot,
all sixteen new child cases and fragmented materialization checks passed,
alongside four fresh real MCP journeys. The combined dependency/application
suite did NOT fully pass: 141 passed / 26 failed in 37.12s. Failed workspace
cases looked for the generic `polystore_metadata.json` after the application
wrote `openhcs_metadata.json`. Collection/bootstrap import order is the source-
supported diagnosis; separate-context preservation verification remains open.
The first attempt had 29 passes / 138 setup errors because its cleaned scratch
parent was missing. No assertions weakened. Phase profile did not run after
the failed suite, so there is no after-change timing claim.

Both finite commands are terminal; flock released; tagged audit shows no owned
pytest/MCP handles. Entry guard: 13.4 GiB available RAM / historical swap 11.9
GiB. No JVM/GUI, installation, merge or frozen-harness mutation. Next runtime
check depends on the coordinator's next slot; fresh author now has priority.

The parent recorded gitlink remains `f94bbbe8631a4c78f7ceaec72fb99671b58c9a18`.
The local isolated child retains tested source `8c886e7` plus its published
finite-validation receipt for the future paired test;
the recorded gitlink will not advance before validated paired coordinator review.
Child durable receipt: `external/PolyStore/docs/roi_region_properties_checkpoint_20260929.md`.

Fidelity limits: executed evidence checks disconnected islands, identities,
hole/border/topology contour geometry, parent metadata, archive reopen, exact
masks and int32 TIFF raster preservation. Existing polygons represent independent contours, without
a declared hole-subtraction relationship. Even if ring coordinates and parent
metadata survive ZIP reopen, that alone is not ZIP-to-raster/viewer equivalence.
MaskShape is unsupported by the existing ImageJ ROI codec. Do not invent an
equivalence algorithm. Exact masks and label TIFFs are separate evidence. 3D and
private diagnostic fidelity remain unverified. No biology/Euler output opened.

## Earlier essential catalog review (changed surface only)

Audited against fetched `openhcsdev/main` at `98d9b9d23` and the working #206
checkpoint, using the owner's current archived catalog. This is source/AST and
owner tracing, not a full NRA scan, proof replay or global clean-debt claim.
The later independent review found two bypasses this receipt missed; the
follow-through above supersedes its admission/lifecycle ownership claims.

| Pattern | Concrete owner / witness | New-case check and disposition |
| --- | --- | --- |
| IMPL-12, copied procedure | `synthetic_data.py:827`, `SyntheticMicroscopyGenerator._site_position`; both layout loops call it at 875/881. | A shared positioning change now needs one owner edit, not two copied procedures. Zero jitter/overlap and both layout families have deterministic/count tests. Duplicate layout-position procedure removed. |
| IMPL-1/2/3/4, external family dispatch | `source_matching.py:114`, `SourceFilterMatcher`; `SourceFilterTargetResolver:232`; adapter discovery uses the existing `AutoRegisterMeta` registry (`bioformats_adapter.py:556`). | Directory plus OR-group clauses and a second/unrestricted alias require declarations only, no preparation switch edits. Ordinary numeric geometry and filesystem identity checks are not kind dispatch. The speculative second detection method was deleted; existing `detect` owns extension. |
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
Cleanup completed after preserving results here: only this owned 8.1 MiB
disposable directory was removed. Fixtures can be regenerated by the tests;
there is no retained copy of the disposable output.
The handed-off finite check regenerated 4.2 MiB of synthetic fixtures; only
that disposable directory was removed after retaining the results above.
Source, PR body and evidence stay in the persistent worktree.

No merge/install performed. Installed acceptance is reserved to the coordinator.
Do not close either issue solely from source tests.

## Changed paths

Generation: `openhcs/demo/synthetic_data.py`.

Preparation: `openhcs/core/source_bindings.py`,
`openhcs/core/source_binding_workspace.py`, `openhcs/microscopes/bioformats.py`,
`openhcs/microscopes/bioformats_adapter.py`,
`openhcs/microscopes/microscope_base.py`,
`openhcs/microscopes/source_bindings_handler.py`.

ROI summary: `openhcs/processing/materialization/core.py`.

Regressions: `tests/unit/test_synthetic_generator_zero_geometry.py`,
`tests/unit/agent/test_synthetic_plate_zero_geometry_journey.py`,
`tests/unit/test_bioformats_preparation_selection.py`,
`tests/unit/test_fragmented_roi_materialization.py`.

Profile/evidence: `benchmark/fragmented_roi_profile.py`, this checkpoint document.
Paired continuation: `external/PolyStore/src/polystore/roi.py`,
`external/PolyStore/tests/test_roi_region_properties.py`,
`external/PolyStore/docs/roi_region_properties_checkpoint_20260929.md`.
Parent recorded gitlink is preserved. No reserved viewer/measurement/#211 files changed.
