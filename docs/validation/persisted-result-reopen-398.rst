Persisted result reopening: issue 398
====================================

Owner and boundary
------------------

Singer owns this source-only investigation on
``fix/persisted-result-reopen-20261001``, based on main ``49a95d8fb``.
Dalton owns the scientific pipeline; the parent owns installed acceptance.
No native process, installation, scientific array, or failed job is modified
or replayed by this investigation.

Original witness
----------------

The retained witness is
``neurite-development-skill383-20261001/output/ASSISTED-2-FAINT-PROCESS-QA-CHECKPOINT.rst``
under the parent's persistent issue-batch worktree. Candidate 1b intentionally
did not open a viewer after its original finalization failure. Consequently
there is no historical window-state receipt for these persisted images.

The native ``input_openhcs/openhcs_metadata.json`` nevertheless declares exact
workspace references, selected w2 source provenance, spatial metadata, and
source-artifact projections for the candidate mask and unrooted residual.
The public explicit-result inventory returns null source paths; explicit
image streaming refuses the absent historical receipt; sampling cannot find
the physical artifact in the inventory. Graph reopening separately refuses
missing native ROI source metadata. Those failures must not be bypassed with
invented snapshots, file-name inference, or a relaxed provenance guard.

Supported read-only control
---------------------------

A serial guarded source invocation of the real ``PlateInspectionService``
queried the native output root using ordinary automatic microscope detection,
image inventory, no previews, and a read-only path policy. It returned zero
images and ``plate_image_file_listing_failed``: multiple metadata
subdirectories exist but none is marked main. Runtime was 3.72 s, peak RSS
233288 KiB, exit 0, within a one-CPU/512 MiB/60 s scope. No viewer or subprocess
was allowed. This is source evidence, not installed acceptance.

Earlier import/constructor/wrong-microscope harness failures are retained
separately; they do not establish product defects. Original raw logs remain
in the owned ``persisted-result-reopen-20261001`` scratch directory pending
byte-exact archival with the completed source suite.

Ownership crossings
-------------------

PR394 owns runtime payload and materialization files. Its graph ROI renderer
currently constructs ROI content without the existing archive source-metadata
binding. This investigation has not edited that shared file. PR397 owns
selected-plane output declarations; no consumer axis workaround is permitted
here. Neither PR claims inspection/streaming services or native read-only
metadata projection. Issue398 links the original broader issue134.

Architecture and acceptance
---------------------------

Reuse the native metadata handler, virtual source-workspace projection,
inventory, original image loader/sampler, and ROI metadata codec. Shared
behavior stays with those owners; no parallel receipt schema, registry,
projection store, path-guessing loader, or consumer type roster is allowed.
Applicable audit patterns are BOUND-1/2, IDEN-1, and IMPL-4/12/13.

Required source acceptance is an ordinary public inventory/sample/reopen
journey from declared persisted metadata with a misleading image name and
more than one output branch, with no historical viewer receipt. Unbound
images and ROI archives must remain rejected. A new declaration must work
without changing generic consumers. Live installed acceptance remains with
the parent. The source checkpoint below completes the image route, not graph
recovery or installed acceptance.

Working source checkpoint
-------------------------

Production head ``6cea76331ebc16a5299754592f2bf43893f84310`` changes only
``openhcs/microscopes/openhcs.py``. It deletes 39 production lines and adds 24.
The existing ``OpenHCSMetadataHandler._metadata_projection`` owns choosing
explicit input authority versus conflict-checked read-only output aggregation.
``workspace_mapping_metadata`` now uses that same decision; the aggregate
projects workspace mappings through its existing conflict-checking merger.
The duplicated JSON reader in ``_load_metadata`` was deleted: the original
``_load_metadata_dict`` owns decode/cache/error handling for both projections.
There is no new schema, loader, registry, facade, consumer switch, or binding
store. The existing metadata handler/IO-base MRO remains unchanged; no new
independent capability required a new base. Existing cooperative full-window
request hooks are exercised by the regression shard, not only inspected.

Required relation: every admitted native reference retains the original
typed projection and source identity through inventory, bounded sampling,
and the existing image stream. A read-only output view must not manufacture
a pipeline main input. The two-branch fixture uses source-artifact declarations
and misleading checkpoint filenames; a third independent alias works by adding
only its declaration. Generic inspection, sampler, loader, stream, and viewer
consumers have zero edits. Conflicting addresses, incompatible backend owners,
and an explicit main branch without a mapping remain refused.

Public route for parent acceptance
----------------------------------

Use the metadata-owning ``input_openhcs`` root as ``plate_path``, ordinary
``kind='image'`` inventory/streaming, and the exact declared checkpoint image
path returned by inventory. Do not pass ``result_directory`` or synthesize a
``source_receipt`` for this native source-workspace route. The original public
tools are ``openhcs_query_plate_files``, ``openhcs_sample_plate_image``, and
``openhcs_stream_plate_files_to_viewer``. The sampler already admits the exact
physical path as well as the virtual name when inventory declares it.

A metadata-only source invocation against the retained candidate now returns
9 image records, no errors/warnings, including candidate_mask and
unrooted_residual with exact physical pixel addresses and channel2 source
metadata. It took 3.48 s / 228820 KiB. No image previews or scientific pixel
arrays were loaded. The native document still records source-binding plane
semantics; this patch does not reinterpret historical axes. PR397's selected
plane declarations remain separately owned. Actual parent-installed loading
and same-coordinate QA must qualify those persisted semantics.

The explicit result-directory receipt guard is unchanged and tested: a real
but undeclared image still fails before launching a viewer. This is recovery
of the original typed native inventory route, not weakening that boundary.

Graph boundary
--------------

The graph archive's source metadata is separately missing at its original ROI
writer. Native image mappings do not declare a graph binding; filenames cannot
fill that gap. Strict ROI refusal is retained. A narrow shared-renderer release
was requested on PR394 (comment5939735640); no materialization, runtime graph,
axis, or source-binding file was edited. Existing issue134 tracks that broader
workflow; issue398 and PR399 deliver the image reopening portion. There is no
claim that this repairs an already-unbound historical graph archive.

Bounded evidence
----------------

All executed source checks were serial, provider/plugin-free, one CPU,
512 MiB cgroup memory plus zero swap, and a 60 s outer deadline, using the
existing read-only private interpreter and original ABI dependencies. Paired
pyqt source import is pinned at ``ad4948775ab81180a354d4b793d17ee5ddff3972``.
No environment, native process, installation, or scientific run was changed.

* Original red: 3 failures at the real no-main boundary, 4.75 s / 244968 KiB.
* First fix: 3 PASS, 4.47 s / 247848 KiB.
* Expanded guards: 6 PASS, 4.42 s / 249712 KiB.
* Shared-loader/invalidation and unbound receipt guard: 8 PASS,
  4.41 s / 245472 KiB.
* Final compatibility shard: 18 PASS, 45 explicitly deselected unrelated
  tests, 5.17 s / 252472 KiB. Includes the continuous public image route,
  independent declaration, native calibration, original crop/window validation,
  explicit ROI request binding, no-main inspection, and type-parametric codec.
* Original R0 is unchanged ``agent_comms.debt_ratchet`` at pinned
  ``3b03785f45df2ef5dc62ba6aed99294192ecbb01``. First R0 failed honestly at
  ``5672afa40``: class-line excess increased from183 to191. This is an eight
  line increase, not eight statements. Original reader duplication was removed
  at its actual owner rather than changing the measure or omitting the file.
  Final R0 at ``6cea76331`` against main ``49a95d8fb`` PASS,
  14.43 s / 87640 KiB; excess falls183 to168, all other deltas zero.
  Every changed production path is included (the one native metadata file).
* An original NRA full-context attempt used pinned
  ``673c062fc656e9c74f1eddcab30f036c9befbc1f`` with selected native handler,
  ``--context-root openhcs --json --raw-findings --json-payload full``, single
  parse/analysis worker, and no cache. The scope failed ``oom-kill`` at
  MemoryPeak536870912 and exit143 before producing JSON. No bound was raised,
  source excluded, detector copied, or completion inferred. Its original empty
  output and failure log are retained. Global NRA/R1 coverage is unresolved
  under this bound; the receipt instead records the exact ownership trace,
  antipatterns, original R0, and behavior evidence at their actual strength.

Archive and cleanup
-------------------

``docs/validation/persisted-result-reopen-398-source-20261001.tar.gz`` retains
all original raw harness/product failures, positive-growth R0, passing source
logs, the original full-context NRA empty output and OOM scope observation,
the exact read-only inventory command, and the original red synthetic fixture
files. SHA256:
``7c1f69c9663445e9a489a86d593eaefe5dc1b71bceb1cac183058b2f3d6502ee``.
``tar -d`` compared the archive against every original and passed. Original
pytest whitespace stays byte-exact in the archive, not loose versioned logs.
Whole-PR ``git diff --check`` passes.

All check sessions terminated; the failed NRA scope reports an empty
ControlGroup. The owned disposable root
``/home/ts/.cache/agent-scratch/persisted-result-reopen-20261001`` contained
3,385,366 logical bytes (4.3 MiB allocated). It is released after verified
archival; source/history and all parent scientific inputs/outputs remain.
This does not overlap Lorentz's worktree cleanup.

PR399 is a visible source checkpoint. Parent installed public-tool acceptance
is pending; no live-readiness, historical graph recovery, or global NRA
completion is asserted.
