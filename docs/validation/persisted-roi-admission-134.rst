Persisted ROI directory admission: receiving investigation
========================================================

Singer owns this receiving investigation under issue 134. Main audited:
``889bca2e1f69ef6bfb50ded599903c23b019ccbb``. Completed issue 398 and PR 399
remain closed; their ordinary saved-image reader/reopen acceptance is unchanged.
Current source status: Root integrated the publication requirement in PR394
``82243634ce097d0d1a2d9e77664cbfeac3e6ec94``. Singer accepted the exact diff and
receipt against the receiving requirements. Root owns the integrated seam; no
shared-file release remains pending. Draft404 retains evidence and the parent
native ROI provenance/reopen gate, not a competing source implementation.
The distinct remaining graph writer omission now has a tested source-bearing
ZIP proposal in ``graph-roi-source-roundtrip-134.rst``. Root retains production
core.py ownership; narrow writer integration/release was requested through394.
Historical investigation below is not a native ROI or biological pass.
Visible draft: https://github.com/OpenHCSDev/openhcs/pull/404.
The historical implementation proposal superseded the initial diagnostic-only
checkpoint and is now superseded by Root's integrated checkpoint. Its original
qualification and current receiving acceptance/native-boundary receipt is
``persisted-roi-only-owner-134.rst`` in this directory.

Original public witness
-----------------------

Dalton's retained root is
``/home/ts/wt/openhcs-issue-batch-20260929/neurite-development-skill383-20261001/output``.
``assisted-2-candidate-2-isolated.stdin:45`` requests
``openhcs_stream_plate_files_to_viewer`` with the candidate-2 output plate,
``kind=result`` and the exact physical
``results/A01_s001_w2_z001_t001_neurons_step0_rois.roi.zip``.
``assisted-2-candidate-2-isolated.stdout:44741-44789`` retains
``plate_file_stream_failed`` / ``PlateFileRecordNotFoundError`` with zero resolved
records. No request was replayed or native/viewer endpoint touched here.

The native ``assisted-2-candidate-2-sensitivity-diagnostic/input_openhcs/openhcs_metadata.json``
contains four saved-label image projections under ``results`` and five checkpoint
image projections under ``images``. Neither branch declares ``results_dir``.
Only metadata, retained transport receipts and filesystem names were inspected.
Scientific pixels, ROI geometry and held-out sources were not read.
Metadata SHA256 at inspection:
``69b83da2d22197ef6af073cf7a97c53efa5e249694c5fecdc78a4cf0285469b2``.

Required relation and existing owners
-------------------------------------

A compiled persistent artifact destination must publish its result-directory
identity through the existing metadata contract so ordinary result inventory can
admit the actual saved ROI archive. An output branch's spelling is not evidence
that it is a result directory.

``RuntimeArtifactMetadataTarget.from_plan`` receives the exact compiled artifact
analysis directory but supplies ``results_dir=None``. Its production destination
selection is image-only. ``OpenHCSMetadataWriter.OutputTarget.write`` owns shared
publication; ``AtomicMetadataWriter.publish_source_projection_metadata`` already
supports the existing result-directory field. ``OpenHCSMetadataHandler.analysis_result_directories``
correctly admits only that declaration. ``PlateResultFileInventory`` owns the
single registered-format record projection. No reader fallback or parallel store
is warranted.

PR 394 claims ``core/steps/function_outputs.py`` and its original tests, together
with the materialization batch/outcome authority. Narrow target/publication hook
ownership was requested at
https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5941747455.
Those shared files remain untouched pending that coordination. The older graph
renderer/native ROI source-metadata omission is a separate crossing already
recorded there; it is not silently repaired by admitting a directory.

The proposed repair preserves the shared publication algorithm on ``OutputTarget``
and minimal destination/participation hooks on the runtime artifact leaf, consuming
the original saved materialization outcomes. It must include ROI-only outputs and
nested declared destinations, without a concrete-consumer switch or second render.
Catalog review: BOUND-8 identifies the declared destination lost at publication;
MEMB-2 cautions against an image-only roster standing in for persistent result
participation; BOUND-2 forbids bypassing the existing inventory/source metadata
owners. Existing source projection and ROI provenance safeguards stay intact.

Existing explicit route
-----------------------

The supported typed selection carries the original output ``plate_path``,
``kind=result``, the explicit canonical ``result_directory`` ending in
``assisted-2-candidate-2-sensitivity-diagnostic/input_openhcs/results``, and the
original exact ROI ``file_paths``. No acquisition-component filter is supplied.
For read-only inventory qualification, ``include_previews=false`` avoids reading
ROI geometry or images. The receiving check exercises this original service and
record resolver without invoking streaming or native processes. Path admission
does not prove that the archive's separate native ROI source-metadata contract
passes; no historical snapshot/source receipt is fabricated.

Qualification
-------------

The retained explicit-directory service query passed: 17 admitted result records,
exact neurons archive resolved as ROI, no previews. The original metadata handler
still returns zero ordinary result records. This verifies the supported selection
contract, not native ROI source provenance, streaming or scientific interpretation.

Two mixed-image/ROI synthetic cases use the real ``RuntimeArtifactMetadataTarget``,
its shared writer, atomic projection store and original metadata handler/inventory.
The original typed projection publisher seeds a synthetic image address; file
contents are sentinels never loaded. Both ``declared_outputs`` and
``nested/independent_outputs`` fail with an empty result inventory despite the
persisted exact ROI. This establishes the missing publication relation without
filename inference. Independent destination names alone cannot repair it today;
new-declaration/cooperative-hook acceptance belongs to the coordinated source
repair and has not been claimed here.

Serial final diagnostic run: 1 passed, 2 failed, exit 1, 4.88 seconds elapsed,
235804 KiB maximum process RSS. All runs used a kernel scope with
``MemoryMax=512M``, ``MemorySwapMax=0``, ``CPUQuota=100%``, CPU affinity 0 and a
60-second outer timeout. Plugins and providers were disabled. Two pytest config
warnings concern disabled asyncio plugins. Existing Python/ABI dependencies and
the pinned pyqt source were read-only; no installation, startup or native call.

First collection failure is retained: receiving harness imported a nonexistent
``polystore.storage_backends`` module. It was corrected to original
``polystore.disk``. The next direct ROI-only fixture reached the original strict
``SourceProjectionSet requires at least one projection`` guard; it lacked the
saved image authority present in the actual mixed run and is not presented as the
installed missing-directory proof. Its input and failure remain intact. The final
mixed fixture supplies that authority through the original typed publisher and
fails at directory admission itself, as above.

``docs/validation/persisted-roi-admission-134-source-20261001.tar.gz`` contains all
three byte-exact raw source logs, each original check-input version and synthetic
failed fixtures. ``tar -d`` verified it against every loose original.
Archive SHA256:
``5d01ecf1a408f8bd98053ba8d4d287b8b429dcd020f3e96304f1e8e41cfcb5d3``.
Full guarded commands and process receipts are in the logs. Original public errors and
scientific artefacts remain in Dalton's root, outside this archive. No production
paths changed, so no new production R0/R1 or global NRA pass is asserted. Whole-PR
``git diff --check`` applies to source/docs; authentic raw logs remain inside the
archive without whitespace rewriting.

Only the owned disposable scratch root
``/home/ts/.cache/agent-scratch/persisted-roi-admission-134-20261001`` is released
after verified archival and source-worker termination: 39751 logical bytes,
160 KiB filesystem usage. No other worktree/cache, native owner,
scientific output or uncertain input is removed.

The former shared-owner boundary is resolved: Root integrated the relation with
the existing successful-save batch authority at the source checkpoint named above.
Singer retains the receiving evidence and separate native/graph acceptance crossing.
No copied capture/materialization algorithm, compatibility reader, parallel
registry, invented source receipt or scientific replay was introduced. Diataxis
reference style keeps the verified admission facts distinct from implementation
and installed acceptance.

Historical implementation: exact shared owner proposal
------------------------------------------------------

Parent requested continued repair, not diagnostic-only completion. Public PR 394,
issue 384, their tracked source receipts and commit metadata still identify the
shared human GitHub account rather than a named acting agent/contact. The receiving
source remains under Singer's ownership; no foreign worktree or production file
is edited while the shared hunk crossing is unresolved.

``docs/validation/persisted-roi-directory-owner-134.patch`` exposes the actual
first repair checkpoint, three hunks in ``core/steps/function_outputs.py``:

* Existing ``RuntimeArtifactMetadataTarget.from_plan`` declares its independently
  compiled persistent analysis directory as ``results_dir`` rather than losing it.
* Its existing ``for_directory`` hook carries the exact destination through each
  production/reconciliation directory projection.
* Existing shared ``OutputTarget.write`` publishes the full plate-relative
  directory instead of dropping nested ancestry through ``Path.name``.

The proposal removes three expressions and adds eight source lines. No renderer,
capture loop, consumer, registry, source-binding, axis, scientific parameter or
historical reader changes. The generic publication algorithm stays on the existing
ancestor; two minimal destination hooks stay on its existing leaf. The proposal
preserves PR 394's once-saved batch outcomes and its geometry reuse. Applicable
review cautions remain BOUND-2/BOUND-8 and MEMB-2, with IMPL-12 explicitly excluding
another publication/materialization procedure.

The hunks pass admission against both the main-derived owner and PR 394 pinned
``fdf50241aa9adc6d96bc9c530dcc9acd19692b64``. Initial published patch at
``4510610a8`` included normal blank context and passed default ``git apply --check``.
The final patch omits unused blank context; its exact admission recipe is
``git apply --check --unidiff-zero docs/validation/persisted-roi-directory-owner-134.patch``.
The corresponding ``--directory=.qa134-proposal-20261001/pr394`` check qualifies
the separately archived PR 394 source. Default admission of that minimal-context
format refuses a hunk; this original formatting control is retained separately
and is not a product failure. The resulting production-code blob is unchanged.

The receiving proposal is visible to the integration owner at
https://github.com/OpenHCSDev/openhcs/pull/404#issuecomment-5942252207 and the direct
crossing/contact request at
https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5942252441.
This remains a repair in progress, not an acceptance or completion claim.

Behavioral new case and proposal qualification
----------------------------------------------

The source projection copies only the selected owner file into an owned persistent
disposable directory in the existing worktree. The explicit proposal selector
loads that file before collection; the original runner still owns read-only ABI
preparation and provider/plugin-free pytest invocation. No product method/class
or assertion is mocked or rewritten. The selected source path is printed in the
raw receipt. Other imported OpenHCS files come from the original receiving source.

The original unchanged two mixed writer/reader reds become two passes. An independent
``SupplementalResultMetadataTarget`` supplies only its destination declaration;
original family discovery selects it with no consumer/roster edits. Its declared
MRO composes an independent publication audit capability, the original
``ProducedImageMetadataCapability`` and the original ``OutputTarget`` owner.
Cooperative ``super().write`` executes before/after audit around the shared writer;
the original image capability executes its real record hook. Public
``PlateInspectionService.query_files(kind=result, include_previews=false)`` then
admits the exact ROI for simple and nested supplemental destinations. This exercises
capability hooks and resulting user-visible inventory, not inheritance assertions.

Unmodified-owner new-case control: 1 pass / 1 fail, 5.67 seconds elapsed,
288748 KiB maximum process RSS. The nested declaration loses its result directory
because the original ancestor takes only its basename. Original raw failure retained.

Projected owner qualification: 4 passes / 1 explicit deselection, 3.90 seconds
elapsed, 230468 KiB. It covers the original two mixed-output reds and both new
declaration cases. The already-completed retained explicit-directory admission
check is deselected, not replayed. A subsequent distinct exact-destination
``for_directory`` case passes, 3.70 seconds / 236336 KiB, two previously completed
unit cases deselected. Five distinct behavioral cases pass across these shards;
no broad suite, native ROI geometry, installed streaming or biological claim.

Original pinned R0
------------------

Unmodified original guard owner:
``/home/ts/wt/comms-ratchet-pinned-ui348-20261001`` at
``3b03785f45df2ef5dc62ba6aed99294192ecbb01``. Command uses Python 3.14 and
``python -m agent_comms.debt_ratchet --root openhcs --base de0d76b7a9b5177a0630c91487a039370ae81dc7 --head bbd059114d6ce32a97095f9d73b902e39e3854c4``.

The head is the exact unapplied proposal tree, not the receiving PR's production
head. A separate temporary Git index creates that tree without changing the
working source/index or any ref. Its sole production delta is
``openhcs/core/steps/function_outputs.py``; every changed production path is included.
The projected file hash and Git blob both equal
``c6cea8754affd4fd38714f3ceed007922addd3e4``. The commit object and selected source
are archived so the exact qualification input survives even without a live QA ref.

R0 PASS, exit 0, all deltas zero and no positive entries; 14.72 seconds elapsed,
87436 KiB maximum process RSS. Original detector/bound/root is unchanged. Source
shards and R0 use the same one-CPU, kernel 512 MiB/no-swap and 60-second bounds.
The original full-context NRA/R1 resource failure recorded with the earlier
receiving work is not converted into a global architecture pass here. After shared
integration, qualification must identify the actual resulting production head.

Archive, cleanup and next integration boundary
----------------------------------------------

The byte-exact archive
``docs/validation/persisted-roi-owner-proposal-134-source-20261001.tar.gz`` retains
the original new-declaration red, projected positive shards, complete original R0,
formatting control, exact input versions, failed synthetic files and both selected
owner-source versions. It excludes scientific inputs/outputs and foreign caches.
The archived temporary index and commit record document source projection, not
another registry/store. ``tar -d`` verifies all loose originals before cleanup.
Raw log whitespace is preserved inside the archive. Diataxis reference style keeps
this projection evidence separate from actual applied/installed status.

The resource-headroom check reported critical disk headroom; no new agent, environment,
installation, download, full snapshot or large test was started. Only the bounded
serial source checks above ran. The owned source-projection directory is released
after archival; exact size and archive digest are recorded below.

Archive SHA256:
``4a17d826c4bb9768b5b2455be547f981277173abe1a7beeba1f6716cb4c237e7``.
Released only
``/home/ts/wt/openhcs-knowledge-lazy-conversion-20261001/.qa134-proposal-20261001``:
2364599 logical bytes, 2.6 MiB filesystem usage. Selected proposal source, original
failures, raw receipts and reconstruction inputs remain recoverable in the archive;
tracked receiving source/history and all foreign/scientific data remain intact.

Root is the integrated PR394 owner; the combined proposal is superseded. This first
checkpoint repairs the actual mixed-label/checkpoint/ROI witness. ROI-only
participation and the empty-image transaction now have the independently tested
saved-output-owner proposal documented in the linked receipt; the older graph ROI source-metadata omission remains
its separate crossing. Neither is hidden behind relaxed reader guards, guessed
paths, fabricated receipts or a biological replay. Parent's ten viewer-QA lines,
manifest tags and query checks remain disjoint and untouched.
