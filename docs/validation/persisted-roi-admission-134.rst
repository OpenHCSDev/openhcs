Persisted ROI directory admission: receiving investigation
========================================================

Singer owns this receiving investigation under issue 134. Main audited:
``889bca2e1f69ef6bfb50ded599903c23b019ccbb``. Completed issue 398 and PR 399
remain closed; their ordinary saved-image reader/reopen acceptance is unchanged.
This checkpoint is a source investigation, not a native ROI or biological pass.
Visible draft: https://github.com/OpenHCSDev/openhcs/pull/404.

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

Remaining boundary: PR 394 must release the narrow shared target/publication seam
or integrate this relation with its existing successful-save batch authority.
Singer retains this receiving regression and the separate graph metadata crossing.
No copied capture/materialization algorithm, compatibility reader, parallel
registry, invented source receipt or scientific replay was introduced. Diataxis
reference style keeps the verified admission facts distinct from implementation
and installed acceptance.
