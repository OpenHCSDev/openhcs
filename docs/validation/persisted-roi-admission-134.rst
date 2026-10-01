Persisted ROI directory admission: receiving investigation
========================================================

Singer owns this receiving investigation under issue 134. Main audited:
``889bca2e1f69ef6bfb50ded599903c23b019ccbb``. Completed issue 398 and PR 399
remain closed; their ordinary saved-image reader/reopen acceptance is unchanged.
This checkpoint is a source investigation, not a native ROI or biological pass.

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

Pending bounded source checks. No production files have changed. Original public
errors and scientific artefacts remain in Dalton's root. The receiving diagnostic
draft will retain exact commands, first source failures and the admitted-route
result separately. Diataxis reference style separates verified facts from the
future implementation and installed acceptance boundary.
