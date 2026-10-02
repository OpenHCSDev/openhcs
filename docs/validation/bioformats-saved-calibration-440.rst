Saved-source calibration440 receiving receipt
============================================

Status and ownership
--------------------

Singer owns the BioFormats calibration boundary for issue440, alongside the
independent native graph ROI receiving acceptance on draft404. Parent owns paired
installed integration and eventual ordinary public raw/result reopening. Root
retains394's shared source metadata, projection, publication and materialisation
owners. Dewey owns441's stream transport boundary; Planck owns the scientific run.

This branch starts at main8551a48644b5a9cd054ca1c738ffef2295c5266f in the existing
persistent worktree. Root394 was checked at130c03a26684a2f3b6eb262e3ede7b2ce31bed64:
``bioformats.py`` and ``bioformats_adapter.py`` have no394 production changes.
No shared394 file is changed, no environment or package is modified, and no live
viewer or scientific run is accessed. Previous404 evidence and its untracked
``.qa134-graph-20261002`` directory remain intact.

Original witness
----------------

Issue440 retains the installed development-only CZI witness under
``/home/ts/wt/openhcs-issue-batch-20260929/rbpms-r0010-development-434-20261002``.
``output/CONTINUATION02-QA-RECEIPT.rst`` records original source XY spacing
0.12353054911059548 micrometres/pixel, persisted input/candidate03 numeric spacing
1.0, and reopened raw/ROI native scales1.0. That is an engineering failure, not
biological acceptance. The retained metadata document was inspected read-only;
the CZI, result pixels, ROI geometry, reference and held-out inputs were not read.

Required relation and existing owners
-------------------------------------

The calibration declared by a BioFormats image must accompany every exact plane
candidate through source binding and persistence. An absent OME calibration must
remain unspecified, not become an invented physical micrometre measurement.

``BioFormatsStoreMetadata.source_dataset`` retains ``BioFormatsImage.pixel_size``
on ``SourcePlaneDataset``. Its ``_image_candidates`` currently emits only image,
sample and component identity, omitting ``SourceVoxelSpacing``. The original
``BioFormatsHandler._write_dataset`` hands those candidates to
``SourceBindingWorkspaceProjector`` and ``AtomicMetadataWriter``. The latter's
``_update_projection_geometry`` recomputes numeric spacing from the persisted
plane metadata; the existing ``SourceVoxelSpacing.metadata_pixel_size`` correctly
returns1.0 for the unspecified candidates. Fix the producer, not that strict
shared derivation or a receiving viewer scale.

The current NRA skill and authoritative refactor-audit archive were read.
BOUND-8 applies: a richer source fact is dropped when its owner emits candidates.
BOUND-2 prohibits bypassing ``SourceVoxelSpacing`` with an independent calibration
table. IMPL-12/13 prohibit a copied metadata writer or viewer-only mechanism.
No new consumer format/type switch, registry or parallel source store is needed.

Original source checkpoint
--------------------------

``tests/unit/test_bioformats_saved_calibration_440.py`` supplies a new non-plate
OME header declaration through the existing controlled Java fixture. The ordinary
BioFormats discovery, named C2 binding, workspace preparation and metadata writer
run unchanged. No JVM, Fiji, decoder or pixel read is supplied by this fixture.

Original main: two failures at persisted spacing1.0 versus declared0.65/0.217,
one passing unspecified-calibration control. Elapsed5.16s, peak276072KiB RSS,
zero swap; kernel scope MemoryMax512MiB, MemorySwapMax0, CPUQuota100%, affinity
one CPU and external60s timeout. Provider/pytest-plugin autoload disabled.
The byte-exact log is archived in
``bioformats-saved-calibration-440-source-20261002.tar.gz``; loose originals stay
in owned ``.qa440-calibration-20261002``. No cleanup is authorised in this task.

The final source journey will extend the same fixture through original runtime
image metadata and the registered native ROI writer/reader. Source tests do not
establish installed/native readiness. Parent's remaining acceptance is a freshly
prepared ordinary saved-source/raw/result journey, comparing typed units and
native transforms with its original source authority after the live freeze ends.
