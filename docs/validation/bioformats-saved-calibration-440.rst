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

At original main, ``BioFormatsStoreMetadata.source_dataset`` retained
``BioFormatsImage.pixel_size`` on ``SourcePlaneDataset``. Its ``_image_candidates`` emitted only image,
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

Working production checkpoint
-----------------------------

Production head: ``bde6f5760``. Only
``openhcs/microscopes/bioformats_adapter.py`` changes:20 lines removed,40 added.
``BioFormatsImage.source_voxel_spacing`` replaces its stored scalar; the numeric
``pixel_size`` view derives from that typed authority. All candidate publication
uses the existing common ``BioFormatsStoreMetadata._image_candidates`` procedure
and ``SourceVoxelSpacing.merge_into``. There is no second calibration authority.
The old ``_normalized_pixel_size`` procedure and its default-as-physical ambiguity
are deleted. The existing Java decode boundary converts actual OME length objects
into micrometres using their own ``value(target_unit)`` operation, as specified by
the `original BioFormats physical-size example
<https://github.com/ome/bio-formats-examples/blob/master/src/main/java/ReadPhysicalSize.java>`_.
Missing calibration remains unspecified; incomplete/invalid calibration fails at
the original adapter boundary. Anisotropic XY and optional Z spacing remain typed.
The numeric metadata view1.0 cannot establish an isotropic physical scalar.

NRA ownership review follows the original declaration and consumers, not a new
hierarchy. Shared projection, geometry validation, persistence and ROI binding
stay on their existing owners. The original ``SourcePlaneStoreAdapter`` registry
and ``BioFormatsHandler`` cooperative inheritance are unchanged and exercised
through ordinary preparation. No independent new production capability requires
an extra mixin; ornamental inheritance would not repair this lost boundary fact.

New-case evidence: ``_NanometerHeader`` only declares a physical-X hook; its
inherited Y hook invokes it polymorphically. ``_VolumeHeader`` only declares Z.
Both pass through unchanged generic discovery, binding, persistence, runtime
image metadata and the registered ROI writer/reader, retaining physical units.
No generic consumer is edited for either declaration. Synthetic8x8 fixture
arrays are used only to exercise native source-bearing ROI file serialisation.

Qualification and preserved failures
-----------------------------------

* Original source:2RED/1PASS,5.16s,276072KiB, retained ``original.log``.
* First repair controls:2FAIL/26PASS,5.38s,284736KiB. The source calibration
  assertions passed; the receiving fixture ignored the writer's returned path.
* Extended controls:4FAIL/37PASS,5.92s,280960KiB. The30 unchanged Java/store/ROI
  controls passed; the four receiving cases passed calibration but supplied a
  string to the ROI reader's Path contract. Both failed logs remain byte-exact.
* Corrected receiving journey:11PASS,4.59s,283452KiB. Covers two non-unit scales,
  nanometres, Z spacing, anisotropy, unspecified/partial/invalid calibration and
  real native ROI archives. This corrected only fixture path handling.
* Last manifest-boundary change:1PASS/11 explicitly deselected,2.55s,179520KiB.
  The existing manifest fixture now persists0.5 through the same typed owner.
  Already-qualified Java/ROI cases were not rerun for ceremony.

Every source shard uses one CPU, kernel combined512MiB/no-swap cap and60s external
deadline. The existing Python environment, read-only ABI extensions, pyqt source
``ad4948775`` and PolyStore source ``242e302225`` are reused without installation.
The runner's two known pytest async-config warnings are retained; no plugins run.
No optional storage-registry bootstrap, JVM or provider is used.

Original R0 tool: ``/home/ts/wt/openhcs-s1-original-ratchet-20261001`` at
``3b03785f45df2ef5dc62ba6aed99294192ecbb01``. Its first measurement of actual
production ``9b118a943`` found StringSubscript+1: the manifest spacing was read
twice. The decode boundary now reads it once. Final original R0 compares full
``openhcs`` at base8551a48644b5a9cd054ca1c738ffef2295c5266f with actual
``bde6f5760`` and reports the complete changed file, all deltas0, exit0,
15.22s/87540KiB. Both original logs are archived, without copying the detector,
excluding changed paths, weakening bounds or waiving the initial regression.
This is a scoped ownership review and original R0, not a complete NRA global scan.

All raw logs, including original failures and R0, are archived byte-exact in the
source tarball (SHA256
``944296e6c2ebce08cda8734da534cc6bcecd5e7abd01e3aa2e9190ac1c986477``).
The original log has SHA256
``dea55341a8c4d80f64a30d78eedeba007cec372fcd8cbd78fd411b4db2a6e56f``;
reading that member back from the archive matched the retained loose bytes.
Their loose versions and small engineering fixtures remain in
owned ``.qa440-calibration-20261002``; old404 evidence remains untouched. No scratch,
worktree, environment, branch, package or acquisition artifact was deleted.

Remaining installed receiving acceptance
---------------------------------------

Source qualification is complete for this producer seam. Parent owns a fresh
ordinary saved-source/raw/result journey after Planck's live freeze ends: compare
source-derived spacing and units before preparation, in persisted input/result
metadata, and in read-only reopened raw/result native transforms. Original broken
metadata/archive evidence must remain intact; do not invent a source receipt or
silently backfill the saved scientific candidate.404's graph ROI installed reopen
remains a separate receiving obligation after Root394 integration. No installed,
live or scientific correctness is claimed by these source checks.

Publishing boundary
-------------------

Draft442 is the sole440 implementation checkpoint. The exact shared-owner
diagnosis and disjoint producer scope were published on394 in comment5949403614;
no shared hunk dependency was identified. Issue440 comment5949537473 links the
working source checkpoint and preserves the installed acceptance obligation.
The receipt is a Diataxis reference for integration evidence, not an operational
scientific guide. It does not replace the canonical source/runtime contracts.
