Fresh H003 paired-channel repeat: rejected repair and postfreeze comparison
=========================================================================

Scope and selection
-------------------

H003_FRESH25_89 independently analysed the released A02 DNA/actin pair through
the packaged receiving25 skill and recorded MCP client. FIRST produced 55
nuclear and cell instances. The author tried three marker-stage repairs and
selected REPAIR3 as its final attempted pipeline, with 51 instances in each
label image. It rejected an accurate whole-cell census because merges,
omissions and unsupported body envelopes remained. No reference score or
parent biological correction was supplied during authoring. This is not an
autonomous biological pass or evidence that all possible methods were exhausted.

The author froze the scientific outputs at 2026-10-06T04:10:43.719084+00:00.
Its original outer recording ends with turn.completed and COMMAND_EXIT_CODE=0
at 00:13:42-04:00. The separate recorded MCP client exited 2; that retained
client status does not erase completed scientific executions or positive owned
runtime shutdown. Exact author, native and viewer processes were independently
absent before parent scoring. Original failures, timeouts and scientific files
were not replayed or modified.

Parent verification
-------------------

The parent independently verified all 493 manifest artifact SHA256 values
(77,079,686 bytes), eight final-handoff file hashes and three post-writer journal
hashes. The author claims a broader distributed review; the parent separately
opened six REPAIR3 PNGs: raw-only, result-only and combined DNA captures at
the border and central-pair positions, at the recorded full-range window.
These matched captures retain ordinary aligned nuclei and a merged central
pair, alongside an ambiguous clipped border pair. This six-capture check is
not a complete biological review or independent confirmation of every author
capture. All other candidate files and captures remain in the original freeze.

Scoring contract
----------------

The existing Bbbc007ManualOutlineReference.load/load_boundary and
instance_segmentation_metrics/boundary_segmentation_metrics were called
unchanged after author completion. Source hashes are:

* benchmark/validation/references.py:
  099d1ad37058bb41a3cad9456d74fa08d32cfb4549a155e7efb124149a7f92c8
* benchmark/validation/scoring.py:
  57c23fe3efd4964d3ab353e5c156080d12e1289694952ce0a8ac4762251c4da1

The reference is BBBC007/f9620/POS0005, loaded from the retained trusted cache
at /run/media/ts/hdd/openhcs-science/trusted-reference-cache/BBBC007/selected-f9620-pos0005.
DNA outline 20P1_POS0005_D_1UL.tif has SHA256
a64948d4d3bac0c32a44a4c2f137ca4f9bf152f9dc4a8b2a6a4399588cc95103;
actin outline 20P1_POS0005_F_2UL.tif has SHA256
7832d385000b2aabe7c33cffdefa6313fba90cbd67ad9e2e9564742b30fd5b8f.
Both hashes were checked before loading. Matching uses one-to-one maximum-IoU
Hungarian assignment accepted at IoU >= 0.5. Predictions and references are
400 x 400; there is no resizing, registration or border-object filtering.
Closed reference interiors exclude open/frame-connected regions and retain
tiny annotations. They are not certified exhaustive biological ground truth.
Boundary diagnostics use original manual strokes and two-pixel tolerance;
nearest-union agreement does not establish object correspondence.

.. list-table:: FIRST and author-selected rejected FINAL
   :header-rows: 1

   * - Channel/stage
     - Reference/prediction
     - Matches/excess/missed
     - Object F1
     - Mean matched IoU
     - Boundary F1
   * - DNA FIRST
     - 47 / 55
     - 38 / 17 / 9
     - 0.7450980392
     - 0.6062980121
     - 0.8268923120
   * - DNA FINAL
     - 47 / 51
     - 36 / 15 / 11
     - 0.7346938776
     - 0.6046894258
     - 0.8047569217
   * - ACTIN FIRST
     - 54 / 55
     - 37 / 18 / 17
     - 0.6788990826
     - 0.6875436390
     - 0.6608390288
   * - ACTIN FINAL
     - 54 / 51
     - 33 / 18 / 21
     - 0.6285714286
     - 0.6891404804
     - 0.6548402814

DNA directed contact-boundary agreement falls from 0.7323943662 (142 relevant
pixels) to 0.3541666667 (48). ACTIN changes from 0.6947946977 (3,093) to
0.6985694823 (2,936). These are different subsets from the whole-boundary F1.
The reduced final count is not a better instance segmentation: reference
matches and recall decrease, despite a smaller nuclear count discrepancy.
Preserve the author's final choice; do not substitute FIRST based on scoring.

Reproducible custody
--------------------

Control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-h003-retina-fresh25-rotation-20261006/H003_FRESH25_89/author-workspace/output

Payload root:
/run/media/ts/hdd/openhcs-science/next-h003-retina-fresh25-rotation-20261006/H003_FRESH25_89

FINAL-MANIFEST.json SHA256:
089fd1709adff68f3b339039c76dc753935a8dcb92d90560b9fa463b721d3cd7

FINAL-PIPELINE.py SHA256:
548a5f912c48ec4e6bdd888c8e2ac97e1abacff14dc6d3790e6c1dacc131e9bd

Prediction paths are under attempts/FIRST or attempts/REPAIR3 in
staged-input_openhcs/results. Nuclear filename:
A02_site-1_channel-1_z_index-1_timepoint-1_Nuclei_step0.labels.tif;
cell filename: A02_site-1_channel-2_z_index-1_timepoint-1_Cells_step1.labels.tif.
Their independently scored SHA256 values are:

* FIRST DNA: d686f586e8f887a43d028771022a7e2f5b87b438726579a89d7ebf500b1f4e8d
* FINAL DNA: 0e298be2a7f5b5ea7ebc1cc39701e9e575acf3275496ddc9886d196663be28cd
* FIRST ACTIN: 1032f3d9632f0993590d74fb3d1c0a07a2765fa7bd7cf173f373d7504d7e3e9f
* FINAL ACTIN: b5b932829fe1c76faea7a720820c8a7447110fe85959e4ab5fa2d8d007fc2275

Original parent scorer session37958 exited 0. Scoring references and results
were not supplied to scientific authors or copied into the packaged skill.
This repeat is one development field, not unseen generalization. Supported
ordinary nuclei remain useful provisional outputs; complete body boundaries,
cell identities and an accurate biological total are not established.
