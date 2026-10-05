Personal neurite stitched dev13: shared fitting and local path support
===================================================================

This is retained-context development, not a fresh autonomous pass. The author
continued its own fieldwise phase after an objective clarification. All nine
overlapping fields were development sources; no held-out answer or expected
count was used. Earlier freezes remain intact.

Original owner root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-p001-stitched-dev13-94-after-bbbc007-20261005/P001_STITCH_DEV13_94/author-workspace

Canonical HDD root::

  /run/media/ts/hdd/openhcs-science/next-p001-stitched-dev13-94-after-bbbc007-20261005/P001_STITCH_DEV13_94

The coordinator read FINAL_REPORT.rst and FINAL_FREEZE.json, independently
checked all1275 artifact hashes and340 control hashes on2026-10-05, and
personally opened the six native seam/lower-right panels below. The manifest
declares1,854,703,964 artifact bytes and6,163,521 control bytes. Excluded outer
journals and their later harness seals are separate from these whole-file
checks. No new array processing, scientific execution or scoring was performed.

Source and analytical contract
------------------------------

The author reports eighteen physical TIFFs: nine1024x1024 fields with DAPIw1
and FITCw2. Acquisition headers supply3x3 positions, approximately921.6-pixel
stride and10% overlap, with declared spacing1.3556 micrometres. Positions are
acquisition-derived, not independently image-registered or calibrated.

The final pipeline independently reloads each complete nine-field channel
stack and applies one pooled0.1/99.9 percentile fit per channel before assembly.
Reported fitted limits are DAPI580..18305.81700000167 and FITC126..49305;
the same pair is repeated across every contributing site. This is not
per-field stretching. Normalised and raw QA mosaics use the same positions
and dynamic blending; endpoint clipping and blending change pixel values.
The final two-channel analytical mosaic is2868x2868.

Final submitted pipeline SHA256:
16a6c6295aef087d8c9ca5a817a9adc0699a633bf5f0e29030c4518d98eb0351.
Registered dependency p001_shared_fit_positions_v2.py SHA256:
bd9da18e45396df2bbcafcd914c5cee9d9c1bb8d5116edabf609cb4987486b7c.
FITC supplies body/process signal and DAPI supplies nuclear anchors. These
are declared source bindings, not identities inferred from a selected row.

Independent native visual review
--------------------------------

The following original PNGs are under qa in the HDD root; timestamps have
prefix20261005T and suffixZ_napari_6013_OpenHCS_Napari_Visualization.png:

* seam-raw96/160718171370, seam-result96/160715033730,
  seam-combined96/160721683637;
* bottom-raw97/160820208881, bottom-result97/160816945967,
  bottom-combined97/160823711064.

The recorded canvases are953x464, native displayed axesY/X. Capture receipts
declare immediate frames, not render-complete certification. All six opened
images are populated and each triplet visually retains its field position.
The author records raw FITC limits126..3500 and sampled centres(x970,y500)
and(x2355,y2355); these settings are reported provenance, not new measurements.

At the seam witness, several long raw-supported processes are followed by
coloured paths and their attached body envelopes. There is no obvious doubled
body in this bounded view. Some visible faint extensions remain unlabelled;
crowded signal at the lower-right of the seam crop has several adjacent
coloured envelopes whose ownership cannot be settled from FITC alone.
The lower-right field-core triplet also shows broad body localisation and
many supported paths, alongside incomplete faint segments and ambiguous
connections in crowded regions. This is useful local recovery, not proof
that every crossing or soma division is correct.

These triplets precede final attempt09: attempt08 saved the scientific outputs
but failed terminal viewer settlement. The author reports attempt09 changed
only analytical streaming and destination, then completed. The coordinator
does not claim independent bytewise08/09 result equivalence or final09 matched
triplet acceptance from these earlier captures. Both stages remain retained;
final09 raw/combined centre captures are separately inventoried in
output/stitched-native-qa-captures.json and were not opened in this review.

Measurement and autonomy scope
------------------------------

The author reports1654 modelled somas,1988 nuclear labels and1165
outgrowth-owning parent labels in the final mosaic. Modelled total outgrowth
126046.6836 micrometres and the rooted fraction69449/73009=0.9512389 are
algorithm outputs, not validated cell counts, biological length or95.1%
accuracy. The fraction's denominator is candidate trace pixels, not truth.
Unrooted residuals, topology-dropped paths, acquisition-edge truncation and
crossing identity remain distinct limitations.

Retain acquisition-wide assembly, shared stack fitting and local body/path
recovery as development progress. Complete well counts, complete outgrowth
and validated ownership remain unsupported. The final client exited2 despite
the reported completed execution and exact owned-child closure; that runtime
outcome is retained rather than recast as a clean client exit. A future fresh
author must rediscover the multisite task using only its brief, MCP and the
packaged skill; these field-specific answers are not agent-facing guidance.
