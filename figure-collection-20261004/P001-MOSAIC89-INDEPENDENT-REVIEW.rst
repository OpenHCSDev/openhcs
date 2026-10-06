Personal neurite mosaic: independent development review
======================================================

This review covers a retained-context development continuation, not a fresh
autonomous evaluation. The selected checkpoint is mosaic02; mosaic03 is the
final attempted document and is rejected for unsupported near-track branches.
The original attempts and author report remain separate.

Evidence inspected
------------------

Control root:
``/home/ts/wt/openhcs-issue-batch-20260929/next-p001-mosaic-analysis89-development-20261005/P001_MOSAIC_DEV89/author-workspace/output``.
Payload root:
``/run/media/ts/hdd/openhcs-science/next-p001-mosaic-analysis89-development-20261005/P001_MOSAIC_DEV89``.

The reviewer read the original FINAL_MOSAIC_DEV89.rst, both recorded live
analysis/review contexts, candidate summaries and decisions, and independently
opened twelve original MCP PNGs: mosaic02 full-field, interior1 and faint-gap
source/result/combined sets, and mosaic03 faint-low source/combined and
faint-gap result. The faint-gap source is the corrected capture; the earlier
black capture is excluded. Mosaic source captures show pooled-normalized
analytical FITC, not untreated acquisition pixels. These twelve views are a
subset of the author's distributed review and do not independently establish
all-channel or all-join acceptance.

The full canvas shows broad spatial result coverage. Interior1 supports much
of the bright soma and process geometry, with a discontinuity in a descending
path and thin source-supported paths near a neighbouring pair left unassigned.
The faint-gap comparison confirms incomplete continuity in mosaic02. The
stronger-window mosaic03 comparison shows a lateral labelled extension where
the source shows background texture without a coherent filament. This supports
the author's local rejection, not a rejection of every recovered path.

Independent table reconciliation
-------------------------------

Python standard-library CSV reading and math.fsum were used on the original
three per-cell tables, without modifying scientific inputs or outputs. Each
contains 1,567 unique cell keys, exactly 1..1567, physical channel 2, well A01
and declared micrometre units. Summed lengths, body areas, processes and
branches match the corresponding native summary (length/area tolerance
1e-12 relative; integer sums exact).

========== ================== ========= ========
Attempt    Assigned length um Processes Branches
========== ================== ========= ========
mosaic01   138035.68444095762  7919      3578
mosaic02   161589.91388494096  9457      4548
mosaic03   190454.45427874118  9645      4810
========== ================== ========= ========

All three summed body areas are 824576.2170483199 um2. These are algorithm
measurements on one assembled canvas, not nine independent replicates or
sums of overlapping field counts. Declared spacing is 1.3556 um/pixel; this
review does not independently recalibrate it. Length differences describe
parameter sensitivity, not biological confidence intervals or accuracy.

Native cell-table / summary SHA256 identities:

* mosaic01: 801caefce4eb239ea19acdec4623428cd449e9a54065ce3b6bab5230843e41dc /
  8b13887da77ff93919f7ad44fdf1fd7c7f07e41f1a7ac095e06d21f49d1666dc
* mosaic02: 63cf36b773219fe68de34fd23920796949f52014ebfc6768210faaf7225d5228 /
  4c076198d229219c9a0e772b255e947839a3d0824a07c8c2c3c71fdbbc82ee20
* mosaic03: c92dfe6f1df0ec956024f0dab0a8540b038e2d96f0d3c3b70652d6ee57440c1b /
  6859e91795c88be3051457456309d5920c734ed8d4859b6f70a201120a2480ce

Useful scope and remaining work
-------------------------------

The selected result supports a reviewable stitched development checkpoint,
with many bright bodies and assigned process segments and reproducible native
measurements. Faint continuity, crowded body partitions and crossing ownership
remain qualified. Complete arborisation, verified biological neuron count and
fresh autonomous success are not established. No reference answers were opened.

The selected complete PipelineDocument was read: DAPI selects physical w1 and
FITC w2, with source channel order preserved. Its SHA256 is
01f9f417e9f650bb518139786c89c82b110c0af590591e5d388aeecc87678939;
the rejected final document is
49df417f043c7fb7a12e47547462f126dd5b74f9f0f03a4fcec81b93824e8223.
Streaming SHA256 verification independently establishes byte-identical nuclear
and body-label TIFFs across the three trials:
83836b942a76e0773c2780fb0fec181cb47d9c4e8876f4c25442b36f50aca36e
and 33878551fb313936a0a5ea7fda953df2ca3ca5cb2ea8785640bc989abdce59ea.

The original closure receipt confirms viewer/native exit, and independent
process checks find neither original PID 1601805 nor 1590675 present. The
author preserves client exit status 1; that status is distinct from the three
completed scientific executions and terminal outer-author exit 0.

Subsequent completed custody check: FROZEN_MOSAIC_DEV89.json is present.
All 348 complete-file control seals and three exact-byte-prefix journal seals
match their original size/hash declarations. Every one of the 77 scientific
artifacts (1,152,433,485 bytes) in artifacts-verified-MOSAIC_DEV89.json matches
its declared size and SHA256. The separate terminal outer-journal receipt
OWNER-TERMINAL-CLOSED-JOURNALS.sha256 verifies all six closed author/history
files. Prefix and complete-file seals remain distinct; no original freeze
was rewritten. Existing evidence is not replaced and the run is not restarted.

Publication qualification
-------------------------

The existing shared papers interpreter built both PDFs successfully:
``paper/build/run-20261005T215730-0e490d51`` (59 MiB).
``paper/build_paper.py status`` reports current with no changed inputs.
The reviewer opened rendered manuscript page 25 and supplement page 47;
the new paragraphs are readable and unclipped. The two disposable PNG
previews were removed after inspection; the PDFs remain. No new environment,
package installation, figure regeneration or scientific execution was used.
Invoking the builder with system Python initially failed because paper_build
was absent; the existing shared papers environment was used instead.
