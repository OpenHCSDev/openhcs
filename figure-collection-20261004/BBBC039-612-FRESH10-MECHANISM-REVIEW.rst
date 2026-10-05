BBBC039 frozen paired quality mechanism review
=============================================

Singer owns this coordinator-only source and saved-presentation audit following
merged796. Parent owns797's manuscript/scatter. Planck owns748 integration and
the next522 receiving candidate. No scorer, pipeline, viewer, native process or
author interaction is started here. The original frozen files and failed/UNKNOWN
attempts are preserved; no settings, scores or reference answers go to authors.

Completed determining review
---------------------------

Both final pipelines use Minimum Cross-Entropy and SHAPE markers/watershed.
The old explicit INTENSITY smoothing option does not smooth SHAPE's distance
landscape. Actual changed stage contracts are minimum size/suppression10 to12,
threshold smoothing1 to1.3488, and hole filling AFTER_BOTH to AFTER_DECLUMP.
Their individual contribution is not established by the paired score delta.

The visible failure is not absent raw signal: in the saved unequal-neighbour
diagnostic, both lobes enter foreground support, but the weaker lobe has no
obvious separate displayed seed and the final ROI remains joined. A suppression
change did not repair it. This is an application/diagnostic-closure limitation,
not a demonstrated missing generic guide. No skill or processing change is
proposed. Attribution of the pooled regression to a particular setting remains
unproved; the strongest score-selected case lacks saved native matched captures.

Source and original evidence identities
---------------------------------------

All paths below are retained originals, not new inputs or reconstructed views.
Define OLD as::

  /home/ts/wt/openhcs-issue-batch-20260929/next-bbbc01395-after612-20261004/BBBC039_FRESH612_96/author-workspace/output

Define NEW as::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96/author-workspace/output

NEW's image captures are on its original HDD science root, not directly in
NEW/qa. Define NEW_IMAGES as::

  /run/media/ts/hdd/openhcs-science/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96

SHA256 pins::

  OLD/final_full200/pipeline.py eb3a043f81c7e1508f036bbeb5c6f74aaf586f2fef8622c519eb5ad5072105e9
  OLD/REPORT.md 4600f82d902be420406137764cc6da53b672e63fb071024dfb7f0f8155f38ea7
  NEW/pipeline.py 0824f47839bfe4a5ac05592d8e57f4c548c68517ea46f7ea7765d0921b9f6b1a
  NEW/report.md 50928e9d1ac905f477047605bcbcc573a135eddd3b76c134c9befa2edeaf9a59
  NEW/qa/FULL200-final-triplets.json cb23d9588d5565852870ddb8d4a012f20aec43ec26b533db84ab621a185dfac9
  NEW/qa/FULL200-final-mounted-state.json 3f6d35ddfef4f96f145324859306f4ef9ce30167d80e23c41085b9ebfca6ca1f

Original installed source roots, identified from retained MCP receipts, are
issue-batch/engineering-mcp-queued-cancellation-20261004/receiving03/target
(OLD) and engineering-pre-first-routing-20261004/receiving10/target (NEW).
No import or backend execution was needed to read these declarations.
Relative to their openhcs/processing/backends/cellprofiler directories::

  primary_objects.py OLD 12b3c8a3829a8b19697029467ccb3bc5f8c897ab0ebbc9f5f0b7d35f49619f5f
  primary_objects.py NEW 62c3fe6e04841d69e2858f3b6492dfc86188998ea945ad769a96899fbcd8577b
  thresholding.py BOTH 4ed28e53ec30580fb9558b94ad4c50eb17a59b61a4a516cf992b388fadf887d0
  morphology.py OLD bf52da0b5e8db68f613deb0bd5c61f76e1c49d6e6b8a8b1117c9dc6e4b0ea647
  morphology.py NEW 52c8b7ef7493abd1a202e0f2df812cacfb8ea515759b23dc9a9f6055d6fe52dd

The primary_objects diff is documentation-only, including the explicit warning
that intensity smoothing is ignored for SHAPE. The morphology diff is NOT
documentation-only: it includes labeled-hole filling/kernel changes. Therefore
this review does not claim an identical complete numerical backend or an
isolated parameter experiment. Both installed interop/cellprofiler/
image_normalization.py files have SHA256
a840f237daecc63d9e45e65166fd5d0a91117a4e417134e5b1fd6971026a0e6e;
that shared delegating normalization source is not proof of every dependency's
equivalence. The original same-source-key/hash checks remain those of #796.

Effective stage contracts, not argument-name correlation
-------------------------------------------------------

Read identify_primary_objects, FillHolesOption, DeclumpingMaximaGeometry,
filter_labels_by_diameter_range and PrimaryObjectDiagnosticPlanes in the
actual installed source. Their determining relationships are:

* Threshold smoothing changes applied foreground support even for SHAPE.
  Both pipelines use global Minimum Cross-Entropy, not a MCE/Otsu comparison.
* SHAPE uses distance to the admitted labeled boundary plus deterministic tiny
  tie-breaking noise. INTENSITY's automatic_smoothing/smoothing_filter_size
  do not alter this landscape. The old explicit3/new automatic option is not
  a SHAPE mechanism explanation.
* With advanced settings enabled, AFTER_BOTH fills before markers and after
  declumping; AFTER_DECLUMP does not pre-fill. Threshold-support diagnostics
  are captured before pre-fill, initial components after it. Changing this
  option can change the distance landscape before suppression/partition.
* Manual suppression is governed by the existing footprint/seed owner; both
  runs disable automatic suppression and low-resolution maxima.
* Minimum diameter is an equivalent-area cutoff, pi*d*d/4, not a measured
  bounding span. The changed lower cutoff is about78.54 to113.10 pixels.
  Size filtering occurs before final hole filling. Final fill cannot recover
  a basin already removed by size admission.

Consequently support, pre-fill geometry, emitted markers, unfiltered basins
and accepted labels must be distinguished. Their interaction is a plausible
mechanism family, not a demonstrated assignment of the314 extra false negatives.
No alternative codec, semantic owner, production scanner or consumer is added.

Strongest regression and available paired native evidence
--------------------------------------------------------

The already published #796 JSON is the ONLY scoring source used here:
figure-collection-20261004/bbbc039-fresh10coverage-postfreeze-evaluation.json,
SHA256 e257a17d67662967ba9af16a9a94aa78756b47a889c3e093a0cf1abe640f828e.
Its same200 comparison reports314 extra FN,11 extra FP and303 fewer predictions;
pooled F1 is90.6224% to89.8368%. These are annotation-relative results, not a
perfect biological census or evidence of skill causality. No score was rerun.

The largest recorded per-field F1 decrease is20589_P23_7: TP12/FP0/FN0 becomes
TP8/FP2/FN4. Neither inspected native capture inventory supplies a matched
triple for this field. Dense20630_H06_6 also lacks the required captures; it
must not be substituted with the differently identified20639_H06_4. No
reference pixels were opened, and no synthetic overlay was generated to fill
these gaps. Thus the strongest score-selected mechanism is unresolved.

Available shared final field20630_A02_1 is a genuine, lesser paired regression:
TP101/FP5/FN9 becomes TP96/FP5/FN14; F1 .935185 to .909953. Its six original
raw/result/combined PNGs were personally opened. Upper-left crowded group
partitions differ, with a broader joined region in NEW, while many isolated
compact-body controls remain coherently outlined in both. This supports local
partition deterioration, not a claim that every additional FN is that merge.
Colour palettes are not cross-run object identities.

Both triples cover the same520x696 source at center(0,259.5,347.5), but OLD zoom
is.65 and NEW zoom.8. Within each triple isolation/camera controls match; the
cross-run screenshots are NOT pixelwise matched presentation. OLD uses a
recorded p0/p99 display request; NEW state gives raw window120..680/gamma1.
Their contrast is not asserted numerically equal. NEW saved state reports101
ROIs in the exact source domain, scale1/translation0, not proven physical
calibration. Original OLD/runtime/mcp.stdin and NEW/runtime/mcp.stdin preserve
the route isolation, axes and capture requests; NEW's mounted-state and triplet
index carry its source/result/camera receipts.

Failure-stage witness and positive controls
------------------------------------------

NEW's20592_A21_1 unequal-neighbour witness has a dim upper lobe touching a
brighter lower one around native y239..258/x116. Camera is center(0,250,180),
zoom2, z_index0/timepoint0. Personally opened raw/result/combined-corrected,
foreground, response and seeds show connected admitted support, a broad
lower-dominant distance response, no obvious separate seed in the weaker upper
lobe, and one accepted ROI. Nearby compact bodies retain individual seeds and
outlines: this is not a whole-frame failure. The earlier all-layer combined
capture after failed isolation is retained but excluded.

The original report and saved REPAIR01/REPAIR03 combined captures agree that
lower suppression and then intensity markers with lower suppression did not
separate this witness. REPAIR02's reported two peaks in a one-dimensional
smoothed profile do not prove two emitted two-dimensional markers or basins.
This audit does not infer unobserved IDs from the profile. This field's overall
annotation F1 actually IMPROVES (.902778 to .929577), so its local merge is a
failure-stage control, not proof of the pooled regression or old same-pair
success. No old matched capture of this particular pair was established.

As an independent OLD continuous-body control, candidate02_field0_native's
three PNGs were opened. The native legend identifies20585_F14_7, not the A06
true-pair repair. A ring-shaped body remains one filled outline and several
isolated ovals remain coherent; the continuous crescent still has multiple
partitions. OLD is therefore not presented as error-free or a universally
better declumping choice. The old report's A06 suppression repair is distinct
from this F14 control and cannot be transferred by filename alone.

Existing guidance versus actual applied reasoning
-------------------------------------------------

The full current analysis-learning, measurement-interpretation and
segmentation-diagnostics references were read at main154566ed. Relevant source
SHA256, under packaging/codex/openhcs/skills/use-openhcs/references/::

  analysis-learning.md 78a5179e6e5d5e12cfc281ef17ae359bcb3496508609c4db3357e3dfe0e6b7fa
  measurement-interpretation.md 5f8b4784f4cfe1f008b593fafce99ba08065b122daa0dad58fba3546b2ad4fd1
  segmentation-diagnostics.md 3173aebf8412d878148efa7dee5e8ccb011e08e51377ac5c707042d6f2df6938

Measurement already distinguishes equivalent area from span, threshold from
marker smoothing, within-body texture from real pairs, and footprint competition
with a stronger neighbour's shoulder. Its stage-linked worked contrast states
that profile peaks are not proof of two-dimensional maxima or dividing lines.
Segmentation already requires the earliest-loss distinction across support,
seeds, unfiltered basins and size admission, without a zero-error acceptance
rule. Analysis learning already requires tested, scoped repair evidence.

NEW's original stdin94..97 and report record relevant guide retrieval BEFORE
FIRST, followed by measured raw profiles and a reasoned SHAPE hypothesis. This
is not a demonstrated failure to retrieve the marker/body guides. It also is
not proof that every later passage of today's guide existed in that bundle.
The incomplete applied link is from the chosen empirical envelope to actual
weaker-neighbour seed/partition survival and pre-filter geometry after changed
support/fill/suppression/area choices. Failed local repairs preserve that limit;
choosing the original useful method after them is not itself misconduct or a
reason to reject every measurement. No known older settings are fed forward
to authors as an answer, and no duplicate generic skill paragraph is warranted.

Capture byte pins
-----------------

All entries below were personally opened unchanged. Every basename is the
listed timestamp followed by _napari_6017_OpenHCS_Napari_Visualization.png.
Prefixes are OLD/qa or NEW_IMAGES/qa, respectively::

  OLD final_field2_full_raw/20261004T130942480136Z 86c07ba9c159a38caa27e59a0b51687af58881918893f0853a1ff9fdc131358c
  OLD final_field2_full_result/20261004T130947639815Z 1278b7885e81835205491797c6ca9d6fe551162dace90f17756b0c5614d7bc92
  OLD final_field2_full_combined/20261004T130952836362Z 9966a862657b5c2000df0576a80efc6ca9d73cd92201291fb4195fd88c40bfa0
  OLD candidate02_field0_native_raw/20261004T125348507707Z a01b77cae1a756f26727feeb5c6af6c92e7057ca803dbc86969f0f38aa917daf
  OLD candidate02_field0_native_result/20261004T125352981245Z a6de6d3983390624d7f6efc72fd6d4f14c6e8ba8be358aca24e754f82753a491
  OLD candidate02_field0_native_combined/20261004T125357377402Z fcb6edf160abb16608f3bd8924c196155ecedf675ceae83c17dad50609982273
  NEW FULL200/A02-raw/20261005T130255533882Z d4bdb0815564bf1b7a8c75e58dfc3df259677bb3638ce6b289ed52d918831617
  NEW FULL200/A02-result/20261005T130303594735Z 1ba7d08069454f01d6ce9f2172c2c90cda22fd66cee723fad84e36ca4ca4f116
  NEW FULL200/A02-combined/20261005T130311190833Z 4320ab0e41b53dd2f4fa4b875684be85d1f4b716311aa2884870b36563d6e4b4
  NEW DEV06/A21-pair/raw/20261005T123059076340Z bc7817b9a4c6e32b39696c71743483826d560ae96bcf21fe78f169e36981f459
  NEW DEV06/A21-pair/result/20261005T123105270611Z 239f96affda0e6dd33b275d77056bfd46e09090d9e88fe91a143bf33bcc7ec7b
  NEW DEV06/A21-pair/combined-corrected/20261005T122920525074Z fd25a92a6c540da93d415449b39c2007af7afda67b99cdbb8e91335eff72fb8e
  NEW DEV06/A21-pair/foreground/20261005T123111933921Z 92767d1261ea3dff3600c9bbf0cab4594e048f2c69f40366f1f14ec1864ec5f0
  NEW DEV06/A21-pair/response/20261005T123123420522Z c3d7c2f45140b4d8642aed6441463787b609230fa408f6183a62ae2133ff88b5
  NEW DEV06/A21-pair/seeds/20261005T123129936476Z d17adf37948ed7e11d045255642227d68ef2fdcd26f3c667d1419371b9cb00e2
  NEW REPAIR01/A21-pair/combined/20261005T123631204684Z b46c226eb833749fe08d7ddc468acb443ff0cd889e829d57493386eef38b6a00
  NEW REPAIR03/A21-pair-combined/20261005T124804799692Z 2514fc480419782f47a9f96a82c84981752e2aec17688e081ed4ad518a1d3aad

Disposition and precise acceptance
----------------------------------

The original source, guide, frozen report and installed-declaration relationships
were read; the selected17 native PNGs were opened and byte-pinned. The current
NRA/refactor-audit instructions and applicable IDEN-6/BOUND-2 patterns informed
identity and effective-declaration checking; there is no structural refactor,
global AST/R0/R1 proof claim or new scanner. No tests, scorer, external data
decoder, scientific pipeline or renderer were run. Corrected read-only path/key
lookups do not represent scientific retries. No references were opened as
pixels, no live author contacted, no outputs or UNKNOWN dispositions changed.

The audit acceptance is met at its actual tier: a saved local partition
regression, a stage-specific unresolved pair, coherent positive controls, and
explicit missing cross-run/prefill/marker/basin controls. The pooled causal
allocation remains unresolved. #798 changes this receipt only; parent owns
#797 publication and Planck the #748/#522 native receiving integration.
