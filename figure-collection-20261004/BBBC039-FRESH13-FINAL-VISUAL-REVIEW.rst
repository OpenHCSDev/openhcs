BBBC039 fresh13: independent final whole-field review
===================================================

Scope and decision
------------------

On 5 October 2026 the parent reviewer personally opened nine original native
PNG captures: raw-only, result-only and combined views of a dense reserve
field, a sparse reserve field and a zero-output control. This review uses
retained captures after method freeze; it neither changes the frozen pipeline
nor opens reference annotations. Planck owns independent postfreeze scoring.

The three triplets show useful ordinary DNA-body localisation across contrasting
densities and rejection of the reviewed noise-only field. This is positive
visual evidence, not an exhaustive count or a reference accuracy score.
Crowded-object separation remains a separate limitation already documented in
``BBBC039-FRESH13-DEVELOPMENT-WITNESS-REVIEW.rst``. That development review
found plausible residual merges; the final whole-field sample does not erase
those findings or establish improvement over the predecessor.

Observed quality
----------------

* Dense validation field ``20646_N12_7``: many isolated oval and elongated
  bodies have broadly supported footprints, and much of the crowded field is
  partitioned into distinct labels. Several irregular or lobed footprints in
  crowded regions remain ambiguous at whole-field scale; this sample cannot
  settle their multiplicity or exact dividing boundaries.
* Sparse test field ``20646_N21_1``: ordinary isolated bodies are covered and
  adjacent central bodies have separate labels. A bright lower-left bilobed
  structure is divided into two labels; the whole-field raw image alone does
  not establish whether this is a valid pair or an internal split. No blanket
  claim of perfect separation follows from the otherwise good coverage.
* Zero-output field ``20592_F13_7``: the strongly stretched raw view shows
  granular noise, uneven background and small bright specks, without obvious
  intact bodies at this scale. The result-only canvas is empty. Raw-only and
  combined PNG bytes are identical, consistent with no visible overlay.
  This supports this nuisance-control outcome, not all zero-output fields.

Presentation evidence
---------------------

Source labels and framing agree within each triplet. Recorded snapshot
dimensions agree within each set: canvas 953 by 398, displayed axes y/x,
camera angles 0/0/90, native centre y=259.5, x=347.5. All nine screenshots
show gamma 1. The saved window acknowledgements resolve the p0/p99 windows
to 119--790 for N12, 110--686 for N21 and 118--171 for F13. These are retained
author acknowledgements, not a fresh live state readback or an independently
reconstructed complete sequence of presentation changes.

Custody
-------

Original capture root::

  /run/media/ts/hdd/openhcs-science/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/qa/final/

Directories below contain the timestamp followed by
``_napari_6021_OpenHCS_Napari_Visualization.png``. SHA256 was recomputed from
all nine original files and agrees with ``provenance/native-QA-ledger.json``::

  20592_F13_7-whole-raw-p99       20261005T182007862295Z  11c0c77f9b6777313ab75544ccf3b7b4afe4331b728a9d0ba904a2a016cfaa08
  20592_F13_7-whole-result-p99    20261005T182008881388Z  4e9b19657e32bb915053634d3267f92765cf022686d356c4d60b1e61c14c5d66
  20592_F13_7-whole-combined-p99  20261005T182009389910Z  11c0c77f9b6777313ab75544ccf3b7b4afe4331b728a9d0ba904a2a016cfaa08
  20646_N12_7-whole-raw-p99       20261005T182036219296Z  d19042d75755e28a790a8a5d9a1396071f458f8d47943402f9f68ba5c23ec529
  20646_N12_7-whole-result-p99    20261005T182036726262Z  b7f8fa2ebcb4050ddb01c9a272fea6735b35bcc28b317bba2288abb0f6ec7c42
  20646_N12_7-whole-combined-p99  20261005T182037086344Z  21880f6a0cbfd05c621ee1a22af1b2565e7c4c38b26dc89bdaa488320d9dbf29
  20646_N21_1-whole-raw-p99       20261005T182040315680Z  2d493857f4e6d4ff51ec5df419c994db4f98ae659ed4de0e819a67e3a784cb2c
  20646_N21_1-whole-result-p99    20261005T182040715300Z  7c94c7c1706d499c7ecf7ebbe492fc520cc357c3df133889469e052159b82786
  20646_N21_1-whole-combined-p99  20261005T182041082839Z  0d768eb05600e2e31a71741a76935f5dbe0fefbd3b5cefced0dc9477d5be4d1a

The ledger and ``provenance/final-QA-review.json`` are under the original
``BBBC039_FRESH13_88/author-workspace/output`` directory in
``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-fresh13-88-after-bbbc013-20261005``.
This review changes no scientific source, labels, pipeline, reference boundary
or live viewer. It covers these nine whole-field captures, not the author's
entire 93-capture review or the complete 200-image corpus. The empty field was
selected after output materialisation and is not a random specificity sample.
