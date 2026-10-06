BBBC007 fresh19: qualified sixteen-field completion
==================================================

The independent author BBBC007_FRESH19_95 completed sixteen paired DNA/actin
fields through its original MCP client, without reference masks, previous
scientific outputs or reference-score feedback. Twelve fields supplied
development evidence; A01_9, A03_11, A03_14 and A04_11 were reviewed after
the scientific freeze at2026-10-05T23:27:23.197280+00:00.

The final source SHA256 is
5a97d3d7cf0c6c1b6e2b4fbf477aac11ec96d2b35a7cc26a7ecf1d93b044c275.
The handoff-manifest SHA256 is
7eff8a34fff5a434ec20b2ef8511da53a184e4f2664f01a7a4568e3423e699f5.
Controls are retained under
/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc007-fresh19-95-after-h00418-20261005/BBBC007_FRESH19_95/author-workspace/output.
Scientific payloads and native PNGs remain under
/run/media/ts/hdd/openhcs-science/next-bbbc007-fresh19-95-after-h00418-20261005/BBBC007_FRESH19_95.

Independent parent verification matched the manifest hash, thirteen selected
artifact sizes/hashes, three complete closed inner MCP journals and two outer
journal byte-prefix hashes. This verification did not hash every one of the
3367 manifest entries or assert a complete outer-journal seal. Independent
summing of the sixteen integrity rows reproduced1413 nuclear IDs and1413
seeded regions, with identical positive ID sets and zero seed mismatch pixels
in every row. These are persisted computational checks, not independent
pixel-level remeasurement or biological count accuracy.

The author repaired its opposing faint-pair and textured-single-body controls.
The parent personally opened the final A04_11 nuclear and actin detail
raw/result/combined sets and the A03_14 nuclear whole-field set. Ordinary
nuclear localization and growth beyond seeds are useful. The A04_11 cyan
nuclear region covers two apparent raw bodies, while some actin partitions
cut shared diffuse support. Neither these sampled views nor conserved seed
IDs establishes complete recovery or anatomical cell boundaries. Capture-time
presentation was not independently reconciled for every PNG. No manual
reference scoring was performed during that visual review and no findings were
returned to blind authors. Subsequent postfreeze scoring is recorded below.

The frozen outcome retains exploratory geometry and original-channel
photometry, with dim misses, possible merges and crowded-boundary uncertainty.
Lengths and areas use pixels and square pixels; physical calibration is
unverified. Original failed attempts, incorrect/corrected QA and adverse
reserve findings remain preserved. Positive exact-owned viewer/runtime exits
are separate from the original recorded client exit code2.

Independent postfreeze outline comparison
----------------------------------------

After the author exited, the parent used unchanged score_007 and
summarize_cell_partition from
/home/ts/code/projects/openhcs/benchmark/annotated_validation.py,
SHA2561db72c805e35c6a1328cf1b890bc2af55cc39c159524961187b7f8d81d6820cc.
Original execution handle26165 completed exit0. No pipeline was rerun and no
metric or parameter was selected from these reference results.

The original prepared_20260917_0355/BBBC007_cell_boundaries source manifest
SHA256052dae09880c67d30a869fbb155b882b3612db1b86908e09e02fa8b4b1d3b905
and trusted reference manifest
SHA25623d15c73878745a7d96ee738431f2e6fc3c318cb40b32b2bc897442a375f64fb
bind source_set_id/channel, not the older pilot's differently numbered fields.
All32 prediction planes matched the frozen manifest sizes/hashes; all32
staged raw hashes matched original archive members; all32 reference files
matched their exact recorded outline archive members. Original raw/archive
pair names also matched after removing only their images/outlines prefixes.
Archive hashes are b7009e2fce0a3152a5c9adda916eaa699d09696f4bd02a7d05d12d041e30c6d1
and6a5246f9a9d743d22eafdb409fae638a8461af97e9ff9c4a92f25eba236224d3.

The existing directed boundary metric counts internal four-neighbour label
transitions, excluding boundaries adjacent to background or the frame, and
asks whether they lie within two pixels of the union of manual cell outlines.
Of85093 eligible boundary pixels,63223 qualify: pooled fraction0.742987084719072;
mean field fraction0.741057444046598. It measures precision of scored internal
boundaries, not boundary recall, instance F1 or anatomical cell identity.
Incomplete foreground can receive a favourable directed score.

.. list-table:: Frozen field-level outline comparison
   :header-rows: 1

   * - Source
     - Predicted nuclei
     - Closed manual interiors
     - Eligible boundary pixels
     - Within2pixels
   * - A01_10
     - 101
     - 87
     - 5301
     - 3948
   * - A01_5
     - 107
     - 90
     - 5671
     - 4219
   * - A01_7
     - 152
     - 126
     - 8727
     - 6240
   * - A01_9
     - 148
     - 146
     - 7140
     - 5590
   * - A02_1
     - 73
     - 81
     - 4866
     - 3252
   * - A03_11
     - 115
     - 108
     - 8179
     - 6351
   * - A03_13
     - 55
     - 49
     - 3841
     - 2924
   * - A03_14
     - 82
     - 77
     - 6042
     - 4595
   * - A03_6
     - 32
     - 31
     - 1640
     - 1272
   * - A03_7
     - 90
     - 79
     - 6469
     - 4925
   * - A04_10
     - 70
     - 60
     - 2906
     - 2084
   * - A04_11
     - 78
     - 80
     - 5851
     - 4164
   * - A04_2
     - 103
     - 101
     - 7423
     - 5673
   * - A04_5
     - 54
     - 47
     - 3066
     - 2197
   * - A04_7
     - 83
     - 78
     - 4419
     - 3126
   * - A04_8
     - 70
     - 61
     - 3552
     - 2663

Closed manual interiors total1301, versus1413 predicted nuclei;16 open/frame
regions are excluded by the unchanged decoder. The112 count difference is not
a false-positive estimate. Predicted seed/cell overlap failures are zero, an
internal consistency result. The four author-reserved fields have423 predicted
nuclei versus411 closed manual interiors;20700/27212 scored boundary pixels
qualify (0.7606938115537263). That four-field subset follows the author's
pre-existing split, not a new selection chosen by reference score. No results
were returned to live blind authors; these references remain evaluator-only.

Paired first-completed and final development comparison
-----------------------------------------------------

Original evaluator execution20528 completed exit0 on the same twelve
development fields, excluding the four predeclared reserve fields. The earlier
lookup attempt28091 stopped before scoring because FIRST_TECH02 uses
NucleusLabelsUInt16/CellLabelsUInt16 names rather than FINAL's label filenames.
The corrected lookup accepts these two recorded naming forms, requires one
checkpoint per source/channel and verifies every size/hash against the frozen
manifest. The scorer and annotation bindings above are unchanged.

FIRST_TECH02 is the first completed scientific candidate, after technical
measurement/streaming repairs. It is not a successful first dispatch. Its source
SHA256 is1d5cd2819772c78205bca1091de633ca6318346e372e51b7d9229cd344deef71.
Independent AST comparison found identical Nuclei and SeededCells callable
settings and processing configuration between FIRST.py and FIRST_TECH02.py;
measurement declarations differ and an integrity step was added. Earlier
technical failures remain in the original record.

.. csv-table:: Same-field comparison, before reference feedback
   :header: "Source", "First nuclei", "Final nuclei", "Closed manual interiors", "First eligible boundaries", "First within2px", "Final eligible boundaries", "Final within2px"

   A01_10,107,101,87,5506,4056,5301,3948
   A01_5,98,107,90,5067,3868,5671,4219
   A01_7,146,152,126,8323,5961,8727,6240
   A02_1,16,73,81,167,113,4866,3252
   A03_13,54,55,49,3833,2848,3841,2924
   A03_6,35,32,31,1761,1324,1640,1272
   A03_7,87,90,79,6223,4809,6469,4925
   A04_10,69,70,60,2775,2004,2906,2084
   A04_2,100,103,101,7267,5463,7423,5673
   A04_5,53,54,47,2991,2069,3066,2197
   A04_7,84,83,78,4460,3127,4419,3126
   A04_8,69,70,61,3535,2646,3552,2663

On these fields FIRST has918 predicted nuclei versus890 closed manual
interiors; FINAL has990. Net count agreement therefore worsens, but excess
and missed counts can cancel and the closed-interior denominator excludes12
open/frame regions. No instance precision/recall is inferred. A02 recovery
from16 to73 against81 closed interiors supports the original visual diagnosis
of a severe coverage failure; it does not establish a matched-object recall.

Directed boundary agreement is38288/51908 (0.7376126993912306) first and
42523/57881 (0.7346624971925156) final. Mean field fractions are0.7313180106610657
and0.7354435134607923. Final admits5973 additional scored boundary pixels,
4235 of them within2pixels, while pooled agreement remains approximately flat.
This comparison supports a substantial local coverage repair, not a general
boundary-accuracy gain or a causal estimate of the skill's effect. All twelve
paired fields remain visible, including regressions; no outcome or parameter
was chosen from the evaluator results and no live author received feedback.
