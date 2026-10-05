Personal neurite development89: nine fields, scoped geometry
===========================================================

This is the same-author retained-context development phase P001_VIEWER_DEV89,
not a fresh autonomous pass. The parent independently opened thirteen original
MCP captures on 5 October 2026: matched faint FITC raw/result/combined triplets
at sites 1, 5 and 9, plus high-window raw FITC and separate DAPI at sites 1 and 9.
No new execution, viewer manipulation, reference annotation or feedback to the
analysis author was used in this review.

Observed support and limitations
--------------------------------

Site1 central and lower-right bright bodies have separate footprints. Several
process segments align with raw, but a diagonal faint connection remains
interrupted; colours changing at contacts do not resolve neuronal ownership.
At site5, the central vertical bright group has separate identities and nearby
process geometry, while contact and a lobed-body split remain uncertain.
At site9, numerous footprints follow bright body/process support, but a dense
cluster contains visibly uncovered bright support. The high-window FITC and
DAPI views establish that this is not simply a blank raw channel. The author's
bounded final-mask samples further identify incomplete body association; this
review does not manually assign extra cells or validate every cell boundary.

The author reports removal of one unsupported body assignment in a local
nuclear-admission repair. Only final captures were independently opened here,
so this is retained author evidence, not an independent before/after claim.
Many supported localisations and process segments are useful. Faint gaps,
body undercoverage and ambiguous contacts limit population counts, complete
per-cell lengths and anatomical branch ownership. These limitations do not
make all local geometry absent or invalid.

Coverage and identities
-----------------------

Execution cc548124-14a8-4bf4-8f2b-f2a87352713c completed all nine fields.
Independent row counts from the actual final per-cell CSVs are, for sites 1--9,
174, 216, 196, 160, 230, 245, 112, 223 and 311. These are algorithm rows,
not biological cell counts; overlapping fields are neither unique-cell totals
nor nine independent biological replicates. The final coverage record lists
four label TIFFs, five QA checkpoints, SWC and GraphROI artifacts per field;
that inventory is author-reported, not a fresh independent reopen of every file.

The parent checked the original frozen source and QA-decision hashes and all
45 final screenshot hashes against their native snapshot receipts: all passed.
Pipeline SHA256 is
72490b811f887a9d461a1d64c38939a7e29c345c4679e5e2d637560bef721683.
QA-decision SHA256 is
232a72cb379228a4d3a301d00e80925d10a62bc08daa672791b8ff40463bcf6d.
This pass does not claim an entire scientific-payload hash audit or runtime
closure. Original closure/client/outer-journal dispositions remain owner records.

Source records
--------------

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-p001-viewer-development89-20261005/P001_VIEWER_DEV89/author-workspace/output

Read sources: FINAL_SCIENCE_DISPOSITION.json, final-qa-decisions.rst,
final-artifact-coverage.json, final-field-records.json and
final-distributed-capture-receipts.json. Actual per-cell CSVs are under the
matching HDD programme root, attempts/analysis06/normalized-fields_openhcs/results.

Capture subdirectories are final-site{1,5,9}-native-{raw-faint,result,combined-faint},
with additional raw-high and dapi at sites1/9. Original filenames and SHA256
values are in final-distributed-capture-receipts.json. Native witness centres
are recorded as site1 y/x600/450, site5 490/500 and site9 700/500, zoom2;
declared XY scale is 1.3556 micrometres, not independently calibrated.
Faint FITC143--3500, high FITC143--20445 and DAPI616--3839, gamma1, use the
author's retained presentation readbacks; the parent did not re-read a live scene.
All nine fields are development data. This fieldwise checkpoint does not
establish completed analysis of the already assembled mosaic.
