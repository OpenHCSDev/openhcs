Independent review of completed BBBC013 development
===================================================

Scope
-----
This is retained-context development, not a fresh autonomous pass. Scientific
settings froze before the five new pixel-review fields were opened. Earlier
whole-plate tables had already been seen; the pixel reserve is not an unseen
scientific benchmark. No candidate was rerun or changed during this review.

Original report and evidence live under
/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-self-development96-20261005/
BBBC013_SELF_DEV96/author-workspace/output. Canonical scientific outputs and
captures live under
/run/media/ts/hdd/openhcs-science/next-bbbc013-self-development96-20261005/
BBBC013_SELF_DEV96.

Independent table calculation
-----------------------------
Read all 96 original well tables and recomputed the 24 dose/control summaries:
equal well weighting, sample SD, SEM, total/valid cell rows. Maximum absolute
numeric difference was 4.440892098500626e-16. Recomputed control Z-prime and
V-factor from those summaries, excluding the labelled empty groups from V.

Wortmannin: negative/positive mean ratios 0.8635920413397533/2.902161728685869;
Z-prime 0.7001161940368548; V-factor 0.7101207012505257.
LY294002: negative/positive mean ratios 0.9942336690081017/2.9410132916533787;
Z-prime 0.512796186097677; V-factor 0.5965534979911493.
Four wells per condition; 48 wells per block. LY positive controls contain
Wortmannin, not LY294002. The labelled empty groups contain cells.

The 96 well tables total 18,073 nuclear-ID rows, 16,589 defined N/C ratios and
1,484 zero-cytoplasm rows. Undefined ratios stay NaN and are excluded from
well means. These are mask-derived quantities, not manual population truth.
Both observed dose series rise at lower doses, then level or decline. No
potency fit or causal toxicity conclusion follows from that pattern.

Visual review
-------------
Personally opened 15 original MCP PNGs: matched raw/combined/result triplets
for D01 DNA and GFP full field, F08 DNA and GFP object view, and H06 DNA object
view. All 72 reserved PNG hashes match qa-index-reserve.json. These 15 views
are the parent's own review, not a claim to have opened all 72.

Recorded display windows: D01 DNA 0..114 and GFP 0..139 (p99), F08 DNA 0..44
and GFP 0..69 (p95), H06 DNA 0..50 (p99). Matched sets retain camera framing;
physical channel labels and source/component receipts agree with their views.

D01 represents many bright nuclei and broad GFP-supported bodies. Crowded
interfaces and incomplete dim extents remain uncertain. F08's central two
DNA lobes share a single magenta mask; the matching GFP view shows little
growth beyond that seed, consistent with the recorded zero-cytoplasm row.
H06 contains visible faint nuclear support without a label. The author traced
that miss to primary foreground admission, not secondary association. These
are concrete coverage/separation limitations, not evidence that every mask
or the complete assay-response calculation is unusable.

Integrity and custody
---------------------
All 194 entries in OWNER-TERMINAL-TABLE-SNAPSHOT.sha256 pass when checked from
the canonical results directory: 96 cell tables, 96 well tables and the two
plate summaries. A first invocation from the wrong directory failed to find
relative paths; the corrected read-only check passed without modifying data.

Final pipeline SHA256:
fc1ebb98abb174b9555bd9b38af6a8df63f91fa947169b90d893c3c405bc2b7a
Native statistics CSV SHA256:
f7490e98bb2c0e34571ebd5924a17e965f790f45f3216a81c475271ae1bef0c9
Native dose CSV SHA256:
6b65ada60656c13ae1792c5d6bfbffb1f5a4226f2d93128a1cf2a502d402e078

Dewey independently checked the full handoff: 4,644 whole files and two
declared author-event prefixes pass. One append-only outer rollout was
incorrectly sealed as a whole file; its original byte prefix matches, and a
separate terminal seal qualifies it without rewriting the original manifest.
Exact native/viewer exits are positive; recorded client exit 2 remains distinct
from author exit 0. No replay or endpoint restart occurred for this review.

Conclusion
----------
Completed plate coverage, reproducible selected-mask assay summaries and useful
local repair are supported. Complete individual-cell boundaries and unbiased
population translocation are not established: GFP governs both mask admission
and response, and dim/merged objects remain. This development result must not
be counted as a fresh autonomous success or shown to current blind authors.
