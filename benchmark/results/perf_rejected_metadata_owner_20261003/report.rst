Rejected flat metadata owner prototype
======================================

The prototype did not reduce representative 3D runtime enough to justify its
additional storage and dispatch machinery. It is reverted from the final source.
Rejected source 9eee98265c939859d49f0c60bd5b3a2168cb29fe remains in Git history;
baseline e8587bd7eb0c4aa283bc300c5eb9f2294f24890f and restored production/tests
are byte-identical. This is evidence for #384 / PR #394, not a completed goal.

One matched near-ordinary 1w_1t diagnostic pair on CPU5, 24 unchanged coarse
hooks, no cProfile/runtime profiler/captures, existing OUTCOMES and memory
observer. Server/library/kernel readiness and shutdown precede/follow pipeline
clocks. Shared dependency sources, physical inputs, native/Python binaries,
manifest/driver/site/controller and installed versions match. Submission bytes
match after the sole fresh-output-directory change. No environments or source
worktrees were duplicated. Generated outputs were 18.16 MB per variant.

                         Baseline      Candidate
Compilation seconds      1.533715      1.275819
Execution seconds        8.276517      8.977410
Total seconds           10.606973     11.012101
Raw callable seconds     3.656715      3.975499
Outside callable seconds 4.607542      4.990668

The candidate misses the required 0.7--1s execution payoff: observed execution
increased 0.700893s and outside-callable time increased 0.383127s. Finalization
exclusive time changed 0.209953 -> 0.480475s. These single observations are
falsification evidence, not statistical proof of a causal regression. The lower
compilation observation is not promoted as a gain. No full30/scaling acceptance
or new native clock is inferred.

Full behavior controls
----------------------

The coherent consumer gate passed 570 tests; extended runtime boundaries passed
700 with nine failures. All nine exact original tests reproduce the same errors
on all 27 original e858 Git-blob modules with the same current dependencies;
none is waived or silently rewritten. The initial source-stem owner interface
failures were fixed before these gates.

Both representative saved V10 edges preserve complete values, metadata, pixels,
masks, store/cache state and aliases: producer60records/123array roles and
loader104roles. A qualified offline dataclass-state decoder transfers original
stored references without constructor/capture/copy. Its instrumentation and
public realization occur outside different subclocks; edge timings are not
compared as whole-pipeline speedup evidence.

Four complete comparisons (fresh baseline and candidate against each retained
native repetition) pass unchanged CellProfiler numerical tolerances and exact
image controls: six CSVs, 120 TIFFs (two logical volumes), schema, relationships,
full physical inventory and 180 ordered source references. Native witnesses,
inputs, source and outputs are hash-checked before and after. No scientific
output or earlier failed receipt is replaced.

Architecture decision
---------------------

Flattening fields did not remove the semantic normalization lifecycle. Scalar
derivation still normalizes once and births provenance/identity plus two owner
allocations; leading-plane capture retains three normalizations and four
provenance/identity births. Public realization defers a real namespace allocation.
One source-context fusion removed a redundant normalization, but that narrow
route cannot materially close the full target gap alone. The earlier saved
normalization envelope is only 0.318s and contains mandatory work.

Stop this representation route rather than polish namespace deferral. Next
inventory the existing authorities and production data flow for repeated graph
projection/validation/serialization and manifest/store/workspace derivation.
Fresh baseline publication 0.768611s, reconciliation 0.300908s, load 0.797152s,
save 0.656345s are investigation envelopes, not claimed removable time. Prefer
one existing nominal authority and derived views, retaining public mutable
namespace epochs, raw schema/order, alias/pixel ownership and first errors.

Reproduction and custody
------------------------

Controller and site are retained byte-identically. Full local source/env freezes
remain at the absolute paths and SHA256 pins in baseline/candidate-source-pins.
Original helper scripts and native witness paths remain pinned there and in
strict-science. The saved V10 qualification preserves original graph/helper
hashes; its 1.027 GB capture is reused, not copied into this report. Exact rejected
production and tests remain reachable through the rejected Git commit. Run fresh
outputs only; finished evidence directories are immutable.
