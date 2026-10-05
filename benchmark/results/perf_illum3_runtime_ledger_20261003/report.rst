Illumination 3 compiler and runtime diagnostic
=============================================

The weakest retained single-thread native comparison is still dominated by
framework work. On unchanged production source 4c0d62e45, one fresh ordinary-path
diagnostic records 0.422891s execution, 0.597369s compilation and 1.419051s total.
The measured execution root is 0.415053s: 11 raw callable invocations account for
0.111740s; the remaining 0.303313s is 73.08% of that root. These are diagnostic
observations, not an optimization, an ordinary paired speedup, or a replacement
for the two-repeat native comparison. The objective remains unfinished.

The original public driver uses one well and one worker on CPU5, mandatory
library/kernel readiness before pipeline clocks, default OUTCOMES and the
original memory observer. Startup and shutdown are excluded. The official
benchmark lease, source/native/environment/input custody and bounded artifact
controls pass. Both profilers are disabled. All 41 coarse hooks preserve the
original call, result/error identity, descriptor and argument mutation; 28
controls pass. Exclusive clocks sum exactly to each root. Original interval
JSON files are retained rather than reconstructed from percentages.

No event-emitting Numba compilation was observed
----------------------------------------------

A passive listener is installed after the original installed ``numba.core.event``
module executes, before readiness. There are zero native ``numba:compile`` START
or END events in the retained startup and measured roots. Original module and
dispatcher bytes are pinned. Unique bounded event batches flush after each
measured root stops, so forced shutdown cannot erase its evidence. All required
root flushes pass; the four event files total 3,107 bytes with no refusals/errors.

This observation rules out event-emitting dispatcher compilation as its pipeline
cost. It does not measure cache loads or explain the older 0.686775/0.385197s
execution spread. The existing polynomial preparation already covers its
declared masked/unmasked and writable/read-only families; no missing warmup is
inferred from a truncated source excerpt or the old variance.

The dominant compiler term is state construction and resolution
-------------------------------------------------------------

Compilation's root is 0.588262s. Twenty-three ObjectState constructions,
46 distinct live/saved snapshots and 343 reconstruction calls consume 0.383406s
in disjoint exclusive clocks; saved-object reads add 0.000067s. Ten effective
configuration reads take 0.192388s inclusively, already inside those costs.
That is neither an additional cost nor a removable-work estimate. The reads
span before and after the compiler captures its concrete configuration.

Execution has four state constructions and eight snapshots, totaling 0.055237s
exclusive including reconstruction and saved reads. Other measured costs include
output recording 0.040833s, finalization 0.025324s, loading 0.021657s,
reconciliation 0.021559s, worker residual 0.021557s and publication 0.017187s.
These describe separate production consumers. No entire lane is claimed removable.
The source map identifies five reads before capture and five afterward, without
per-call timing. Existing requests and contexts are the strongest candidate
owners for later reads, but callback mutation and late errors prevent blind
substitution. No saved configuration optimization is qualified yet. Live/saved
baselines cannot be collapsed unconditionally or late edits ignored.

The installed ObjectState and python-introspect editables are the owned external
trees at a01f8939b9 and ed1e4eb15f. The separately frozen canonical dependency
copies have different revisions. Assessment pins distinguish them. The earlier
731-module AST census is a different epoch; this report does not promote it as
a current global architecture proof. The selected 13 current modules have a
refreshed 71-class NRA census, retained with the determining source map.

Science and rejected route
--------------------------

Both authored float32 NPY outputs, each 463 by 461 pixels, pass the original
comparison against both retained native repetitions. Polynomial correction's
maximum difference is 2.98e-8 under the existing 1e-6 tolerances; convex-hull
correction is exact. Full physical inventory, source identities, correlations,
input/native witnesses and before/after custody pass. Native was not rerun, so
there is no fresh native timing or new paired performance ratio.

The first science-reader invocation failed its final environment guard because
dependency imports added four reader-local environment defaults. Its failure and
per-key hash audit are preserved. The corrected reader runs the unchanged full
controller guard in fresh interpreters with the exact original launch environment
before and after comparison. No keys are filtered or rewritten; both checkpoints
pass. The scientific comparison and tolerances are unchanged.

Separately, six actual-source render replays find only 0.086086s median removable
completion/return rendering, versus the retained Illum3 total target gap of
1.226108s. Mandatory compile/execution render epochs remain independent, and
mutation/callback/error controls pass. Reject this as the dominant performance
route. Retaining the actual executed request remains a separate provenance repair.

Custody and reproduction
------------------------

``assessment.json`` pins every byte-identical compact original receipt and the
full local freeze. Frozen controller/site/reader recipes remain at their pinned
maintenance paths; the full effective environment intentionally includes the
original controller agent identity. This is not a portable turnkey replay bundle.
No environment, scientific output, saved graph or source worktree is copied into
this report. The receipts total approximately 191KB. Existing PR #394 / issues
#384 and #496 carry this investigation; no new production speedup is claimed.
