Complete child measurements and dynamic producer addresses (#492/#495)
======================================================================

RelateObjects previously narrowed prior child measurements to its invocation
channel. BeginnerSegmentation retained all four producer channels, but only
OrigRNA reached its per-parent means; 63 OrigDNA/OrigER/OrigMito fields were
missing. The input object-measurement relation now declares complete producer
consumption. The existing projection owner shares compiler/runtime selection,
including PLATE semantics; duplicated planner and Relate admission paths are
removed.

Dynamic inputs now resolve each discovered group through the actual compiled
input plan and requested backend. Legal retained locations after workspace
rebinding remain distinguishable. ArtifactInputPlan owns immutable point-in-time
query-address snapshots. Both lookup domains use the existing bounded store
cache lifetime, removing competing flat caches and their invalidation/transport
rosters. Cache eviction may recompute; no cache speedup is claimed.

Qualified code is eeed09233eb951e049791d994614053d781c7d22, normally merged
with main 6ce527a29c421ef5a95217b58e8bc33a93ba5fa2. 211 related controls pass;
212 integrated controls pass. The original unchanged R0 and R1 pass on this
independent delta; R1 retains its original 160 second budget. Earlier compiled-selection,
foreign-address, pickle and architecture failures remain retained in the local
source-qualified evidence. This does not assert all of PR394's guards pass.

Actual scientific acceptance
---------------------------

The uninstrumented integrated execution source is
5ed0d13978db1cda92a490614d326525ad552af7. Both retained native repetitions
from 6e69b85122d3c1a44857835ba9b3fe77e743240d pass the complete original
saved-output comparison: all seven CSV and two TIFF outputs are consumed, measurement
and image differences are empty, and full physical inventory passes. Both sides
provide five known relationship-correlation keys and 2,093 pairs. Exact ten
physical source hashes, ordered occurrences/addresses/references/aliases and
authored pipeline match the retained native witness. No exclusion, comparator
alias, correlation waiver or tolerance relaxation was added; existing absolute
and relative numeric tolerances remain 1e-6.

The strict saved reader is source-pinned to the integrated PR394/#479 reader;
its hashes are in qualification.json and the complete retained receipt. This
qualifies the independent producer repair's outputs through the integrated
execution, not a standalone main-only execution or a fresh native run. It does
not promote PR394's unrelated architecture gates.

Against the previous ordinary output, the only changed scientific file is
results/MyExpt_Nuclei.csv, restoring the 63 parent means. Inventory and the
remaining six CSVs/two TIFFs retain their hashes; openhcs_metadata.json also
changes. Native and OpenHCS file encodings/row layouts need not be byte equal:
acceptance uses the original authoritative semantic views plus full physical
inventory, not a claimed cross-producer byte match.

The single integrated ordinary observation is 1.60391807556s compilation,
4.650205373764s execution and7.07008462120s total. It includes compilation and
normal completion; server startup/readiness/shutdown are excluded. This is a
correctness observation, not a causal performance gain: execution source also
contains other PR394/readiness changes.

Evidence and scope
------------------

qualification.json records source/reader/input/witness/helper hashes and the
original hashes of all retained files. strict-native-receipt.json.gz is the
byte-preserving compressed original complete receipt; original-r0.json.gz,
original-r1.log and both control logs retain exact qualification outputs.

Arbitrary external input-plan subclasses/custom mapping callbacks and
side-effectful external query-target callback-count stability under eviction
remain outside the audited concrete production family. Registered production
query targets are the existing location and dynamic-component leaves. No new
query cache class, flag, registry or compatibility dispatch was added.
