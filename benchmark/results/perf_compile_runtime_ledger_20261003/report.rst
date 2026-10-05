Current compiler and runtime owner ledger
=========================================

This checkpoint supports PR #394 and issue #496. It measures unchanged
production source at ``480aed49b30448de4380af5c9274e48084e67b63``; it implements
no optimization. Main #526 was subsequently merged at ``5d62bd52c`` and changes
viewer documentation, knowledge projection and its test only. All measured
production Python bytes remain unchanged.

The original public 3D Monolayer driver runs one worker and one CPU thread,
with inline execution, default OUTCOMES completion and the normal RSS observer.
The server is reused per sweep. Server startup, mandatory library/registry/kernel
preparation and shutdown remain outside pipeline clocks. Both profilers are
disabled. This diagnostic adds 17 compiler/configuration boundaries to the
retained 24 nominal boundaries; its wrappers introduce observation overhead.
It is not a before/after ordinary performance comparison.

The public clocks are compilation **1.495826s**, execution **8.396727s**, and
total **10.694032s**. The execution root partitions **8.383970s** into
**3.660522s** at 211 declared callable boundaries and **4.723448s** outside them
(56.34 percent). Those callable boundaries include conversion, filtering and
metadata behavior; they are not pure numerical kernel clocks.

Selected disjoint execution-exclusive costs:

.. list-table:: Seconds within the original execution root
   :header-rows: 1

   * - Owner
     - Calls
     - Seconds
   * - Stack loading
     - 32
     - 0.781797
   * - In-memory output saving
     - 28
     - 0.667759
   * - Worker residual
     - 1
     - 0.501906
   * - Metadata publication
     - 5
     - 0.502201
   * - Step finalization
     - 30
     - 0.462263
   * - CellProfiler output recording
     - 26
     - 0.382119
   * - CellProfiler image-request construction
     - 30
     - 0.315012
   * - Artifact metadata reconciliation
     - 1
     - 0.295025
   * - Validation and unstacking
     - 28
     - 0.196794

Publication and finalization attribution differs from the previous diagnostic
on the same production bytes. This does not establish a code regression or an
optimization. GC and other stalls overlap owner clocks; they cannot be added
as independent costs. In-memory saving is not final TIFF export.

The compile-only root is **1.260937s**. Its nested, disjoint ObjectState owners
total **0.671090s**: constructor-exclusive 0.161911s, resolved snapshots
0.452570s, reconstruction 0.056494s, and saved-object forwarding 0.000115s.
There are 44 constructors, 88 snapshots, 532 recursive reconstructions and
42 saved-object reads. All ten ``get_effective_config`` calls total only
**0.195838s inclusive**, a subset of those state costs. Context creation cannot
claim the entire 0.671090s as removable work.

The two snapshots have distinct consumers. Live resolution observes current
parameters, live ancestor objects and live global context. Saved resolution
observes detached local parameters and saved ancestors/global context. Registry
callbacks receive their completed dirty/provenance baselines. Fresh compiler
registration also avoids stripped or independently edited UI states. These
facts reject unconditional snapshot collapse or existing-state reuse. The
source audit revalidates all 731 modules in the existing NRA census, covering
5,302 original classes; lexical source evidence is not a proof of callback
purity. Execution configuration state accounts for only about 0.062s.

An original replay of the retained 180-reference input document independently
rules out another route: 68 complete projection-cache-hit availability checks
take **0.024413s median** across nine unprofiled repetitions. Current invalid
source indices are still rejected after projection caching. A cache-before-
validation shortcut would lose that error. This is a replay ceiling with an
already-loaded document handler, not a current end-to-end saving.

Validation and custody
----------------------

All 15 descriptor, argument/result/error identity, call-once, nested clock,
fork-reset and source-drift controls pass. The 41 hooks install from verified
actual declaring files, including ObjectState's dependency source. Original
source, all eight actual dependencies, native binaries, environment and physical
inputs are checked before and after the run.

The first root launch stops before starting a driver because its full
environment fingerprint differs from the prepared agent environment only in
``CODEX_THREAD_ID``. The original matching environment runs the unchanged
controller once and validates science; no fingerprint bypass or freeze rewrite
is used. Driver session 17712 and science session 51754 terminate successfully.

The independent original scientific comparison, exact inventory and physical
source gates pass: six CSVs, 120 TIFFs, three input volumes and 180 ordered source
references. Retained native output witnesses are verified transitively; native
CellProfiler is not rerun here and no new native timing ratio is claimed.

``assessment.json`` joins the full execution/compile ledgers, scientific gate,
control and registration receipts to immutable original paths and hashes.
The full source freeze and recipes remain in the referenced maintenance
directory; the committed evidence totals about 164 KB before this report.
Scientific outputs, saved replay graphs and environments are not copied.

The multi-second runtime target remains unmet. Dominant integrated runtime
changes, matched ordinary before/after gains, branch architectural acceptance,
installed consumer acceptance, full-catalog/scaling measurements and refreshed
figure packs remain outstanding. The performance goal remains active.
