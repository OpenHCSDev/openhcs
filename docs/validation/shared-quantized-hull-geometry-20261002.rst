Shared quantized convex-hull and line geometry validation
========================================================

This follow-up optimizes exact quantized-level reconstruction and shares its
geometry kernels. The earlier work in issue 158 and PR 161 was completed on
September 29; this change neither reopens that issue nor replaces its work.

The old transform rebuilt a binary image, grouped outlines, walked the hull,
and rasterized its edges for every observed integer level. The new reducer
accumulates column extrema in descending level order and paints only newly
covered cells. It uses the same ordered column-envelope walk as
``CellProfilerLabelHull`` and the same Bresenham segment rasterizer as the
existing worm geometry. It retains the original floating-point mask/min/max,
quantization, scale lookup and 256-to-16 recursion. Public line arrays retain
NumPy ownership, mutability, integer dtype, endpoint inclusion and tie ordering.
The 15 disconnected private illumination diamond-hull kernels are removed;
the separate live morphology diamond-offset hull remains.

The existing illumination backend preparation hook reaches C/F reducer layouts,
public line arguments and the label-hull caller before READY. A real readiness
control first failed because the painter's literal-zero offset specialization
did not cover the public line caller's integer offset. That RED log is retained;
the hook now reaches both actual consumers and passes compile/cache-load refusal.
No new class, registry or callable-keyed cache is introduced.

Source and local gates
----------------------

The isolated implementation is commit b97b62cecbf98bf137c7420a649770273e7f50bc,
against main a6c18f054457b7693fb0585ca2167b43325a0c01. The already-merged
masked polynomial readiness repair (PR 474, issue 473) is outside this diff.
Original R0 passes with no per-subject metric increase; original R1 passes with
no before/after findings and no increases, retaining its 160-second budget.
Related geometry controls pass 40 tests; the final label and readiness suite
passes 27. Root integrated controls additionally pass 43 tests.

Both captured real convex inputs match their retained outputs, input mutations,
output dtype/layout and alias behavior. An immutable old-Git oracle also matches
576 finite boundary cases and three nonfinite errors, including exact error
messages. Five local ABBA cycles on CPU2 give an outer-call median of
0.253749059s before and 0.034728013s after. The recursive 16-level call is
contained in the outer call; its saving must not be added to the outer saving.
Local replay alone is not an end-to-end performance result.

Ordinary pipeline comparison
----------------------------

The uninstrumented public-driver run compares frozen PR394 baseline
``eb2f23efdf6c9f7d4da0e5692567b3535f23f257`` (A) with the integrated shared
geometry candidate ``b4700288f6762674e5d79f95730e20cf6d348f16`` (B), in ABBA
order. This is an integrated PR394 comparison, not a standalone-main timing
comparison. The seven changed algorithm functions have identical ASTs in the
isolated and integrated candidate; the two geometry files are byte-identical.

Each case uses one declared well, one inline worker and one thread on CPU5,
a reused READY server per sweep, default OUTCOMES and the default memory observer.
Server startup, mandatory library/kernel prewarming and shutdown are outside
these clocks. Execution is the complete server job, including output/export
work. Pipeline total includes compilation and the measured client lifecycle.
There are two samples per source/case, with no exclusions or significance claim.
All environment, interpreter, dependency, native binary and scientific input
identities are frozen. Run-input hashes include the source-dependent request,
so A and B request hashes differ; the physical inputs remain identical.

Means, seconds:

.. list-table::
   :header-rows: 1

   * - Case
     - A exec (s)
     - B exec (s)
     - A total (s)
     - B total (s)
   * - Illumination3
     - 0.637207031
     - 0.405980945
     - 1.988957128
     - 1.892348221
   * - Untangle
     - 2.028668523
     - 1.239966273
     - 3.234328632
     - 2.311149861
   * - BrightField
     - 3.371351480
     - 2.054752827
     - 4.635292249
     - 3.294145465
   * - Wound
     - 3.385797977
     - 3.254446626
     - 3.976371000
     - 3.825717511

Every observation, seconds:

.. list-table::
   :header-rows: 1

   * - Run
     - Case
     - Compile (s)
     - Execution (s)
     - Pipeline total (s)
   * - 0-A
     - Illumination3
     - 1.057656050
     - 0.651572704
     - 2.080506507
   * - 0-A
     - Untangle
     - 0.612889290
     - 2.265993595
     - 3.393085145
   * - 0-A
     - BrightField
     - 0.740379572
     - 3.562403202
     - 4.889435869
   * - 0-A
     - Wound
     - 0.348586082
     - 3.533864021
     - 4.103729180
   * - 1-B
     - Illumination3
     - 1.084313393
     - 0.415795088
     - 1.901710610
   * - 1-B
     - Untangle
     - 0.601153612
     - 1.075628996
     - 2.196348816
   * - 1-B
     - BrightField
     - 0.715036392
     - 1.994254589
     - 3.259233217
   * - 1-B
     - Wound
     - 0.345472574
     - 3.512702465
     - 4.095615456
   * - 2-B
     - Illumination3
     - 1.120404959
     - 0.396166801
     - 1.882985832
   * - 2-B
     - Untangle
     - 0.599110126
     - 1.404303551
     - 2.425950906
   * - 2-B
     - BrightField
     - 0.690350056
     - 2.115251064
     - 3.329057712
   * - 2-B
     - Wound
     - 0.334090233
     - 2.996190786
     - 3.555819566
   * - 3-A
     - Illumination3
     - 0.931068659
     - 0.622841358
     - 1.897407750
   * - 3-A
     - Untangle
     - 0.791599035
     - 1.791343451
     - 3.075572119
   * - 3-A
     - BrightField
     - 0.694685698
     - 3.180299759
     - 4.381148628
   * - 3-A
     - Wound
     - 0.335768461
     - 3.237731934
     - 3.849012820

Illumination execution falls by 0.231226087s in this comparison, but remains above
half the qualified native mean. Untangle and BrightField exercise the shared
line kernel. Wound is a control without an expected hull gain; its two-sample
shift is not attributed to this repair. No all-workload speedup is claimed.

Independent saved science and native scope
-----------------------------------------

All 16 run/case combinations pass the existing full output inventory and science
comparison, with no tolerance or exclusion changes. Scientific files are also
byte-identical to the qualified retained outputs: Illumination has two NPY
images and no authored CSV; Untangle has two CSV tables and two PNG outlines;
BrightField has one CSV table; Wound has one CSV table with two rows.
Source/environment/native/input freeze validation also passes.

Retained CP 4.2.8.1 measurements used one CPU5 thread and one excluded warmup,
then two measured repetitions in the existing Python3.9/JDK11 worker. The CP
invocation includes pipeline preparation, module execution, post_run and closing
the measurements store. It excludes Python/JVM startup and pipeline/file-list
loading. These are retained matched-source timings, not new CP runs performed
for this patch. Full saved science was already qualified for Illumination,
BrightField and Wound and remains connected through the byte-exact OH gate.
Untangle's measurement-only gate passes, but its saved outline image has the
existing 96-pixel native mismatch; full native image parity remains RED and no
qualified native speedup is claimed for Untangle.

.. list-table::
   :header-rows: 1

   * - Case
     - CP sample 0 (s)
     - CP sample 1 (s)
     - CP mean (s)
     - Existing native science
   * - Illumination3
     - 0.532455969
     - 0.673695599
     - 0.603075784
     - PASS authored saved scope
   * - Untangle
     - 2.951127105
     - 2.998232635
     - 2.974679870
     - RED: saved image mismatch
   * - BrightField
     - 5.875675469
     - 6.428366317
     - 6.152020893
     - PASS authored saved scope
   * - Wound
     - 3.642940130
     - 3.915436237
     - 3.779188183
     - PASS authored saved scope

Reproduction and retained evidence
----------------------------------

The committed focused tests exercise the existing public geometry and library
preparation owners::

    OPENHCS_CPU_ONLY=true pytest -q \
      tests/unit/test_cellprofiler_worm_geometry.py \
      tests/unit/test_cellprofiler_label_hull.py \
      tests/unit/test_cellprofiler_kernel_preparation.py

* ``/var/tmp/openhcs-pr394-shared-hull-ordinary-abba-20261002/all-observations.json``
  SHA256 c79b670bbcd3ecf9d7ef2d0e922b0335bb43629bace0bcee0089bac08cbaadc1. Retains every ordinary sample and source-freeze witness.
* ``/var/tmp/openhcs-pr394-shared-hull-ordinary-abba-science-20261002.json``
  SHA256 8081e377b1b2d1657851120941ed62ce1b77f8fe1b1fbe9ac52b1277e40f62dd. Retains all 16 nonempty authored-output checks and hashes.
* ``/var/tmp/openhcs-shared-hull-committed-actual-replay-v2-20261002.json``
  SHA256 6e00617eae9248940a9c3dfdbbd979f11c3f78046f398fadc5076ca8d9118738.
* ``/var/tmp/openhcs-shared-hull-source-qualified-receipt-20261002.json``
  SHA256 333232d1c0855735c20e317b0d58edb91ca23f47aa419945a5e2d8a4ac056497.
* ``/var/tmp/openhcs-shared-hull-original-r0-20261002.json`` and
  ``/var/tmp/openhcs-shared-hull-original-r1-20261002.json`` retain unchanged guards.
* ``/var/tmp/openhcs-shared-hull-readiness-abi-20261002.log`` retains the first
  genuine specialization-refusal failure; later readiness controls pass.
* Native reports and per-repetition comparison receipts remain under
  ``/var/tmp/openhcs-current-slowcase-native-priority-20261002`` and
  ``/var/tmp/openhcs-current-remaining-priority-native-v1-20261002``.
