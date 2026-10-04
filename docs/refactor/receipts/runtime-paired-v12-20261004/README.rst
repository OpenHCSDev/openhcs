Fresh paired runtime and output qualification
=============================================

Measured source: ``cc4461bc8a58c90c2ae13a5dd3870a67e1d8fc0a``, synchronized
with main ``2df0918353b47fa07d19fe4b6cc8b52b5e4c1695``. All eight actual editable
dependency heads match the snapshot's repository pins. This snapshot includes
compiled-client submission/terminal-record reuse, the measurement query and
row-cache deletions, correlated feature batching, and exact saved-physical
source fallback. Subsequent compiler and public source cleanup is not measured.

All twelve strict comparisons pass: both ordinary observations against both
fresh native observations for each of the three original pipelines. Complete
measurement values, directed relationship correlations, pixels and physical
file inventories are compared using the existing CellProfiler policy. The 3D
pixel comparison requires exact equality. Original ordered source references
remain 180 for 3D, two for Speckles and ten for Beginner; native image-set counts
remain one, one and two, respectively.

Means of two observations
-------------------------

.. list-table:: One selected well, one worker, one thread; seconds and ratios of means
   :header-rows: 1

   * - Pipeline
     - Compile
     - Execution
     - Total
     - Native invocation
     - Execution speedup
     - Total speedup
   * - 3D monolayer
     - 1.049
     - 5.757
     - 7.057
     - 16.144
     - 2.804x
     - 2.288x
   * - Speckles
     - 0.482
     - 0.982
     - 1.674
     - 1.922
     - 1.957x
     - 1.149x
   * - Beginner
     - 0.615
     - 3.792
     - 4.633
     - 15.014
     - 3.959x
     - 3.241x

Every measured sample
---------------------

.. list-table:: Two independent observations per method; seconds
   :header-rows: 1

   * - Pipeline
     - Compile samples
     - Execution samples
     - Total samples
     - Native invocation samples
   * - 3D monolayer
     - 1.028707 / 1.068334
     - 5.278847 / 6.235180
     - 6.573325 / 7.540294
     - 14.833275 / 17.454537
   * - Speckles
     - 0.481356 / 0.482515
     - 1.005144 / 0.959042
     - 1.696810 / 1.650728
     - 1.960386 / 1.884385
   * - Beginner
     - 0.605824 / 0.623433
     - 3.631471 / 3.952364
     - 4.468181 / 4.797630
     - 15.154002 / 14.873502

Clock and interpretation
------------------------

OpenHCS server startup, mandatory function-library/kernel readiness and shutdown
are outside pipeline clocks. Execution includes generic runtime plumbing.
Total includes compilation and default OUTCOMES/RSS completion. Native ratios
use the existing full invocation clock, including pre-first-module work and
first-module-through-post-run work; process/import/JVM startup, input preparation
and the full warmup observation are excluded. The separate native
first-module-through-post-run clock is retained but does not replace invocation
in either plotted ratio.

Both samples are retained without outlier removal. Means and observed ranges
are descriptive; these are not confidence intervals or individual-patch causal
gains. The 3D execution spread is 0.956 seconds and its native invocation spread
is 2.621 seconds. Relative to v11, ordinary total means decrease by 0.367 seconds
for 3D, 0.178 for Speckles and 0.490 for Beginner. The 3D execution mean increases
by 0.083 seconds within that observed spread; its native mean increases from
14.505 to 16.144 seconds, contributing to the larger speedup ratio.

Mean total-minus-compilation-minus-execution is 0.251 seconds for 3D, 0.210 for
Speckles and 0.226 for Beginner. These clock differences are not disjoint causal
attributions to individual client or observer operations. Speckles remains the
slowest relative workload: its mean execution speedup is below the 2x target,
and its total speedup is 1.149x. Full-catalog and multi-well scaling acceptance
remain open. Two reused READY servers each complete the three-case sweep; this
bounded memory observation does not close the historical full-catalog OOM issue.

The earlier analysis-consolidation cleanup is present, but this benchmark
explicitly disables consolidation; no timing benefit is attributed to it.

Artifacts and reproduction
--------------------------

Adjacent PNG/SVG figures, ``metrics.csv``, ``timing_summary.json`` and
``qualification.json`` retain means, all samples, clock definitions, actual
dependency identities and all twelve scientific comparison results. Rendering
uses the existing v11 driver and v7 repository figure owner; no scientific run
or new plotting framework is introduced. The exact renderer is retained at::

   /home/ts/.local/state/openhcs-maintenance/20261004/plot_current_paired_timings_v12.py

The original immutable campaign and existing controller are retained at::

   /home/ts/.local/state/openhcs-maintenance/20261004/canonical-runtime-cache-client-paired-v12-qualified
   /home/ts/.local/state/openhcs-maintenance/20261004/canonical-runtime-cache-client-paired-v12-preparation

Scientific result SHA-256::

   df61eca666cd741f238d96b6f7fd2c22b10c14dc577b64a381969a36a0bb5906

Source/environment/input freeze SHA-256::

   24b4277094722d66ffe6bcccdbb3f543d197463c6a3990c9e764c9390affccda
