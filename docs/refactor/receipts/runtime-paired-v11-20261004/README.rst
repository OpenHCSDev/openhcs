Fresh ordinary and native runtime comparison
============================================

Measured source: ``771950f652e5237b71bf0b21b0b8050bda48e011``, integrated
through main ``32ededf24`` with eight current editable dependency sources and
matching repository pins. Subsequent alignment-owner consolidation and main
#577 integration are not included in these observations.

All twelve strict comparisons pass: two ordinary observations against two
fresh native observations for each of three original pipelines. Complete
measurements, relationships and image inventories use the existing CellProfiler
tolerances. The 3D image comparison additionally requires exact pixels for both
original 60 x 256 x 256 uint16 volumes. Original source reference counts remain
180 for 3D, two for Speckles and ten for Beginner.

Means of two observations
-------------------------

.. list-table:: Single well, single worker; seconds and ratios of means
   :header-rows: 1

   * - Pipeline
     - Compile
     - Execution
     - Total
     - Native invocation
     - Execution speedup
     - Total speedup
   * - 3D monolayer
     - 1.032
     - 5.674
     - 7.423
     - 14.505
     - 2.556x
     - 1.954x
   * - Speckles
     - 0.478
     - 1.042
     - 1.852
     - 1.939
     - 1.861x
     - 1.047x
   * - Beginner
     - 0.607
     - 4.053
     - 5.123
     - 15.028
     - 3.708x
     - 2.934x

Clock and interpretation
------------------------

Server startup, function-library/kernel readiness and shutdown are outside
OpenHCS pipeline clocks. Execution includes the generic runtime, rather than
only callable time. Total includes compilation and ordinary OUTCOMES/RSS
completion. Native uses the same full invocation clock as the previous v7
comparison, excluding imports, JVM startup, input loading and the warmup
observation. Its separate first-module-through-post-run clock is retained in
the JSON but is not used for the ratios.

Both observations are retained and visible in ``matched_runtime_samples``.
These are descriptive observations, not confidence intervals or attribution
to any individual refactor. The 3D execution samples range from 5.016 to
6.333 seconds. Speckles execution ranges from 0.907 to 1.177 seconds.
The total-time target remains unmet for 3D and Speckles; Speckles is only
1.047x faster than native on total. Full-catalog and multi-well scaling
qualification remain outstanding.

The saved-output/consolidation cleanup is included in the measured source,
but this benchmark disables consolidation. No benchmark gain is attributed
to that fix. Later diagnostic profiling is separate and does not replace
these uninstrumented ordinary observations.

Retained artifacts
------------------

The adjacent PNG/SVG figures, ``metrics.csv``, ``timing_summary.json`` and
``qualification.json`` contain all measured samples, clock definitions,
dependency identities and twelve scientific comparison results. The complete
unchanged campaign is retained at::

   /home/ts/.local/state/openhcs-maintenance/20261004/canonical-runtime-chains-paired-v11-qualified

Scientific result SHA-256::

   608a83ff5903f51652ff3d0d61793cad4efaf27b9085dda958174d1139e60a52
