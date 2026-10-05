Fresh paired single-worker runtime: V15
======================================

Measured production source ``4f2e44701c1c5460ca7e447c7b3d05e3530367ad`` includes the request-wide configuration capture and inherited progress admission fix (#595). Main #593 is merged; installed ZMQRuntime is merged #19 at ``04d813fe6c93f74166c05847afb1eae158d3c817``. All eight actual imported dependency heads, source/input hashes and environment guards are retained in the adjacent qualification.

Both ordinary observations and both fresh native CellProfiler observations completed for each original pipeline. All twelve pairwise scientific comparisons PASS: full measurement policy, relationship correlations, physical inventories and image comparisons. Both 3D label volumes match exactly; no plane flattening or tolerance relaxation was used.

Descriptive means of two observations (seconds):

======================================== ========= ========= ========= ========= =========== ===========
Pipeline                                 Compile   Execution Total     Native CP Exec speedup Total speedup
======================================== ========= ========= ========= ========= =========== ===========
3D monolayer                                 0.852     5.217     6.364    13.860      2.657x      2.178x
Speckles                                     0.486     1.036     1.674     1.893      1.828x      1.131x
Beginner                                     0.439     3.451     4.115    14.806      4.290x      3.598x
======================================== ========= ========= ========= ========= =========== ===========

Clocks exclude ZMQ startup, registry/kernel preparation, native imports/JVM/input loading, warmup and shutdown. OpenHCS execution includes runtime plumbing; total includes compilation and default OUTCOMES/RSS completion. Native uses the existing full invocation clock, including preparation, modules and closure. Single-worker execution is inline.

Relative to retained V12, OpenHCS total fell from 7.057 to 6.364 s for 3D and from 4.633 to 4.115 s for Beginner. Speckles total is effectively unchanged (1.674 versus 1.674 s), while its execution mean rose from 0.982 to 1.036 s. The new fresh native 3D mean is 13.860 s rather than V12's 16.144 s, so a smaller plotted speedup does not imply slower OpenHCS. These observations do not isolate any individual patch's effect. All samples are shown; no confidence interval or full-catalog/scaling claim is made.

Speckles remains the poorest relative-performance case. Its execution gap to 2x is approximately 0.089 s; its total gap is approximately 0.728 s. The remaining compiler, completion and IPO costs must be assessed against those gaps. Rejected historical heap/readiness costs are not current savings. The performance goal remains active.

The three direct OpenHCS progress queue bypasses were fixed by using the existing inherited server admission. A real server/client control verifies compiler, axisless and worker progress sequences and retained terminal watermark; worker forwarding drains before terminal completion. The two ordinary sweeps provide installed integration acceptance. Earlier V14 observations failed this integration and remain rejected, with no fresh native run or accepted timing claim.

Configuration controls: 34 PASS plus a saved seven-step Speckles request replay with one admitted capture and zero internal live-getter rereads. Authored PipelineConfig remains the step context provider; the public getter remains live and direct compile captures a fresh epoch. This is not a claim to seal arbitrary external mutation of ObjectState globals.

The separate public aggregate/Mosaic source-position fix is not included in these timings. Its valid-declaration alias counterexample remains open under #435; four previously reproduced baseline Volume fixture failures are also unwaived. Neither removes this pipeline-scoped scientific acceptance.

Retained immutable campaign::

   /home/ts/.local/state/openhcs-maintenance/20261004/canonical-runtime-coherent-paired-v15-qualified

Renderer uses the existing repository figure owner::

   /home/ts/.local/state/openhcs-maintenance/20261004/plot_current_paired_timings_v15.py

SHA-256 custody:

* ``strict-science.json``: ``2f2d6d2462e8d01b8688754e7b95edb21b9d2b3f47dd3197af8100929eb8fab4``.
* ``source-freeze.json``: ``ffc4089f7fcef08af92740b2cca15b81b2541435562357f14b8a925a811e7b2c``.
