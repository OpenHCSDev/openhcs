# Matched WoundHealing normalization receiving

Source: `6cbf26d62db0385e88a2138eaac6809d68dc1898`, clean and frozen through receiving. ArrayBridge: merged `31632d8ce31016f0fe6ef28df61f49da397bf3e6`, version 0.3.8. The existing materialization worktree was reused; native extension source matches the sealed qualified baseline.

Actual fixed twelve-assignment workload, one and four OpenHCS workers on the same owned endpoint, one warm-up plus three measured repetitions per mode. All 96 assignment comparisons passed existing CellProfiler tolerances, with zero database, CSV, image, or declared-output differences. Native CellProfiler was not re-executed: comparison used genuine retained eight-assignment observations at their original cardinality. No native timing projection or native speedup claim is made here.

| Workers | Full output-complete execution median | Axis execution span median | Compilation median | Complete client operation median |
| --- | ---: | ---: | ---: | ---: |
| 1 | 7.908462 s | 7.839103 s | 0.179042 s | 8.149202 s |
| 4 | 3.199810 s | 3.060829 s | 0.183937 s | 3.443651 s |

Actual full execution scaling is **2.471542x** using the newly measured one-worker denominator. Full execution includes worker setup, processing, saving, publication, exports and finalization; external server startup and scientific qualification are excluded. Compilation is reported separately. Four-worker full execution decreased from the published prior cohort's 5.207406 s; the new one-worker measurement is 7.908462 s versus the prior 7.754487 s. The minimum 3x thirty-workflow goal remains unfinished.

The recipe records endpoint incarnation, all server thread affinities, workload and retained-reference arguments. Parent control uses CPUs 2–5; all server threads use CPU 5 for the one-worker mode and CPUs 2–5 for four workers. Numerical thread limits are one. Qualification uses CPUs 0–1 outside the measured processing clock.

Diagnostics are explicitly separate from production timings. Source reconstruction proves original loaded pixels are reused; source guards were not loosened. A four-fork saved-source replay priced normalization allocation changes, with exact numerical, metadata and producer-immutability controls. The archived P0 phases were collected before the patch and are diagnostic only. Raw reports, all eight receipts and progress streams, and a SHA-256 inventory support the production result above. This bounded receiving does not replace the published full thirty-workflow manuscript figures.
