# Qualified Neighbors export fix receiving

This bounded record measures twelve repeated source assignments of ExampleNeighbors on clean production commit `e229a7f8ed8869841e11daf8a7b0824d40225d70`. Each worker mode has one warm-up and three measured full output-complete jobs. All 96 assignment comparisons passed with no database, CSV or image differences against retained genuine native outputs; no new native CellProfiler pipeline was run. Retained native clocks are comparison provenance, not twelve-assignment CellProfiler timing claims.

| OpenHCS workers | Full execution median | Axis-span median | Compilation median |
| --- | ---: | ---: | ---: |
| 1 | 8.758263 s | 5.935320 s | 0.346070 s |
| 4 | 3.211876 s | 1.884299 s | 0.364365 s |

Full execution scaling is **2.726837x**, against the updated one-worker baseline. Axis-span scaling is 3.149882x; the full job remains the performance headline. The older qualified source measured 12.246930 s and 11.280830 s (1.085641x). The four-worker full job decreases approximately 71.5%, and the one-worker full job approximately 28.5%. The old denominator is not used for the new scaling ratio.

Server startup and scientific qualification are excluded. Coordination, saving, exports, publication and finalization remain inside the full server execution job. The owned server and all its threads were pinned to CPU 5 for one worker and CPUs 2–5 for four workers; the client stayed on CPUs 2–5, with qualification workers on CPUs 0–1. Numerical thread limits and endpoint incarnation witnesses are retained in the recipe/reports. One owned endpoint is reused, with a fresh warm-up in each mode.

The fix removes unused relationship projection twice in the four-worker export admission/fallback route and admits existing output partitions according to requested subjects. The actual batch's CSVs remain byte-identical. Experiment reductions use the same demand decision. SQLite scalar-boundary replay is separately scoped and does not claim an observed whole-pipeline benefit.

This is one workflow receiving evidence, not a replacement thirty-workflow manuscript sweep or proof of the minimum 3x goal. It leaves about 0.292455 s of four-worker full-job reduction needed if the current one-worker baseline were unchanged; optimizations must be assessed on both updated modes. Published full-cohort figures retain their original sealed source and measurements until a new complete qualified sweep is available.
