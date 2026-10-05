# Native-library discovery preparation

Endpoint catalogue preparation now calls public `threadpool_info()` after catalogue imports/projections complete and before READY. Cancellation remains authoritative both before and after discovery. Each job still discovers current libraries and applies its requested thread limits.

The single diagnostic configure call cost 28.65 ms with cProfile, including 17.28 ms of first filesystem path resolution; applying limits cost 0.04 ms. This identifies a small preparation dependency. It is not an end-to-end speedup result or a solution to the remaining single-well gap.

Actual normal catalogue preparation confirmed discovery before READY with unchanged library limits; subsequent 2-thread and 1-thread limits worked. Four existing cancellation/failure controls passed. [receiving.json](receiving.json) preserves exact source heads, receipt hashes and scope limits.

Persisted formats: none changed.
