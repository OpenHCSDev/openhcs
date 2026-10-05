# Generic image placement, export buffers, and grid readiness

One ordinary observation per pipeline, CPU5, one well/worker/thread, source `394e9bc74c58a81772e83d25502c53cd754fd00d`. Includes main e76ee3fde and PRs #772, #775, #776. ZMQ startup, function catalog and registered kernel preparation are excluded from pipeline clocks. Native references and previous qualified observations are reused, not remeasured.

| Pipeline | Compile s | Execute s | Total s | CP execution speedup | CP total speedup |
| --- | ---: | ---: | ---: | ---: | ---: |
| Speckles | 0.219 | 0.675 | 0.971 | 2.833 | 2.074 |
| Vitra | 0.184 | 1.180 | 1.463 | 2.354 | 2.028 |
| Wound | 0.092 | 1.057 | 1.206 | 3.515 | 3.166 |
| Yeast | 0.274 | 1.412 | 1.814 | 3.328 | 2.642 |

All four pass existing CellProfiler measurement tolerances, exact exported image comparisons, relationship correlations, complete output inventories and nonempty participating tables. Source, input, installed dependency and retained native guards pass. [Machine-readable receiving](receiving.json) records unrounded values and evidence hashes.

Compared with the previous qualified observation, total time changes by +141ms Speckles, −223ms Vitra, −814ms Wound, and −655ms Yeast. Preserve the Speckles regression. These are single observations of a coupled batch plus main's provenance fix, not individual causal estimates or a stable 2× minimum. Vitra has only about20ms of margin against the retained native 2× target.

The Yeast DefineGrid step changes from490ms to13.206ms. All17 grid kernel cache files predate that measured step. Ordinary lifecycle cleanup removed startup event logs, so the cache receipt does not claim a direct READY timestamp comparison. Independent fresh registered-preparation controls execute production-size mutable and readonly centroid calls with compilation disabled. Kernel bodies remain unchanged.

PR #775 preserves original image owners when CPU placement is identity and the mask is already admitted, deferring dense realization to the existing consumer. PR #776 uses one owned working buffer through generic uint8 conversion. Their private replay evidence remains scoped to representative consumers and retains allocator-order caveats; these public totals do not attribute the whole change to those leaf savings.
