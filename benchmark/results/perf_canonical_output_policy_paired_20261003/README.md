The output-policy correctness fix is merged in [PR #531](https://github.com/OpenHCSDev/openhcs/pull/531), closing #530. These fresh observations use performance source `ee8f97552b349499655bb3f961860b34dc784071`, synced with main `ba7b26b82`. Existing environments and the public ordinary/native drivers were reused; both repetitions are retained. Full strict saved-output comparisons pass for all eight ordinary/native pairings, including exact 3D images.

| Pipeline | Compile | OH execution | OH total | Native CP invocation | Execution speedup | Total speedup |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3D Monolayer | 1.176 s | 8.994 s | 10.974 s | 14.317 s | 1.592× | 1.305× |
| Speckles | 0.498 s | 1.261 s | 2.091 s | 2.081 s | 1.650× | 0.995× |

Means use both measured observations. Ordinary 3D execution spans 8.562–9.425 s; the earlier qualified mean was 9.127 s. These separate two-repeat observations do not establish a causal speedup. The remaining 2× execution gap is 1.835 s, so the larger generic source/context/publication work remains necessary. Seven corrected CP groups preserve their input instead of producing anonymous image replacements; this is an architectural dependency, not completion of the performance target.

Server startup, mandatory library/kernel readiness, shutdown and native imports/JVM/loading/full warmup precede or follow pipeline clocks. Ordinary total includes compilation and default OUTCOMES/RSS completion. This is a two-case preview; full30 and scaling figures remain unfinished. Figures use the existing `benchmark.reports.cppipe_figures` owner with a 2× reference. `timing_summary.json`, raw CSVs, native reports, strict science and `qualification.json` retain determining evidence.
