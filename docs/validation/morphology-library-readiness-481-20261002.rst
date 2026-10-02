Morphology library readiness for canonical declumping signatures (#481)
======================================================================

The first frozen6e69 Speckles observation executed its second IPO step from
1790972729.5844479 to1790972730.5785608. The masked float32 declumping smoothing
specialization was written at1790972730.3320456, inside that measured step.
This disproves complete library readiness for that invocation. The cache-write
witness does not measure exclusive compilation time.

The existing Numba morphology backend warmed partial masks only with float64.
IPO's separate preparation used float32 with full masks. A fresh-cache current
main control reproduced the exact maskedfloat32 signature request after public
prepare_processing_callable(erode_objects); a refusal of Dispatcher.compile,
including disk loading, correctly failed. Closed #352 covered different erosion
and quantized-threshold obligations and is not reopened.

The existing NumbaNumpyMorphologyBackendStrategy.prepare_backend now invokes
its original smoothing method over float32/64, writable/readonly images and
writable/readonly full/partial masks. Its contiguous conversion still owns C/F/
strided layout behavior. The original local-max preparation stays intact.
No numerical kernel, runtime method, dtype conversion, public default, new
registry, cache or per-pipeline exception is introduced.

Qualified isolated production/test commit8bd25dac3 is based on main62c57a8c9.
Normal merge91a13e28f incorporates current main6849d09b1 and its independently
qualified #477 repair. Eight meaningful isolated controls pass, including two
fresh interpreters using cold then populated owned caches; both refuse any late
compilation or disk loading. Existing float32 exact SciPy-rounding and planewise
controls also pass. Original R0 allthree roots has every metric delta zero;
original R1 passes its unchanged160second budget with empty before/after/increased.

The integrated frozenadef79b4 source ran actual Speckles1w1t through the public
reused READY server, default OUTCOMES and memory observer, one inline worker and
one thread on CPU5. Its single observation is0.959121s compilation,1.915174s
execution and3.212164s total. Library/kernel/server preparation and shutdown are
excluded; compilation and output closure remain in total. No kernel-cache files
were written during the measured step window. Complete authored output inventory,
allthree CSVs and exact scientific bytes pass against the fully qualified6e69
reference with159 rows; existing fullnative science is transitive through those
unchanged bytes. No additional native process was run for this readiness-only
change. Seven parent integration controls pass; the isolated planewise control
is recorded separately rather than overstating the parent selection count.

This fixes readiness; it does not materially close the performance gap. The
original1.9496s execution/3.1406s total is retained with its observed late JIT.
A compiler-instrumented1.0506s execution is diagnostic and is not substituted
for ordinary latency. No matched causal saving, new main-only benchmark, full
catalog performance claim or statistical significance is asserted.

Qualified receipts and SHA256:

* ``/var/tmp/openhcs-speckles-late-masked-float32-readiness-20261002.json``:
  ``903331f804e491334ca3c4d005bc23d34c5930b080c56db6c118701baa4df723``.
* ``/var/tmp/issue481-morphology-readiness-qualified-receipt-20261002.json``:
  ``8481ad6fdebd6bed1ba93e7a3fa1ce4ca442c63bacb5f3b349725cdc10525877``.
* ``/var/tmp/openhcs-pr394-morphology-ready-speckles-science-20261002.json``:
  ``29526b6c5c37bbd840c706393b9290695894bc80a2247aedc7c718cb58ee5477``.
* Ordinary source-freeze:
  ``de3140edb42f54ef4b1a8f162fd0261151262df1305bfcb1a5c908ff6f632724``.

Original failure logs and the first source-local outer test-cache invocation are
retained; the test controls were repeated with explicit task-owned caches.
Frozen source/env/dependencies/native inputs and the original shared source-
identity cache were not cleared or modified by isolated controls. Actual public
runs retain ordinary cache behavior. External custom providers remain outside
the admitted existing backend-family signature domain.
