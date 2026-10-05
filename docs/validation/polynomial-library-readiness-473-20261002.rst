Polynomial library readiness repair
===================================

Issue 473: the existing illumination preparation hook prepared the unmasked
polynomial solver, but did not prepare the masked solver or every canonical
readonly array combination. The first measured pipeline execution could compile
a missing specialization after the server reported READY.

The hook now prepares the existing float64 C-order polynomial image signatures
with absent, writable and readonly bool masks, for writable and readonly images.
The numerical functions, preparation owner and registry remain unchanged.

The regression test uses a fresh subprocess and isolated kernel cache. It first
prepares the declared callable, then rejects every dispatcher compilation or
cache load while exercising 36 dtype, layout, mutability and mask combinations.
An independent polynomial oracle verifies the result; mutation, alias and
geometry-error controls preserve the public behavior. The original source fails
because the masked dispatcher remains unprepared.

On the isolated main-based repair, the preparation and fitted-illumination
controls pass 20 tests, with two existing skips. The original R0 ratchet passes
for openhcs, scripts and benchmark against main cf5a83f89, without changed tool,
checks, budgets or exclusions. The original R1 policy also passes against that
main at tested source 0a6109599, retaining the original 160-second budget.

The retained original Illumination3 run wrote masked kernel cache artifacts
inside its polynomial step (0.526s); the unchanged already-cached step took
0.016s. This supports the late-compilation diagnosis and is not a measured
repair speedup. The integrated repair's fresh ordinary single-worker observation
is 0.647611s execution and 1.961545s pipeline total, with 0.962373s compilation.
Server/library warmup and shutdown are outside these pipeline clocks. Both
authored saved NPY images are byte-identical to the qualified original output;
the full existing output inventory and numerical comparison gates pass.
One observation does not establish a paired speedup or broad performance gain.

Reproduction::

    OPENHCS_CPU_ONLY=true pytest -q \
      tests/unit/test_cellprofiler_kernel_preparation.py \
      tests/unit/test_cellprofiler_callable_kernel_preparation.py \
      tests/unit/test_fitted_illumination_fields.py

External retained evidence:

* ``/var/tmp/openhcs-masked-polynomial-prewarm-qualified-receipt-20261002.json``
  SHA256 8a50407145d4906af60514f4402ba0cf0df3037aadf2e873beb30b1d3eac7f3e.
* ``/var/tmp/openhcs-illum3-late-masked-preparation-attribution-20261002.json``
  SHA256 f6b2dfecfce1844d209f6f6301d97f3362cf4e886ce87c543e36517aa3beff2e.
* ``/var/tmp/openhcs-polynomial-library-main-local-controls-20261002.log``
  records the isolated main-based 20-pass gate.
* ``/var/tmp/openhcs-polynomial-library-main-original-r1-submodules-20261002.json``
  records no before/after findings and no increases.
* ``/var/tmp/openhcs-pr394-masked-prewarm-ordinary-science-v2-20261002.json``
  SHA256 21231dffa14dbe17bf824a4258f677e7d656122036da81e0b3d8c9c8bc2f9c02.

The original R1 attempt refused uninitialized disposable-worktree submodules;
its failure is retained. The supplement initializes independent local clones at
the exact recorded gitlinks and reruns the unchanged policy. The first scientific
validator incorrectly expected two Wound tables instead of two rows in Image.csv;
the retained V2 supplement checks the authored inventory without changing the
existing production comparison policy or tolerances.
