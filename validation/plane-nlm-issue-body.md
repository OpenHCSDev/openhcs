Addresses #458. Dewey owns source; parent owns integration/live acceptance.

ONE08 entered ordinary `skimage:restoration.denoise_nl_means` after rescale and
tophat, then its isolated 4-GiB scope OOM-killed the native process. This was not
a host OOM. The original terminal receipt, kernel evidence, compiled plan,
candidate source, and `pre_nlm` output remain untouched in
`/home/ts/wt/openhcs-issue-batch-20260929/rbpms-r0010-development-434-20261002/output/`.
The selected physical C1 image is 2586x2586 and is assembled along SITE. Its
actual NLM kernel input rank and allocations were **not recorded**: treating a
singleton SITE stack as volumetric NLM remains a hypothesis, not a proven cause.

Dewey owns a CPU independent-plane processing declaration, not a runtime/core
repair. Existing `ProcessingContract.PURE_2D` owns slicing, restoration, and
metadata/provenance; scikit-image owns the original NLM algorithm. Existing
FLEXIBLE `slice_by_slice` exists, but public authoring excludes it as a runtime
parameter. JAX/Torch NLM declarations are not an equivalent installed CPU
scikit-image route. CellProfiler `reducenoise` is FLEXIBLE/FULL_STACK, not an
explicit per-plane declaration with the original public NLM parameters.

Scope: add an explicit PURE_2D operation on the existing NumPy processor surface,
automatically discovered by the original registry, without changing volumetric
NLM, adding an axis guess/squeeze, copying an algorithm, or editing Root394's
core/runtime/registry files. Planck owns the frozen science input and small
engineering fixture; parent owns integration and installed/native qualification.

Acceptance: public discovery -> author/validate/render -> compile/execute of a
new small synthetic singleton SITE fixture; actual kernel rank 2, output
shape/dtype/value equivalence to independent original 2-D calls, declared axis,
units and provenance preserved, bounded peak RSS. Controls must retain original
volumetric NLM behavior, reject unannotated 3-D arrays, and demonstrate a new
PURE_2D declaration through unchanged generic consumers. No ONE08 replay, no
candidate09 authorization, no biological acceptance claim. Source proof and
installed engineering acceptance remain distinct.

Working checkpoint: new production declaration c7820b; tests/evidence 2f9cc9745,
now normally integrated with merged main cc9fcdfd4. Relative to current main,
the production delta is only54 lines in
`openhcs/processing/backends/processors/numpy_processor.py`. Current PR394
01875a772 roster was checked before integration; that file is not claimed.
Shared core/registry/smoothing files are untouched.

26 source controls PASS in7.155s/450124KiB aggregate RSS, including real fast/slow
scikit-image kernels, singleton/multi-plane input, exact pixels/dtype/rank,
metadata/provenance/calibration, strict bare-volume/unknown-kwarg rejection,
unchanged original volumetric adapter, nominal transport and a new independent
declaration through unchanged generic consumers/MI behavior. Original test
failures are archived and adjudicated in `validation/plane-nlm-458.rst`.

Unchanged original pinned scoped R0 PASS (17c630→c7820b, zero positive deltas),
14.205s/162612KiB; complete Python AST owner closure1120modules/snapshot,
zero parse omissions. Binary/Cython internals, dynamic alias/metaclass
resolution and global R1/FULL are not claimed.

Parent reviewed the source and is preparing a private ordinary wheel; Planck
owns the fresh tiny synthetic PipelineDocument fixture. Installed public
discovery/author/compile/execute and actual live rank/buffer/peak acceptance
remain PENDING, not replaced by source proof. No native job, science replay,
environment install or new fleet is started by this worker. Issue stays open
until that scoped installed acceptance. Original ONE08 OOM is not reinterpreted.
