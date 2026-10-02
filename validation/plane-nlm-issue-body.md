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
