# BaSiCPy readiness checkpoint (#213)

Status: draft **source integration**, not installed, import- or fit-validated.
Backend/dependency owner: Linnaeus. Parent PR151 owns recipes/policy. Memory/
session PR208 remains independently pending actual live acceptance.

## Implementation and dependency source

`basic_flatfield_correction_jax` delegates to the real JAX BaSiCPy model. There
is one ensemble fit, no copied low-rank algorithm or NumPy/CuPy fallback. Removed
ignored `lambda_sparse`, `lambda_lowrank`, `verbose`, renamed `max_iters` to
the model's `max_iterations`, and deleted the per-volume batch adapter. Repository
call-site search found only its own two duplicated internal callers. No alias
or compatibility reader is retained. Existing user-authored pipelines must use
the actual parameters; exported declarations/saved histories are not modified.

`FittingMode` comes from BaSiCPy rather than a second OpenHCS enum. Every exposed
knob reaches the model. Corrected output remains floating point; no integer
recast, clipping or unit-interval conversion is performed by this adapter.
`timelapse=False` avoids subtracting the estimated per-observation baseline.

The paired [BaSiCPy draft](https://github.com/OpenHCSDev/BaSiCPy/pull/1) reuses
Tristan's clean JAX prototype `ae2c647`, rather than PyPI 2.x's PyTorch API.
`requirements-basicpy.txt` pins the reviewed fork commit. As with this project's
existing source-only dependency files, no Git URL enters PyPI metadata. After
review, install that file in the coordinator-selected **isolated** validation
environment; do not run it against the active analysis venv. A published fork
wheel/version and ordinary optional extra can replace the source pin only after
actual import/fit acceptance and release review, not by adding an unavailable
PyPI dependency now.

The existing gpu/all JAX constraints rejected this modern candidate. They now
delegate exact JAXlib/CUDA-plugin matching to `jax[cuda12-local]>=0.9.2,<0.10`,
preserving the local-CUDA installation route without bundling new CUDA libraries.
JAX owns its dependencies ([0.9.2 metadata](https://pypi.org/pypi/jax/0.9.2/json),
[installation documentation](https://docs.jax.dev/en/latest/installation.html)).
This does **not** claim that unrelated Torch/TensorFlow constraints in all/gpu
support Python3.14, or that this change was installed/validated on CUDA.

## Observation and artifact boundaries

BaSiC requires independent, diverse observations of a common illumination field,
same channel/grid/acquisition. It cannot distinguish stationary biological
structure from shading merely because fitting converged. N>=2 is only a sanity
check, not sufficient scientific evidence.

The existing `PURE_3D`, `required_variable_components(SITE)` and
`allowed_group_by(CHANNEL)` declarations require a real cross-site stack and
reject a Z-only/mixed-channel FunctionStep. Direct calls accept `(N,Y,X)` or
`(N,Z,Y,X)`; they do not split volumes into separate fits. Pipeline acceptance
targets exactly `[SITE]`, with fixed Z/time and channel grouping. Multi-axis
SITE+Z/time grids and time-only pipeline admission are not claimed by this
checkpoint: the existing required-axis declaration checks inclusion, not an
exact alternative independent-axis set. Do not advertise those configurations
as validated.

Fitted flatfield/darkfield artifacts remain to implement/verify. Existing
`artifact_outputs`, image sidecars, `SourceProjectedImageOutput` and
`ImagePayloadMetadata.collapse_leading_plane_axis()` provide the likely route:
a fitted field is an aggregate of all observations, with contributor provenance,
not one selected source plane. Repeating the field N times or lying about a
plane projection would introduce identity/RAM debt. Core artifact/runtime files
are Zeno-owned; this patch does not edit them or introduce a second artifact
pipeline. Source-only aggregate projection feasibility is being checked before
adding a local behavior-owning output leaf.

## Actual evidence

Current metadata (no backend import): active Python3.12.3, JAX/JAXlib0.9.2,
NumPy2.1.3, SciPy1.18.1, scikit-image0.25.2. **BaSiCPy is not installed.**
The independent target `/usr/bin/python3.14` is Python3.14.7. The fork's candidate
matrix is documented in its PR; wheel metadata and AST syntax are not runtime
readiness. Coordinator supplied actual old-wrapper MCP discovery/signature
evidence; no fitting occurred on that running installed server.

Executed here, source only:

```
/usr/bin/python3.14 scripts/check_basicpy_source.py \
  --basicpy-source /home/ts/wt/basicpy-python314-20260929/src/basicpy/basicpy.py
```

Five checks pass (0.009s): knobs against actual upstream declaration fields,
enum owner, existing pipeline declarations, no integer cast/hidden dependency
failure, reviewed source pin and JAX-owned dependency matching. Focused Ruff and
diff checks pass. These checks do not import OpenHCS/JAX or execute a model.
Normal merge of freshly fetched `openhcsdev/main` is up to date at `a0263e82a`;
all recorded submodules are initialized in the isolated worktree.

## Focused antipattern / new-case review

Scope: changed wrapper, shared flatfield enum, JAX dependency declaration and
paired fork's DCT/Pydantic owners. Focused source/AST/catalog review, not full NRA
scan or global proof.

- BOUND-7: removed `hasattr(shape/dtype)` probing of a known array argument.
  Validate finite observations once, and preserve real model errors.
- MEMB-1/BOUND-2: upstream `FittingMode` owns optimizer choices, not a mirrored
  enum. New fitting modes require only BaSiCPy's owner, no consumer switch.
- IMPL-12: delete duplicated batch loops/forwarding. A new N count or volume
  shape uses the same model fit, not another branch/registry.
- IDEN-4/TIME-7: replace misleading Z/ignored-knob documentation and copied
  optimizer defaults with actual observation semantics and model-owned defaults.
- IMPL-13/TIME-1: paired fork reuses the public JAX DCT owner; copied private
  helper is deleted in place. Pydantic models retain durable schema ownership.
- New output case must extend existing image-output/artifact owners and prove
  aggregate provenance, not add metric/artifact dictionaries or special-name
  dispatch to generic consumers. This part remains under source review.

## Pending scheduled acceptance

Parent #151/#212 gets first released validation slot. This worker waits for
explicit next-slot handoff, then uses nonblocking flock/resource guard. No new
environment/GUI/JVM/runtime, install or active baseline changes happened here.

1. Verify imported paths first; real isolated Python3.14 dependency resolve and
   import against the exact paired source, without an old JAX downgrade.
2. Bounded real fit-transform on synthetic independent same-channel shaded
   fields. Inspect flatfield/darkfield; report time/RSS/PSS/private/swap/thread
   receipt. Compare known shading with moving-object and stationary-pattern
   controls to test biological leakage, not just output variance.
3. Compile and execute the same fixture through real OpenHCS/MCP and existing
   artifact materialization/inspection. Verify floating saved range and exact
   contributor/observation routing, no fake/mock UI or alternate pipeline.
4. Verify the affected installed entrypoint only after coordinator-reviewed
   integration/installation. Neither paired PR closes #213 until acceptance.

No blind inputs/reference answers or saved user declarations are reconstructed
or modified. No new paid provider/service calls. No source or runtime leak claim.
