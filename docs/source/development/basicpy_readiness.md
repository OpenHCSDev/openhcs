# BaSiCPy readiness checkpoint (#213)

Current parent checkpoint: real BaSiCPy Python3.14 fits and paired OpenHCS
Python3.12 CPU fits, dtype behavior and field provenance checks passed. See the
canonical [2026-09-30 receipt](../../validation/basicpy_parent_numeric_20260930/checkpoint.rst).
No install, compiled/MCP execution or biological acceptance is claimed.

The current packaging change declares `openhcs-basicpy>=1.3.1,<1.4` in the
ordinary project dependencies. It supplies the reviewed JAX fork under its
existing `basicpy` Python API; upstream PyPI `basicpy` 2.x is not substituted.
The separate source requirements file is removed. The paired fork release must
be published and resolved before this dependency change can be merged or called
installed. Linux, Windows and Apple Silicon receive it automatically; Intel
macOS is excluded because modern JAX no longer supplies that platform's wheels.
This does not assert that illumination correction is available on Intel macOS.

The remaining text records the historical 2026-09-29 source-only checkpoint;
its pending checks and owners must not be read as today's runtime state.
Original backend/dependency owner: Linnaeus. Parent PR151 owns recipes/policy. Memory/
session PR208 remains independently pending actual live acceptance. Its two
independent authority findings are corrected/published in `d69d65adb`; no memory
MCP measurement or installed-history readiness is inferred from that source fix.

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

Source tracing found another range boundary: ArrayBridge's outer decorator
defaults to preserving/rescaling into the input dtype on **direct** calls. Removing
the adapter's `astype` alone was therefore insufficient. The paired
[ArrayBridge PR2](https://github.com/OpenHCSDev/ArrayBridge/pull/2) extends the
existing dtype wrapper's typed `dtype_config_default` keyword and reflected
parameter owner; no BaSiC-specific wrapper, registry or bypass is introduced.
OpenHCS declares `DtypeConfig()` (its existing native-output owner) on this
callable. Explicit caller/step dtype policies can still override that default.
The exact ArrayBridge commit `7f94d27925348f0cf0e4cc200692a4214c3722b2` is recorded
in both the gitlink and source requirements. PR2 is stacked on the separate
retained-history PR1; neither is merged or installed here.

The paired [BaSiCPy draft](https://github.com/OpenHCSDev/BaSiCPy/pull/1) reuses
Tristan's clean JAX prototype `ae2c647`, rather than PyPI 2.x's PyTorch API.
The historical checkpoint used `requirements-basicpy.txt` to pin the reviewed
fork commit; that file has now been removed in favor of the ordinary dependency
described above. No Git URL enters PyPI metadata. The historical source-only
installation route is not an instruction to modify the active analysis venv.

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
targets exactly `[SITE]`, with fixed Z/time and channel grouping. In addition to
the existing required-axis inclusion check, the fitted-field declaration owns
an exact metadata-backed observation-domain check before fitting: retained
varying components must be SITE only. Mixed SITE+Z/time/channel and Z-only stacks
are rejected, not silently flattened into observations. Raw direct-array callers
declare the leading N themselves; absent source metadata is not invented.
Time-only pipeline admission and numerical volume readiness remain unverified.

The wrapper now returns corrected main flow plus flatfield/darkfield from the
**same real fit**, through existing `artifact_outputs` image sidecars. Local
`FittedIlluminationFieldOutput(SourceProjectedImageOutput)` owns the aggregate
source-context transformation: complete-stack/count/grid admission, all
contributor provenance via the existing metadata owner's
`collapse_leading_plane_axis()`, and clearing pixel-range metadata that does not
describe fitted parameters. It does not select a false source plane or repeat
the field N times. Existing declaration bindings retain group lineage; artifact
names own persisted filenames, with on-demand viewer inspection. No shared
core artifact/runtime/config file or generic registry was changed. Runtime
materialization and compiled/MCP routing still require real acceptance.

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

Initial five checks passed (0.009s); the current expanded seven source checks
pass in 0.018s under Python3.14.7. The new API guard initially selected a local
variable's name instead of the factory's `decorator` declaration; the selector
was corrected without changing an API or weakening a runtime assertion. Checks
cover aggregate field-owner projection and the paired typed-default API in
addition to knobs/enum/contracts/range/source-pin ownership. Focused Ruff and
diff checks pass. These checks do not import OpenHCS/JAX or execute a model.
Normal merge of fetched `openhcsdev/main283b21275` is `2e4409871`. The source
follow-through is `a61f8bf82`, followed by normal merge `3938002b9` of latest
main `de23449a4` (#219, outside this surface). Recorded submodules are initialized,
with only the reviewed paired ArrayBridge gitlink advanced. Parent #151/#212 is
now merged/installed; this worker did not install.

Provider-free numerical/projection regressions are written but **not run**:

- Nine fitted-field metadata cases retain all contributor paths/common fixed
  components and reject mixed/Z-only axes, one-plane context, wrong grid/count.
- Two real BaSiC tests use only 24 synthetic 32x32 same-channel observations:
  direct decorated-call floating range and formula/known-shading field inspection,
  plus moving-object versus stationary-pattern biological-leakage controls.
  No mocked BaSiC, alternate pipeline or blind input/reference is used.
- Paired ArrayBridge has four real NumPy regressions for native fractions,
  negative/out-of-uint16 values, explicit override and unchanged legacy defaults.

Those runtime assertions are prospective checks, not passing evidence. No new
scientific framework import, fit, MCP server or GUI/JVM startup was performed for
this follow-through under Confucius's shared slot.

## Focused antipattern / new-case review

Scope: changed wrapper, shared flatfield enum, JAX dependency declaration and
paired fork's DCT/Pydantic owners. Focused source/AST/catalog review, not full NRA
scan or global proof. Aggregate outputs and direct-call dtype policy are included
in this follow-through's source review.

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
- BOUND-2 / IDEN-4: direct-call dtype semantics come from the existing typed
  ArrayBridge/OpenHCS config owner, not the adapter's output dtype assertion.
  The paired API changes the callable declaration; generic consumers and
  explicit overrides remain on the same wrapper and runner family.
- IDEN-4 / BOUND-2: aggregate field identity belongs to its new existing-base
  output leaf and the existing metadata projection owner. New fitted outputs
  reuse that leaf plus one artifact declaration; no changes to generic runtime,
  artifact catalogs, switches, metric dictionaries or registries are needed.
  Added projection tests are the new-case experiment, still pending execution.

## Pending scheduled acceptance

Parent #151/#212's finite validation/install completed; Confucius now owns the
heavy live slot and frozen installed harness. This worker remains on source work
until the next-slot handoff, then uses nonblocking flock/resource guard. No new
environment/GUI/JVM/runtime, install or active baseline change happens here.

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
