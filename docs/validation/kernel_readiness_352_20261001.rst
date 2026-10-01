Prepare supported 3D and quantized threshold kernels before readiness (#352)
==========================================================================

The ordinary public 3D tutorial at synchronized main
``094425c8c81324da7a3878379074e1bd8234ff52`` requested three Numba specializations
inside execution after the registry had announced readiness. The trace records
int32 rank-3 erosion, float32/uint16 threshold codebook population, and the
uint16 diagnostic context. These cached ABI loads cost about 9ms in that trace;
they are not an explanation for the multi-second execution gap or a material
performance gain. The change enforces the requested preparation boundary.

Production source is ``e6a87e5601d2189b14fc87b0a538c9cd6ccef8b2`` against that
main revision and its unchanged recorded dependency pins. Source algorithms,
mask/identity contracts and scientific comparison tolerances are unchanged.

Ownership decision
------------------

The bounded question is which existing declaration must prepare supported
numeric specializations before a pipeline executes. Existing nominal authorities
are ``CellProfilerBackendStrategyMixin`` and the registered morphology and
threshold-diagnostics strategy families. Registry/callable preparation consumes
those declarations; the ZMQ server consumes the unified preparation operation
before reporting readiness. The concrete Numba backend owns its kernel input
ABI. Independent NumPy/SciPy and other provider leaves retain their own behavior.
Transport readiness is a consumer, not another kernel authority.

Required implementation/consumer relations, licensed by the user's preparation
and shared-layer requirements:

* The Numba morphology leaf prepares its existing public erosion operation for
  int32 labels in both supported spatial ranks, 2D and 3D.
* The Numba threshold-diagnostics leaf prepares both producer float dtypes and
  both code widths selected by the existing codebook producer: float32/float64
  with uint8/uint16. Scale values derive from NumPy dtype limits. Existing planar,
  whole-image, unmasked and partial-mask routes consume this prepared behavior.
* The existing registry/callable hook and server readiness chain consume these
  backend declarations. No transport-side kernel list or timed-execution warmup
  is introduced.

No new wrapper, authority, inheritance hierarchy or compatibility route is
needed. Preparation input tuples describe numeric ABI dimensions, not another
behavior-dispatch family. This authored leaf-declaration extension is not a new
NRA transformation or theorem of numerical equivalence. General readiness for
arbitrary new user-produced layouts/dtypes is not proved by this bounded gate.

Counterevidence and controls
---------------------------

The fresh-process empty-cache regression test first fails on unchanged main,
recording ten missed specializations across volume erosion and float64/uint16
masked diagnostic variants. After the fix, preparation through the public
callable hook exercises all those combinations without a dispatcher compile call
or signature change. Erosion is checked exactly against the existing SciPy
provider. Existing numerical threshold tests retain their exact assertions.

An earlier harness attempt failed before exercising preparation because its
isolated worktree did not yet contain the unchanged native extension. That setup
failure remains in the archive and is not the missing-signature reproduction.
Both native extension binaries were then copied from the synchronized shared
build and verified byte-identical. No C++ sources, ABI or dependencies change.

Original R0 passes openhcs, scripts and benchmark with no positive metric deltas.
Original NRA R1 passes its two configured detectors with all recorded dependency
sources in context and no increases; the existing threshold record-shape finding
remains visible. This is not all-detector cleanliness. The original ClassDef
inventory before/after is 702 modules, 5,147 original declarations, 5,135 projected
and all 12 unprojected OPEN retained. No classes, bases or method rosters change.

The final source passes 1,965 tests plus the 42 existing subtests, with one optional
Napari skip and two unchanged watershed warnings. The focused cold-process gate
passes both tests. Broad tests and static audits finish before runtime acceptance;
there are no other owned timed benchmark jobs alongside it.

Native parity and production readiness
--------------------------------------

Full Official30 native-reference qualification passes 30/30, every difference
count zero, on the final production checkpoint.

The final public 3D pipeline succeeds with the ordinary default memory observer.
Its observation-only trace records three readiness markers and zero dispatcher
compile calls after readiness, compared with three on synchronized main.

Scientific qualification uses the retained native CellProfiler 4.2.8.1 outputs
from ``official30-native-complete-fresh-20260928``. Existing 1e-6 absolute/relative
numeric tolerances and exact identity/discrete checks are unchanged. This is not
a fresh native timing/scaling experiment. Pipeline clocks exclude ready-server
startup and shutdown. Diagnostic clocks are not pooled into an ordinary matched
performance cohort, and no pipeline speedup is claimed for this readiness fix.

Continuing performance work
--------------------------

The separate exact-operation metadata prototype matched 7,440 real projections,
but ordinary main/prototype/prototype/main timing on the 3D tutorial saved only
0.204s execution and 0.194s total. That standalone route was rejected as too small
to address the remaining gap; it is not included in production. Reconstruction
and exporter prototypes that regressed real inputs or offered insufficient
end-to-end payoff likewise remain outside production. Parent issue162 remains
open for larger execution/compilation/export reductions and fresh native scaling
figures. The bounded readiness issue closes only when this fix is merged.

``kernel_readiness_352_evidence_20261001.tgz`` contains the source/pin/binary
receipt, original guards and census, original failure and final test/XML results,
controllers, actual late ABI trace and final public readiness trace, and native
qualification observations. ``SHA256SUMS`` authenticates every included file.
Large native/scientific outputs remain in the named benchmark workspace.
