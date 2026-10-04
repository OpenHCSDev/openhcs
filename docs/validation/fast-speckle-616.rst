FAST speckle enhancement616
==========================

Source decision
---------------

Main634875dd0af084017e8383159f2d5ce118845429. Reused finished131 checkout;
foreign dependency worktrees/untracked diagnostics unchanged. No new worktree,
environment, installed package, viewer, science replay or runtime. PR608 owns
labeled-hole morphology; its source owner was notified before this change.
Only feature_enhancement.py consumes the existing grayscale-opening backend;
no morphology.py, backend registry, settings schema or preparation owner changes.

SpecklesFeatureEnhanceMethodStrategy owns FAST selection and mask restoration.
Its previous radius>3 FAST body repeats grayscale-opening implementation using
SciPy's general footprint filters. It now requests the declared OPENCV provider
through MorphologyBackendStrategy.for_callable and calls grayscale_opening.
The existing OpenCV owner composes the morphology backend and preserves reflect
boundaries and input dtype. No Gaussian/downsample/disk decomposition or radius
change; SLOW and radius<=3 stay on their original route. The existing wrapper
preserves PURE_2D, float32 output, mask and intensity metadata. IMPL-12 applies
to the duplicated opening procedure removed from this consumer.

Before-change AST evidence: refactor-audit's existing overlay parsed the whole
cellprofiler production package; original family and related _backend.py,
morphology.py, feature_enhancement.py declarations/callers were read semantically.
Registry/declaration selection is reused, not mirrored. This is not a global
NRA proof or dependency-wide structural audit; no new family is introduced.

Native allocation diagnosis
--------------------------

Inspected installed SciPy/version.py declares1.18.1. Its _min_or_max_filter
classifies a non-full disk as nonseparable and calls _nd_image.min_or_max_filter.
Published v1.18.1 NI_MinOrMaxFilter calls NI_InitFilterOffsets. The latter counts
all nonzero footprint points and allocates:

  product(min(image_axis, footprint_axis)) * footprint_nonzero * sizeof(npy_intp)

For a2586x2586 image, radius150 disk has70681 points and301x301 border-region
combinations:51230154248bytes (47.7118GiB) on64bit. This is one filter's offsets,
not two simultaneous offset tables; native frees offsets before returning.
The second filter repeats the work. The91KB dense disk itself is not the giant
allocation. Image/intermediate arrays and wrapper buffers are additional.

Primary native sources:
https://raw.githubusercontent.com/scipy/scipy/v1.18.1/scipy/ndimage/src/ni_filters.c
https://raw.githubusercontent.com/scipy/scipy/v1.18.1/scipy/ndimage/src/ni_support.c

This is a source-derived allocation request, not proof of actual resident bytes,
binary/source equality, OOM or historical leaf attribution. Original0119 job8
and status timeout remain unreplayed; Dewey retains interrupted custody.

Verification scope
------------------

Installed declared-callable receiving passed45 controls: finite float32/float64
planes, radius rounding, masks/background, original metadata projection,
independent PURE_2D planes and declaration-owned feature-size binding. Explicit
reflected-index opening checks cover ordinary, unequal and singleton shapes,
including radius150 on1x9; constant negative input produces zero top-hat.
No full retinal array, biology acceptance or whole-pipeline speed claim.
Existing agent-resource check showed14.9GiB available with disk/swap warnings;
checks must be small and serial, preserve failures, and use no arbitrary caps.

Original observations (not full callable acceptance)
--------------------------------------------------

First declared-callable check, PTY66758 terminal2: collection stopped because
the foreign old PolyStore source lacks TiffPhotometric required by currentmain.
No test body ran; no dependency changed. Parent subsequently supplied the
qualified main634875 whole610 target/dependency wheels for ordinary private
receiving, not permission to mutate that borrowed target.

Native process pair PTY22067 terminal0,96x128 float32 plane, SciPy1.18.1/OpenCV5:
radius8 original peak87048->87560KiB, .004337s; OpenCV87356->88396KiB,.017634s.
Radius24 original87580->121348KiB,.131366s; OpenCV87532->88644KiB,.001914s.
Both finite outputs were pixel-exact. OpenCV peaks were read before the original
comparison allocation. Single first-call clocks are not a stable timing campaign
or whole-pipeline speed claim. Radius24 offset formula34439944B agrees with the
observed original peak increase at this scale.

Separate radius150/1x9 finite plane: original .016052s, peak90884->93296KiB;
OpenCV comparison FAILED all9pixels. Original opened0 vs OpenCV opened-5 on this
fixture; no assertion was weakened. Followup constant1x9/radius4 control agreed
(-5 opening) on both natives. Followup constant1x9/radius150: SciPy erosion=-5
but its dilation=0. This violates constant preservation of reflected grayscale
opening. No claim of its C-level root cause or binary/source equality is made.

External contract decision
--------------------------

CellProfiler4.2.8 enhance_speckles explicitly defines white top-hat as original
minus erosion-then-dilation opening; its implementation calls SciPy's generic
footprint filters. The existing OpenCV owner's MORPH_OPEN executes erosion then
dilation, applying BORDER_REFLECT to each pass. The exact same rounded disk is
used. An explicit numpy symmetric-extension/window oracle independently proves
this mathematical contract for finite small inputs, including the oversized
singleton case. We intentionally do not emulate SciPy's constant-negative bug.
Thus ordinary-size SciPy parity and mathematical oversized-border correctness
are distinct claims; full bitwise parity with that defective SciPy case is NOT
claimed. No shape-specific production dispatch, clipping or approximation exists.

https://raw.githubusercontent.com/CellProfiler/CellProfiler/v4.2.8/cellprofiler/modules/enhanceorsuppressfeatures.py
https://raw.githubusercontent.com/opencv/opencv/5.x/modules/imgproc/src/morph.dispatch.cpp

Ordinary private receiving
--------------------------

Persistent engineering root:
/home/ts/wt/openhcs-issue-batch-20260929/engineering616

Original build-receive01.sh reused the existing ordinary builder and offline
ObjectState1.1.9, python-introspect0.1.16, PolyStore0.3.2 dependency wheels.
Build PTY82113 terminal0. Ordinary wheel SHA256:
f5677be10e8a8d25f74dd6e1ab9bf56f65e4178dab740e4d7d4d72ac96c8ca66.
Both feature_enhancement and polystore.config import from this private target;
feature bytes equal production source (SHA337841079eb8bae59b446f1266c27585c38fd0830db92f62d2db43c8c875288f).
No old target, foreign dependency source, shared environment or live SCI changes.

callable-receive01.log terminal1 retains an unrelated repository pytest-plugin
import failure. callable-receive02.log/PTy88533 terminal1 retains31PASS/6FAIL:
all pixels/masks passed, but the new metadata fixture incorrectly assertedNone
instead of the existing empty ImageUnitIntervalIntensityMetadata. The corrected
fixture compares the original owner's complete without-unit-interval projection.
callable-receive03.log/PTy29521 terminal0 records45PASS/.68s. Pytest cache warnings
and imported-plugin warning are retained; no repeated run solely for warnings.
These checks are ordinary installed registered-callable acceptance, not MCP
catalog/server, science pipeline or autonomous retinal acceptance.

declared-cost01.log/PTy38587 terminal0: same installed declaration radius150
on96x128 float32 synthetic plane completed .109319s; finite float32, unchanged
input. Process peak stayed348032KiB before/after the call. This peak includes
warm imports and is not a zero-allocation proof. Original SciPy filtering was
NOT run at this size (its offsets formula would request6.47GiB). No throughput
extrapolation to2586x2586 or stable campaign claimed. Own target22,630,400B,
wheel4,407,296B and source build21,307,392B were measured; no parallel fleet.

Normal current-main integration3612ba4982500427a5cb9199f1daddd28393ffa9 changed
only independent operations/docs/shell controls. The installed processing bytes
remain identical; the private wheel is honestly pinned to92ecee source, not
claimed to include the later unrelated main operations. Foreign dirty links and
old diagnostic directories remain unstaged/unmodified.
