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

Pending proportionate finite float32/float64 synthetic equivalence, radius
rounding, masks/background, borders and non-square/singleton planes through the
original declared callable, plus modest separated-process peak/time comparison.
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
(-5 opening) on both natives. Thus ordinary-sized parity does not establish
equivalence for a footprint much larger than its input. This unresolved case
remains a merge blocker under616's exact-preservation acceptance, not a reason
to replay retinal science, add an approximation, or invent a runtime guard.
