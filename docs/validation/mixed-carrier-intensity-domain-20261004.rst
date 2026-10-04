Mixed-carrier current-intensity ownership checkpoint
==================================================

Active fix owner: Singer. Base main9f75ed8fbce41e6959b48c4961bc9cb612e6fd3b;
Root394 is merged, not an outstanding implementation promise. Current open
PR597 changes compilation/editor lifecycles and is disjoint from this family.
The existing Dewey/Root route was checked for an active conflicting claim.
This checkpoint publishes ownership and the determining relation; production
implementation, source controls and installed receiving are not yet qualified.

Source-derived counterexample
----------------------------

NamedSourceBinding.apply_loaded_payload normalizes a declared RGB carrier
before converting it to monochrome. Scalar grayscale preserves integer codes.
ImagePayloadStackComposition stacks conformable members via np.stack, promoting
mixed integer/float storage without reconciling their current intensity units.
Per-plane metadata still carries acquisition scales and source dtypes.
normalize_image_payload_intensity scales integer arrays but simply casts float
arrays; source-plane selection does not restore the previous storage dtype.
Consequently a legal composition can change a scalar member's downstream
normalization result, even though its values and source metadata were retained.

This is a source counterexample, not a replay of any original scientific job.
The retained original observations are pinned in the existing engineering
receipt BBBC007-CARRIER-INTENSITY-HANDOFF-20261004.rst under
engineering-neurite-units-20261003. They are not proof of the original run's
first wrong numeric transformation or its biological outcome.

Required relation and owner closure
-----------------------------------

Existing ImagePayloadMetadata must own the current analytical intensity domain
independently from acquisition dtype/full-scale provenance. The original
normalization recipe consumes that owned declaration through source loading,
composition and source-plane projection, then CellProfiler input/measurement
consumption and persisted metadata. Quantization proof is a separate fact:
losing exact quantization does not mean that normalized pixels became raw codes.
No consumer may infer current units solely from storage dtype or observed range.

Read the complete declaration, constructor/write, composition, projection,
transformation, serialization and consumption family before implementation.
Use existing nominal owners and cooperative capabilities where independent
behavior composes; delete the replaced competing normalization decisions.
No caller-specific rescaling, guessed factor/codebook, min/max normalization,
parallel metadata store, codec or compatibility alias is admitted.

Acceptance after coherent implementation
----------------------------------------

Tiny conformable declared scalar/RGB inputs must retain the same normalized
numerical units whether consumed independently, composed or reordered.
Include replicated and distinct RGB, explicit non-default source scale,
integer-only sources, raw floating analytical pixels, already normalized and
processed floating images, masks, source identity and persisted readback.
Require no double normalization and no loss of legitimate analytical remapping.
An independent declaration/capability must need only its own hook, not generic
consumer edits. Local source controls and ordinary installed/public receiving
are distinct readiness tiers; no original UNKNOWN input is replayed.

NRA/refactor-audit and applicable catalog entries were read: IDEN-1 for current
versus acquisition units, BOUND-2 for bypassing the existing metadata owner,
IMPL-2/3 for external consumer dispatch and IMPL-12 for copied procedures.
Whole production/dependency AST and R1 closure are next, using existing tools.
The independent #541 physical/pixel analysis-frame route remains untouched.
All foreign gitlinks and retained untracked histories are preserved. No current
scientific package, input, settings, job or viewer has been changed.

Authenticated source and implementation checkpoint
------------------------------------------------

Singer remains the active #599/#600 fix owner. On explicit public-source-fetch
authorization, the four exact recorded dependency commits were fetched from
their .gitmodules origins into the existing engineering599/source-references
directory, without changing shared dependency stores or creating a worktree:

* ObjectState9fb5b7eeea96f3b7bb0579de30718bbcc0018823
* PolyStore89deeef3662eabb11bc520fad9acd976698636bd
* pycodify108a8edbf25de258168756bac22c7572f018fa90
* ZMQRuntime04d813fe6c93f74166c05847afb1eae158d3c817

The original audit Package parser dependency03 pass completed with 59, 114,
12 and 67 parsed modules respectively and zero parse/source failures. Original
source01 and dependency02 failures remain unchanged. The earlier donor claim
was incorrect: a grouped shell command concealed individual cat-file failures.
The exact source objects are now independently present; this is not a donor
wait or a claim that source01 originally had complete coverage.

The existing ImageUnitIntervalIntensityMetadata record distinguishes normalized
analytical pixels from raw acquisition codes. An absent exact quantization
scale does not reset normalized pixels to raw. No second domain flag or store
is added. ImagePayloadMetadata now owns the numerical recipe; the original
normalization entrypoint delegates to it. The shared ImagePayloadStackComposition
ancestor reconciles mixed-domain members before dtype promotion, and its bundle
leaf delegates ordinary stacking through cooperative super(). The context-only
stacking procedure and all four production consumers are replaced together.
Native serialization that changes pixel values resets to the native raw domain;
value-preserving serialization retains the current analytical domain.

This is the first production checkpoint, not a completed qualification. Tiny
conformable numerical, projection, native persistence, whole-context R1 and
installed/public receiving evidence are still required. Logs reside under
/home/ts/wt/openhcs-issue-batch-20260929/engineering599.

Working source qualification and required receiving
--------------------------------------------------

Production05bcc19ecce31d7c1944f0f8cfe7e819534df33b is qualified below. Normal
integration of maina35d58163018785631f43ad7968e68b9569dc367 produced d6070360c:
its three incoming files are the published PolyStore floor, original spatial
field docstrings and their configuration-help control. All six #599 production
files are byte-identical to qualified05bcc. No foreign gitlink was changed.

The original source9f75 numerical diagnostic completed in 1.02s/147908KiB,
terminal0 and Swap0. It demonstrates independent scalar128/255 = 0.5019608,
but mixed-stack selection = 128.0. Its original metadata module SHA is
278383795c5db8631f109a75833aad509f0f2070ac56fd585787793ed7b64220.
It is a real original-source numerical counterexample, not scientific input,
a mock product or replay of a retained scientific mutation.

R0 initially found actual metadata-class growth +62 and a new foreign absence
probe +1. The correction acts on that owner, not the detector: the original five
intensity fields, quantization/projected-scale methods and numerical algorithm
now belong to ImagePayloadIntensityFields, an ABC composed into the existing
ImagePayloadMetadata. Existing SourceImageProvenanceFields owns replacement;
the declared MRO admits that concrete method ahead of the intensity contract.
The metadata leaf supplies the existing payload/leading-plane projection and
one axis-presence hook. Provenance, spatial placement and voxel spacing remain
their independent existing capabilities; no fields, stores or registries are
mirrored. The replaced methods and context-only composition procedure are gone.

The source-binding monochrome hook retains declared source scale; normalized
state, not float dtype, prevents repeat scaling. The saved-buffer context owner
retargets acquisition facts onto the actual independent buffer's intensity
state, without replacing its pixels. Changing native file pixels returns the
metadata to that native raw domain; value-preserving storage retains current
units. A common exact quantization scale now requires every represented plane
to prove it, not merely the subset with known proofs.

Source controls are terminal and original raw logs are retained:

* Initial numeric controls01: 11 PASS/9 FAIL. Eight incorrect fixture assertions
  required a composed diagnostic value_name to equal an original source label;
  spatial origin, shape and fill remain the actual checked contract. One real
  slotted-dataclass zero-argument super() failure was fixed through the original
  cooperative super(ImagePayloadBundleContext, self) hook.
* Numeric/projection02: 98 PASS, 5.82s/310312KiB/Swap0.
* Consumer03: 74 PASS/3 FAIL, 156 deselected. These were remaining assertions of
  the replaced normalized-domain marker after native pixel conversion; the
  assertions now require raw-domain absence, not a weakened quantization test.
* Complete affected family04: 265 PASS, 66 deselected, 13.51s/439904KiB/Swap0.
* Family05 at fe3cc: 267 PASS, 67 deselected, 14.63s/438180KiB/Swap0. Real source
  bindings, replicated/distinct RGB, reorderings, declared non-default scales,
  raw integer/float carriers, analytical remapping, masks/calibration/provenance,
  buffer identity and original image formats/readers are covered.
* Final changed quantization family06 at05bcc: 85 PASS, 5.31s/307920KiB/Swap0.
  No unchanged broad suite was repeated for the narrow final proof correction.

Two independent PixelAudit/MaskAudit capabilities cooperate in both C3 orders,
and a metadata normalization hook runs through normal generic composition.
The observed hook sequence is normalization, pixels, mask, with correct values.
The new cases add only their declarations/hooks, not generic consumer edits.

Original R0 Git3b03785f45df2ef5dc62ba6aed99294192ecbb01, unchanged existing
run_pinned_r0_419.py and all six changed production paths: final04 PASS,
26.29s/87052KiB/Swap0, positive deltas empty; ImagePayloadMetadata god-class
excess decreases by77. The first Python3.12 invocation's unrelated original
package forward-annotation NameError is retained; existing Python3.14.7 executes
the same original detector/caller successfully, without source adaptation.

Full audit Package AST at fe3cc parses 700 OpenHCS, 88 scripts, 156 benchmark,
697 test and 608 recorded dependency Python files with zero omissions. It emits
67/1/6/130 relevant full AST modules plus the original NumPy/skimage API ASTs.
Final05bcc's changed owner is parsed again through the original Package parser;
the remaining authenticated context and exact Git delta are unchanged. This
is source-family evidence, not behavioral or global-detector certification.

Original full-context R1/NRA0844525 remains incomplete: its unchanged55s deadline
expired during parse_python_module, 58.25s total/139444KiB/Swap0. Prior reference
clone and incorrect NRA API bootstrap failures remain in distinct original
logs. Exact dependency source availability is resolved; no donor, detector copy,
raised deadline or omitted dependency is used to obtain a false global PASS.

Next receiving boundary: one ordinary whole candidate package must exercise
declared tiny conformable scalar/RGB carriers through public source selection,
processing and persisted matched raw/result sampling with the same declared
scales, including swapped source order. Independent versus composed normalized
pixels must agree; analytical remapping must not be divided twice. This is
engineering-only, never the original scientific source/settings/job. Singer
owns receiving until normal package/lane custody is coordinated with the parent
and builder. No installed/native/MCP or biological acceptance is claimed here.

The byte-exact source02 archive includes changed production/fixture sources,
original parser/bootstrap callers, original numerical failure, all failed and
passing controls/R0/R1 logs, and full source-family evidence. Original source01
archive and all frozen scientific journals/UNKNOWN dispositions remain intact.

Archive: docs/validation/mixed-carrier-intensity-source02-20261004.tar.gz,
SHA256 f060dbbbec0ace28daeedf24dee83d00cb3af717b10887d973b39daa24411031.

Declared-memory and arithmetic-domain review correction
------------------------------------------------------

Parent review identified a reachable non-NumPy boundary: mixed intensity
reconciliation precedes the original runtime stack's host conversion. The
shared composition now resolves the original carrier's destination/device
before reconciliation, through one ancestor recipe also used by both pixel
hooks. The intensity owner uses the original ArrayBridge MemoryType.to_numpy
leaf before numerical operations; stack_runtime_slices still owns the final
conversion. Mask stacking derives its device from the output memory owner,
replacing the previous literal zero. No backend switch, converter or device
store is introduced. Applicable ownership findings are BOUND-2 and IMPL-12.

The original complete-family AST remains archived. Supplemental original audit
Package AST in memory-owner-ast-before07.jsonl covers OpenHCS memory and the
entire CellProfiler interop family plus exact recorded ArrayBridge source.
CellProfilerCompileTime contracts install the existing runtime adapter;
CellProfilerModuleExecutor._image_request and ImageOutputRecorder.runtime_input_value
normalize declared image inputs, including named/special inputs. Measurement
inputs also use normalize_cellprofiler_image_payload. Threshold explicitly
normalizes at its numerical entrypoint. The arithmetic proof-clearing callers
are smoothing, illumination, morphology, thresholding, color, image math,
edge enhancement, image geometry, intensity and feature enhancement. Direct
helper calls do not establish the adapter invariant. Consequently the shared
without_unit_interval_intensity_scale method now invalidates only an existing
normalized proof: raw-domain arithmetic remains raw, not implicitly normalized.
No caller-specific normalization patches are added.

Focused post-change memory/domain controls are next. They run the real original
MemoryType conversion and stack owners with a CPU-controlled CuPy leaf that
forbids implicit __array__, in both source orders, stack/bundle compositions,
implicit and explicit destinations, and nonzero device/mask preservation.
This source fixture cannot claim physical GPU or installed/public acceptance.
The previous 267/85 controls and original failure archives remain unchanged.
