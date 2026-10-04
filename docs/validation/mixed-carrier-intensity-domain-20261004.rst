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
