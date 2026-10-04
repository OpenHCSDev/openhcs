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
