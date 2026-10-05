Source-scoped photometry authoring
=================================

Scope
-----

One maintained how-to owner: docs/source/guide_for_biologists/image_sources.rst,
allowlisted as openhcs_image_sources. Packaged SKILL.md and the existing custom
authoring reference link to its new subsection; neither copies the procedure.
No runtime, codec, grouping, measurement, label, or provenance changes.

Determining evidence
--------------------

Two original source-boundary errors were reviewed read-only. An invocation
requesting two named images retained an inherited SITE stack and rejected the
second image with ``STEP_INPUT binding ... selects no current planes``.
Separately, a custom scalar measurement declared nominal label inputs without
an image-set context relation. The exact artifact address existed, but its
fixed producer channel differed from the consumer, and runtime rejected it.
These are distinct incomplete declarations, not proof of wrong-channel values.
The first author independently changed the consumer's variable component;
execution of that new revision was not qualified by this audit. No author
was contacted or given source, settings, biological evidence, or feedback.

The existing RuntimeArtifactInput._records/_matches_execution_scope checks
exact producer address and declared identity; NamedSourceBinding projects only
current represented planes. InputImageSetContextSourceRelation owns the custom
input context and does not regroup or broadcast. The original CellProfiler
object-measurement ancestor already derives it from selected image inputs.
The docs fragment uses these owners, not a replacement selector or alias.

Claim check: open PRs at the checkpoint were #404 and #160, neither this guide.
#743 is merged multi-image provenance delivery; #722 remains the distinct
wrong-numeric-channel report. #889 is a regional floor/clamp guide, not a
runtime photometry repair. Dewey received the exact source/error distinction
directly; no request to coach either live author. Current-main integration
started at b1e720f5e; all foreign gitlinks and cold validation history remain.

Qualification
-------------

Pending focused declared-input constraints, source/projected knowledge section
retrieval, packaged route availability and isolated managed sync. Original
failed inputs remain in their science journals, untouched. Future normal
bundles only; no live author skill replacement and no autonomous-gain claim.
