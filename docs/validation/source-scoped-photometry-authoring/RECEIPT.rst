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

Qualification03 terminal0: 2.51s, 243932KiB peakRSS, swaps0. Existing paired
interpreter and immutable receiving20 installed code were read-only backing;
all five relevant source/installed owner files were verified byte-identical.
No build, installation, native/viewer/catalog launch or scientific operation.

Six existing input-context relation controls passed: valid image/label/graph
targets preserve context without regrouping/broadcast; output-image and
label-source references reject; output/contextless targets reject. The actual
RST fragment was parsed by the existing docs validator and executed against
those owners; its source context reference is exact and grouping/broadcast
relations remain empty.

The existing build_mcp_knowledge_assets projector copied 90 declared paths.
KnowledgeBaseService returned the same subsection from canonical source and
projected package trees: 3167 characters at max_chars4000, truncated=false.
Original AgentSkillBundle/sync_skills installed one declared skill containing
13 files into an isolated disposable destination, verified byte equality and
second-sync unchanged. Skill-creator quick_validate returned Skill is valid.
Changed production/docs diff check passed. No full-repository audit or actual
new installed MCP/biological gain is claimed by this docs-only qualification.

Qualification01 retained a checker assertion incorrectly treating 13 resource
files as 13 skill roots. Qualification02 retained a checker path error treating
the plugin manifest as a skill-relative file. The corrected checker derives
roots/files from AgentSkillBundle; no product code or assertion contract was
weakened. All six original stdout/stderr logs are archived byte-exact in
qualification-logs.tar.gz. Scratch knowledge/managed trees are disposable once
borrower checks permit; original science journals are not disposable.

Parent subsequently reported H003 raw-channel measurement success. This is
later than the historical audit-time execution-unverified checkpoint above,
not evidence that these unpublished docs repaired a live author. Both live
author sources and skills remain untouched. Future normal bundles only.
