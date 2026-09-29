# How to promote a blinded analysis recipe

Use this guide when a pipeline trial might become reusable guidance, not for
routine function discovery. A successful OpenHCS compile or run is not a
biological validation. This is a *how-to guide* for an analyst making a
promotion decision; the current `image_analysis_workflow` and `viewer_review`
authoring contexts remain the operating authority for image inspection.

## Develop, review and validate a candidate

1. Define the development and untouched validation reserve before tuning.
   Keep treatment labels and scoring references hidden. Inventory source
   carrier/channel semantics through authorised metadata only; do not open
   held-out pixels to decide parameters. If there is no untouched reserve,
   report development-only evidence; do not label this new adaptation as
   held-out validated. This does not downgrade parity evidence for the
   original benchmark scope.
2. Start with the closest validated OpenHCS/CellProfiler benchmark pipeline,
   especially the Official30 corpus, before authoring. Search the
   knowledge base for the biological task and retrieve the exact relevant
   `OpenHCS Python` section. Confirm candidate functions and
   their parameters through the live registry. Record the document/section ID,
   function import path, native reference, case-specific parity evidence,
   version or commit, and evidence tier used. Benchmark parity is validated
   evidence for its tested reference scope, not biological acceptance for a
   different assay. Import or execution success alone is a narrower tier.
   The `openhcs_official30_examplehuman_nuclei_recipe_card` knowledge document
   shows how to retain a specific parity receipt and settings while separating
   inferred transfer risks from observed failures and marking new-assay QA
   unassessed. It does not replace the development, freeze, or held-out gates.
3. In the development set, keep one trial record per semantic change: complete
   pipeline source and SHA-256, parameter snapshot and SHA-256, source-manifest
   SHA-256, compile and execution receipt IDs, and typed result-artifact ID.
   Record required input layout, channel identities, stain targets, and exact
   settings. Preserve known failures with the error type, failing stage,
   source/parameter identity, diagnostic change, and outcome. Do not turn an
   execution-only success into a known-good biological recipe.
4. Review spatially distributed fields at native coordinates. Follow the
   [viewer QA procedure](viewer-qa.md) and retain matched raw-only, result-only
   and raw-plus-result views with channel identity, numeric display limits,
   Z/time, source identity and the result artifact. Verify viewer state and
   recapture the set if the user changes the canvas or presentation.
   Retrieve `openhcs_biological_image_analysis_evidence` for the cited
   display, segmentation, measurement, and reporting boundaries.
   Inspect the bitmaps yourself and record supported positives, plausible
   misses, splits/merges, and an explicit accept/reject/ambiguous judgement
   against stated biological criteria. Escalate ambiguous objects to a domain
   reviewer. Counts, overlap scores, and visually attractive preprocessing
   alone cannot pass this gate.
5. Freeze the accepted pipeline, parameters, source layout contract, and
   acceptance criteria in a dated receipt before releasing the validation
   reserve. Run the frozen candidate on the reserve once, without tuning on
   its outcome. Compare with the same biological criteria. Any subsequent
   change creates a new development candidate and needs a new untouched
   reserve; never relabel a consulted field as held-out.
6. For a metadata consistency check, construct `RecipePromotionEvidence` from
   the retained receipts and run
   `openhcs.agent.blind_recipe_audit.audit_recipe_promotion(evidence)`. Resolve
   every returned issue before promotion. An empty issue tuple means the
   *claims are internally coherent*, not that files exist, timestamps are
   genuine, blinding held, or biology is correct. Independently verify those
   facts and have the assay expert approve the result.

The audit accepts identifiers and hashes, not images; it does not read disk,
contact MCP, or open the UI. Keep raw-image and held-out access governed by
OpenHCS path policy and the study protocol. Store only opaque identifiers in
shareable recipe/error guidance; do not publish private field labels, source
paths, or held-out outcomes in a general knowledge base.

## Why these gates exist

[Agentic-J, Sections 2.2.2, 2.3, and 3.3](https://arxiv.org/pdf/2606.02080)
reports a multi-step microscopy workflow whose positive-class sensitivity was
only 50% despite a plausible aggregate result, a read-only post-project QA
checklist, curated knowledge retrieval, and recipe/error stores for prior runs.
Those are paper observations, not proof that this OpenHCS gate improves accuracy.
The staged freeze, same-coordinate witness, source/parameter digests, and
biological promotion rule are our conservative transfer to blinded OpenHCS
workflows. The gate intentionally does not reproduce Agentic-J's agents,
database, or publication checklist.
