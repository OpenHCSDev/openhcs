BBBC007 fresh10 first-candidate independent review
================================================

Parent reviewed saved original MCP bitmaps and authored pipeline source only;
no reference masks, expected counts or held-out answers were opened. Current
author remains independently responsible for development. These observations
were not sent as parameter advice to the fresh author.

Original evidence root:
``/run/media/ts/hdd/openhcs-science/next-bbbc007-fresh10-96-20261005/BBBC007_FRESH10_96``.

The previously opened A01/site5 nucleus raw/result/combined set preserves
matched geometry and shows useful isolated-nucleus coverage with apparent
merges and misses in crowded groups. It is not a task-wide accuracy estimate.

Parent now opened A02/site1 cluster raw capture023443920931Z and seedcombined
capture023550451225Z. The raw shows numerous bright, touching or near-touching
bodies against diffuse background. The sparse red seed-maxima marks do not
provide an evident one-per-body correspondence across this cluster. Their
small rendered size and screenshot alone cannot establish exact marker count
or identify which subsequent stage removes particular bodies. This pair is
stage evidence, not a final-result three-view acceptance set.

The reviewed ``pipeline_first01_technical03.py`` uses DNA primary-object
shape markers, intensity watershed, manual smoothing3 and suppression7,
global Li threshold with correction0.9, size8..45 and size exclusion enabled.
ACTIN secondary objects use propagation. Primary/body support, the marker
landscape and size rejection therefore require distinct diagnosis; a plausible
crowded merge must not be assigned to watershed alone from final labels.
The author is already inspecting those intermediate stages independently.

The source uses physical DNA/ACTIN bindings with explicit monochrome loading
and a well/site source-set metadata join. This review found no evidence of the
earlier personal-neurite channel-swap concern in these bindings. Numerical
completion, counts, full16-field coverage and true cell boundaries remain
separate claims requiring their own current evidence.
