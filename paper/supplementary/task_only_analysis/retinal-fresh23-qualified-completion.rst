Fresh retinal repeat: admission repair with preserved pair separation
====================================================================

R0010_FRESH23_94 independently analysed the released development acquisition
using the receiving23 package, task brief and MCP on isolated display :94.
No reference answer or held-out image was opened. The author froze TECH1 on
6 October 2026 at 02:27:33 UTC, accepting useful RBPMS soma-like candidates
and mask-defined measurements while retaining weak-object and boundary flags.
The result is not an exhaustive biological count or a validated new-assay recipe.

Acquisition and method
----------------------

The single CZI contains three 2586-by-2586 uint8 physical channels: AF647/RBPMS,
AF488 of unspecified identity and Hoechst. Metadata calibration is unverified;
geometry is reported in pixels. The original and staged CZI retain SHA256
``3609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851``.
The author inspected all channels and retrieved the packaged ExampleHuman
pipeline and recipe card before choosing its method. Their integration contracts,
not DNA defaults or benchmark parity, were transferred to this retinal task.

Before FIRST, distributed measurements supported ordinary body widths around
80--120 pixels, pair separation of 75--90 pixels and internal texture of
20--30 pixels. Measured RBPMS body/background means were 41.28/20.82 for an
upper body, 27.61/20.44 for a dim body and 38.15/19.27 for the right pair.
These are regional comparators, not an independently annotated negative field.

FIRST used manual threshold 0.11, smoothing 4, shape markers and watershed,
45-pixel suppression and 40--170-pixel diameter admission. It yielded 81
instances but fragmented the central ring into three regions and incompletely
admitted weak bodies. The author diagnosed foreground support rather than
changing seeds alone. REPAIR1 changed threshold/smoothing to 0.095/10,
retaining the other segmentation settings. The central ring became one region,
the genuine right pair remained separate and bright regional controls remained.
Its 110 instances still include uncertain weak crescents and irregular patches.

TECH1 corrected original-channel photometry by explicitly setting the step-local
RBPMS binding to PIPELINE_START. REPAIR1 had measured near-zero values from
the wrong step input. No segmentation setting changed. The parent independently
read both label arrays: they are identical, SHA256
``00108b523c7010bd0e385b2729d02b4ef98ccdc621ab032bb5fe53812302eedf``.
The final complete PipelineDocument has SHA256
``990e27ddf302ea72d790b5833f520e460811a91f418e4434ec13abd40368f205``.

Endpoint evidence
-----------------

The author reports personally opening all 63 retained captures, including matched
whole-field, upper, central, right and lower raw/result/combined views. Final
RBPMS review used numeric contrast 0--63 and gamma 1. Separate matched Hoechst
views contextualised a weak-body ambiguity without treating every nucleus as
an RBPMS-positive soma. Three attempted composites were rejected because channel
translation prevented simultaneous rendering. Visibility alone was not accepted
as evidence of colocalisation. Full capture custody remains in capture-manifest.json.

Independent saved-output checks found 110 nonzero IDs and 110 CSV rows with
identical ID sets; every exported area matches its saved label pixel count.
Nine IDs touch the frame: 1, 2, 3, 5, 8, 91, 95, 97 and 110. The other 101
are nonborder algorithm candidates, not independently validated cells.
All 110 rows have nonzero within-object fluorescence variation. Mean intensities
span 0.102068--0.336206 in original uint8/255 units; integrated intensity equals
area times mean to within 2.28e-13. This establishes internal table consistency,
not per-pixel independent photometry validation or biological envelope accuracy.
Weak-class sensitivity and exact crescent/contact boundaries remain unmeasured.

Freeze and runtime disposition
------------------------------

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/R0010_FRESH23_94/author-workspace/output

Canonical payload root::

  /run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/R0010_FRESH23_94

The parent independently verified all 197 declared control files (4,476,709 bytes)
and 116 source/payload files (682,534,012 bytes): no missing or mismatched sizes
or hashes. These manifest scopes are not exclusive-storage totals. The original
MCP journal's postwriter size/hash also matched in the preceding verification.
Active author history is explicitly excluded from the author's final manifest.
All six retained compile/execution jobs completed without errors.

Typed owned shutdown receipts confirm native and viewer process exit; a parent
process check found neither retained PID alive. The actual client exit code 2
is preserved separately from successful runtime closure. No interrupted command
was replayed. The harness retained separate postwriter seals and reused the
finished display for another fresh author. This repeat supports self-directed
admission and measurement repair, not improved first-attempt reference accuracy.
