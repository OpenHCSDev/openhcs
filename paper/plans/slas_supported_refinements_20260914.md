# Supported accessibility refinements and essential-request receipts

Date: 2026-09-14. Audience: a biology PI with little software-engineering background,
while preserving the technical evidence needed by SLAS Technology readers.

## Outcome

Applied targeted explanations and visual refinements using the papers repository's
style-guide pass. Scientific counts, benchmark conditions, abstract, Discussion
and conclusion remain unchanged. No experiments were rerun. This pass does not
replace the historical OpenHCS 0.8.5 comparison evidence with newer CI results.

- [Revised PDF](../review/slas-accessibility-supported-20260914/manuscript.pdf)
- [Revised DOCX](../review/slas-accessibility-supported-20260914/manuscript.docx)
- [Editable manuscript](../openhcs_nature_methods_draft.md)
- [Frozen panel input](../review/slas-accessibility-focused-20260914/manuscript.pdf)
- [Incoming-note audit](../review/slas-accessibility-focused-20260914/panel/reading_trajectory.md)
- Original reports: [A](../review/slas-accessibility-focused-20260914/panel/reviewer_a.md),
  [B](../review/slas-accessibility-focused-20260914/panel/reviewer_b.md),
  [C](../review/slas-accessibility-focused-20260914/panel/reviewer_c.md).

Page numbers below refer to the frozen panel PDF; the revised PDF retains the same
25-page layout. These are three model-reader reports, not independent human-user
testing or journal decisions.

## Implemented refinement ledger

| Location | Reader's first recoverable claim | Unresolved entry state | Pointer load | Missing or weakened landing | Smallest repair | Audience encountering friction |
| --- | --- | --- | --- | --- | --- | --- |
| p5, workflow sources | Images can be stacked and grouped | A processing group lacks a concrete instance | Supplementary Figure 1 | How grouping changes an analysis | Added nuclear versus neuronal channels using different function chains; kept grouping separate from Z stacking | Biology PI |
| p10, performance Methods | The runs measure scaling | Meaning of repeated wells versus experimental samples | Table 2 and historical harness | What was actually repeated | Same source images assigned to multiple well identifiers, creating repeated analysis work | Biology PI |
| p13, agent errors | Agent recovered from errors | One failed call versus 30 error responses | Supplementary Data 4 and original trace | Plain distinction between the two counts | One request rejected for an invalid operation name; 30 others returned an error from the requested operation | Non-software reader |
| p15, image comparisons | Two image comparisons passed | Nearest antecedent of "these" is the five without references | Previous paragraph | Which set contains the two examples | Replaced with "two of the 25 compared workflows" | All readers |
| p17, performance Results | More workers raise median throughput; RAM differs by workflow | Practical relationship is implicit | Figure 5 and Methods | One positive interpretation | Added that more workers increased median throughput while memory requirements varied substantially between workflows; shortened repeated setup wording | Broad technical reader |
| p4, Figure 1 | Four entry routes share one pipeline | Secondary labels are small/pale | Caption | Readable relationships at article size | Enlarged/darkened labels, split the long settings label, and separated processor labels from the section heading and icon pins | All readers |
| p14, Figure 3 | Outlines link to measured paths | Native table headers are difficult to read | Full-frame context and caption | Readable measured rows | Enlarged a smaller original-pixel selection: three rows, neuron labels and two distance columns; updated box, title, caption and crop receipt | All readers |

## All eight requests labelled essential

Understanding after rereading does not make a clarification unnecessary. The
question is whether the notes show a concrete reading obstacle, an optional
improvement, or only a possible misreading by an imagined future reader.

### A1. Locate the crossover error in Figure 3

- **Final request:** add an arrow, circle or inset so the reader can locate the
  crossover discussed on p13. A calls this a moderate essential repair.
- **What A already understood, p13:** "That makes “reviewable” concrete and
  prevents the example from implying autonomous biological correctness."
- **Actual remaining difficulty, p14:** A cannot identify the particular error
  from the unmarked original outlines. That is a real visual limitation, distinct
  from failing to understand why scientific review matters.
- **Decision:** no invented marker. The retained correction record does not locate
  the corrected crossover with image coordinates. The figure continues to identify
  the original pre-correction result, and Results retains the later correction
  and changed path/branch counts. A localized annotation remains possible if its
  correspondence to the documented correction can be established.

### A2. Repeat the 30/25/two comparison denominators

- **Final request:** add a compact summary of 30/30 executions, 25/25 selected
  reference comparisons and two image-comparison workflows near the result.
- **What A already understood, p15:** "I now have an easy numerical summary:
  30/30 executed; 25 had retained native values and all 25 passed selected
  comparisons; five had no file-export modules and therefore no value comparison.
  Only two workflows had image comparisons."
- **Existing passage:** the first Results paragraph already states successful
  execution of all 30, the 21 CSV / three SQLite / one illumination-array split,
  all 25 selected comparisons passing, and why five lacked value comparisons.
  The next paragraph names the two image-comparison workflows.
- **Decision:** no extra denominator summary. Retained the existing counts and
  "selected" scope; fixed the demonstrable pronoun ambiguity identified by B2.
  A's final request is stronger than the observed comprehension problem.

### A3. Warn that corpus medians do not predict an individual assay

- **Final request:** explicitly say the median describes the heterogeneous
  30-workflow corpus and is not a prediction for a particular assay.
- **What A already understood, p17:** "I infer rather than being explicitly told
  here that medians aggregate one value from each of 30 heterogeneous workflows,
  so they describe the corpus, not a typical assay prediction."
- **Existing passage:** throughput is explicitly "median throughput across
  workflows"; the memory paragraph begins "Across all 30 OpenHCS workflows";
  Methods states one recorded run per workflow and condition. Figure 5 identifies
  individual workflow lines and the median across 30 workflows.
- **Decision:** preserve those positive definitions rather than add another
  negative prediction warning. The short performance interpretation added for C2
  remains limited to "these runs."

### B1. Explain one rejected request versus 30 operation errors

- **Final request:** clarify "one failed at the tool-call level" versus
  "30 completed responses reported operation errors."
- **Earlier note, p13:** B initially stumbles over precisely this distinction,
  then recovers the idea of calls that return errors. Eventual recovery still
  leaves a concrete, avoidable reading cost.
- **Source check:** the original trace's failed `item_92` called
  `openhcs_ui_selected_plate_workflow` with `workflow="init"`; validation expected
  an allowed operation such as `init_plate`. This was not a transport failure.
- **Applied wording:** "Of 140 attempted MCP calls, one was rejected for an invalid
  operation name; 30 others returned an error from the requested operation."
  The existing error categories and recovery sequence follow it.
- **Decision:** supported clarification, implemented without inventing a network
  explanation or converting the count into 31 failed analyses.

### B2. Resolve the antecedent of "two of these workflows"

- **Final request:** name the set containing the two successful image comparisons.
- **Earlier note, p15:** B notices that "the other five" is the nearest antecedent,
  then infers the intended set from the named examples. This is an actual ambiguity
  even though the reader repairs it correctly.
- **Applied wording:** "Image comparisons passed for two of the 25 compared
  workflows: the illumination-array example and the translocation example..."
- **Decision:** supported direct correction. Counts and comparison coverage did
  not change.

### B3. Distinguish repeated workloads from biological replicates

- **Final request:** explain what repeated images and wells mean in these runs.
- **Earlier notes, pp10-11 and final account:** B understands the experiment as a
  systems test but keeps asking whether wells identify actual samples or assigned
  workload. The question recurs rather than disappearing after Table 2.
- **Source check:** at historical benchmark commit
  `f58bca4e9452b9c983924b69ef5deae416c73c50`,
  `benchmark/well_throughput_scaling.py` calls
  `expand_source_schema_workspace_wells`. Its owner in
  `openhcs/core/source_schema_workspace.py` maps additional well identifiers to
  the same source paths. It replicates assignments, not source image files.
- **Applied wording:** "Separate runs measured throughput and peak memory by
  assigning the same source images to multiple well identifiers, creating repeated
  analysis work (Table 2)."
- **Decision:** supported clarification. This explains the positive construction
  without adding a repeated warning about biological validity.

### C1. Prevent 25/30 in the abstract from being read as five failures

- **Final request:** add that the five lack retained exported reference values,
  so a quick reader will not infer five failures or exhaustive output comparisons.
- **What C actually wrote on p1:** "I read it as 25 assessable comparisons, not
  five failures."
- **Later confirmation, p15:** C calls the existing Results paragraph "the clearest
  account of 30/25/5" and correctly restates both selected comparisons and the two
  image-comparison workflows.
- **Existing abstract:** "Automated testing of OpenHCS 0.8.5 executed all 30 imported
  CellProfiler workflows; 25 had retained CellProfiler-produced reference outputs
  and passed their selected measurement or image comparisons."
- **Decision:** abstract unchanged. The suggested mistake did not occur in C's
  reading, and the sentence already names both execution and selected comparison.
  Detailed reasons for unavailable references remain in Results.

### C2. State the practical meaning of the performance plots

- **Final request:** translate worker and queue findings into a plain practical
  consequence, including workflow-specific memory demands.
- **What C already understood, p17:** "I infer the practical message is to tune
  concurrency to hardware capacity; that is not stated explicitly."
  C also explicitly declines to infer per-assay performance from the heterogeneous
  medians and single observations.
- **Applied wording:** "In these runs, more workers increased median throughput,
  while memory requirements varied substantially between workflows."
- **Decision:** useful explanatory landing, implemented as optional polish rather
  than treatment of a false interpretation. It summarizes observed behavior
  without claiming a tested optimal setting or extending the hardware scope.

## Interpretation

All three readers recovered the paper's central argument without the supplement.
The strongest essential requests were B's three local repairs. A1 identifies a
genuine visual gap but does not justify an unsupported annotation. A2, A3 and C1
seek additional protection against interpretations their own notes did not make.
C2 provides a useful explicit conclusion from results already understood.

This supports a small refinement pass, not a restructuring around defensive
qualifications. The package table, concrete editing round trip, scientific-review
example, comparison counts and measured performance remain intact.

## Verification

- Rebuilt with `paper/build_docx_from_markdown.py` and headless LibreOffice in an
  isolated temporary profile. The final PDF has 25 pages, six figures and two tables.
- Visually checked pp4, 5, 10, 12-15, 17-18, 20 and 25, including changed prose,
  both adjusted figures, caption placement, the performance table, conclusion and
  final reference page. Adjusted Figure 1's section heading and support note after
  inspecting their spacing in the first build.
- Extracted PDF text matches the frozen input on every unchanged page. The
  abstract, Discussion/conclusion and references remain unchanged.
- Verified all six DOCX figure payloads match the current generated PNGs. Figure 2
  and Figure 6 PNGs are unchanged by the generator's provenance refresh.
- Verified generator, input and output hashes in the refreshed Figure 1/2/3/6
  provenance records. Figure 3 retains the original source TIFFs, recorded frame
  and crop coordinates; no measurement values or image evidence were redrawn.
- Source and report whitespace checks passed. Frozen panel input and supplementary
  PDFs retain their original hashes. Temporary render/profile files were removed
  after inspection; the revised PDF and DOCX remain at the links above.

Final PDF SHA256:
`0269e4656940fc6fdff0b567acea9ab1a2be90f29eeb4662bdd76d8318639b82`

Final DOCX SHA256:
`2c7ae4680e26f4fbe40c5386558305577ca52ebfbe46d0d3530da8c42e39a04a`

Frozen panel PDF SHA256:
`f0b06b17016086e1c9b87e1aec74a6cd10310416a5174e98a8a103498baaea6e`

Unchanged supplementary PDF SHA256:
`94ba2fec7108e7c97a6cbbf65baf85fb2b5528a3f27e0e8d2c57487c8e013b24`
