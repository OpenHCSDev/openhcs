# SLAS accessibility revision: implementation and verification

## Editorial contract

Audience: an experienced biology PI with little software or AI-integration
background, while retaining the mechanism and evidence needed by SLAS Technology
readers. The revision follows the papers repository's `paper-style-guide-pass`
skill and canonical writing style guide: establish the scientific action before
its implementation vocabulary, resolve terms at first use, and place the
supporting figure where the reader needs it. No scientific analyses were rerun.

Papers-repository revision consulted:
`271a2f23a9121f2c0ea66443843833a02997ec90`. This records the guide version without
copying its instructions into the OpenHCS repository.

The [approved 20-item plan](slas_accessibility_edit_plan_20260914.md) specifies
the changes and their rationale. This ledger records their implementation.
The frozen release evidence remains **30 executions, 25 selected-value cases,
two image-selected cases** for OpenHCS 0.8.5. New reference-export/CI work remains
separate. Function declarations, configured workflows and MCP operation
declarations retain their distinct responsibilities. Worker reuse is within
each run, not an assertion of a persistent worker pool across runs.

## Edit ledger

### Reader-entry checks

| Location | Reader's first recoverable claim | Unresolved entry state | Pointer load | Missing or weakened landing | Smallest repair | Audience encountering friction |
| --- | --- | --- | --- | --- | --- | --- |
| Abstract | An agent-built analysis remains editable by a scientist. | Meaning of MCP and the relationship between functions and controls. | No external lookup should be needed. | What the scientist can actually change. | Lead with shared editing, then explain the parameter mechanism. | broad |
| Introduction | Analysis choices change after inspecting images. | Why a shared definition connects the interfaces. | Tool citations precede the explanation; the overview was far away. | The concrete OpenHCS answer. | Move the mechanism earlier and place Figure 1 before Methods. | broad |
| Workflow Methods | A pipeline turns selected images into linked measurements. | Stack, processing group, override and compilation. | Supplementary Figures 1/3 provide detail but should not supply the basic meaning. | An imaginable sequence of scientific actions. | Use a nuclear-channel example and explain terms as actions. | broad |
| Library table | Reusable software supplies the mechanisms. | What registry, introspection and reactive controls actually do. | Eight package links, with no need to follow them for the argument. | Why separate libraries belong in this paper. | Keep the table; introduce reuse and describe each role with an action. | broad |
| Comparison Methods | Imported analyses are checked against CellProfiler-produced results. | Execution success versus numerical comparison and image selection. | One supplementary evidence pointer plus file-format names. | Which outputs support the result. | Put 30/25 scope before selection mechanics; retain the precise image rule. | both |
| Agent Results | An agent builds and checks a workflow. | Operation errors versus failed analyses; original versus later corrected output. | Figure 3 and Supplementary Data 4. | What the subsequent scientist review contributed. | Classify errors briefly and state the recorded correction sequence. | both |
| Performance | More workers process repeated inputs concurrently. | Meaning of wells, queue depth, execution interval and log scale. | Figure 5 plus the separately scoped historical projection. | What the rate means for the measured workload. | Define assignments and reuse the term in prose and axes. | both |
| Discussion/conclusion | The scientist can reuse and revise the workflow. | Little new state; main risk is repeating the same interface claim. | Table 1 is a reuse pointer, not required to understand the conclusion. | The graphical revision route for nonprogrammers. | Consolidate duplication and name graphical controls alongside Python. | broad |

### Approved changes

| Items | Location and initial reader burden | Repair and landing | Status |
| --- | --- | --- | --- |
| 1 | Abstract introduced implementation before the scientist's action. | Lead with scientists and agents editing the same analysis; explain MCP and how function information supplies controls/catalog descriptions. Execution also uses the configured workflow and selected images. | Implemented |
| 2 | Introduction deferred the OpenHCS mechanism until after the tool survey. | Move the shared-workflow paragraph before the extended survey; cite Figure 1 there. Preserve the related-work citations. | Implemented |
| 3-4 | Methods required the reader to connect signatures, source mappings, groups, compilation and workers unaided. | Follow a nuclear-channel, segmentation, measurement and inspection example. Define each operation in place, including shared defaults and overrides. Retain configurable stacks/grouping and source identity separate from storage. | Implemented |
| 5 | Table 1 assumed software vocabulary before explaining why the packages matter. | Keep all eight libraries in the main text; introduce their reusable purpose and rewrite roles as actions: discover, read, track, generate, convert, route and coordinate. | Implemented |
| 6 | Deployment read as a transport inventory. | Describe desktop and headless operations first, then communication and access controls; retain restricted hosted scope and separate processing-function discovery. | Implemented |
| 7 | Reference-selection formats arrived before the comparison denominator. | State execution versus value-comparison scope before CI packaging and file-selection details. Preserve CSV, SQLite/CPA, NPY and image-selection distinctions. | Implemented |
| 8 | Complex-workflow counts preceded their biological purpose. | Lead with multi-channel organelle analysis and volumetric segmentation, then exact module/step/call counts. Remove an adjacent repetitive operation inventory. | Implemented |
| 9-10 | Agent inspection, later scientist review and operation errors could be conflated. | Name agent output checks, give brief error categories, and identify the later correction as a registered graph-extraction change in 0.7.14. Keep the original counts and timing separate. Describe disabled client safeguards without inventing a motive or security result. | Implemented |
| 11 | Later performance labels could make repeated inputs sound like biological replicates. | Define image assignments scheduled as wells, queue depth and execution-only throughput; use assignment terminology in Results, plot labels and supplement. | Implemented |
| 12 | Discussion repeated the same interface/reuse claim and stranded the conclusion. | Remove overlapping sentences, retain the laboratory reuse example and concise conclusion, and explicitly include graphical controls as a revision route. | Implemented |
| 13 | Figures were collected after Discussion; automatic alt-text captions duplicated explicit captions. | Move the same six figure blocks into the canonical manuscript near their passages. Disable Pandoc implicit captions while retaining image alternative text. Keep each figure with its substantive caption through the existing DOCX builder. | Implemented |
| 14 | Figure 1 arrows and processor choices needed interpretation. | Label edit/import arrows, name the image input and place the function-dependent CPU/GPU qualification beside the processor symbols. | Implemented |
| 15 | The Figure 2 full window could not establish small step/status details alone. | Retain the full window and add real crops of its two steps and connected status, alongside the same-session control/code details. | Implemented |
| 16 | Figure 3 function boxes could resemble processed-image panels; the crossover and units needed evidence checks. | Label Step 1 and Step 2, preserve original pixels, and explain the unestablished physical calibration beside the native table. The retained record identifies the correction but supplies no image coordinates for the crossover; no guessed arrow or corrected inset was added. | Implemented with the plan's evidence-dependent annotation omitted |
| 17 | Figure 4 exposed exact code identifiers without explaining their roles. | Add image/settings and processing-function labels; identify export after all groups. Preserve exact function names, repetitions and object relationships. | Implemented |
| 18 | Figure 5 needed visible scale/units and stronger individual traces. | Label repeated assignments and logarithmic throughput, increase trace contrast, and wrap the long axis label after detecting clipping in the first render. All plotted numerical observations remain unchanged. | Implemented |
| 19 | Figure 6 asked the reader to find small list and coordinate details. | Retain full Fiji/napari captures and add verified crops of the ROI list/outline, selected napari object/list row and channel/Z display. Keep the two demonstrations distinct. | Implemented |
| 20 | Supplement vocabulary needed to match the main performance explanation. | Define repeated assignments versus biological replicates, retain the serial projection formula and update the figure-regeneration provenance description. Exact saved identifiers and the quoted agent prompt remain unchanged. | Implemented |

## Evidence-dependent decisions

- The original agent record's `post_qa_corrected_recapture` identifies a
  clustered crossover, a registered neurite graph-extraction fix, OpenHCS 0.7.14
  and the changed counts. It does not locate the crossing within the image.
- Figure 3 preserves native `_um` column names. Neither the retained run record
  nor the saved pipeline establishes a physical calibration for this display.
- Figure 4 was regenerated using the current importer. Its module sequence,
  setup modules, function identities and parameters match the pre-revision
  receipt. The regenerated Python AST also equals the committed document's AST;
  the text diff is formatting. Its receipt records the current source hashes,
  rather than claiming the generator ran from an untouched 0.8.5 checkout.
- Figure 6's Fiji outline crop is an example of an outlined nucleus, not a claim
  that a particular Fiji list row was selected. The napari capture visibly
  contains the highlighted object and ROI-0021 row.

## Verification

Completed before freezing the review input:

- All four main-figure generators completed successfully. They checked the
  relevant source images/video and source records and refreshed output receipts.
- All six PNG files embedded in the manuscript DOCX match the current generated
  image SHA256 values. All six image alternative descriptions remain present.
- The generated CellProfiler Python has the same parsed syntax tree as the
  committed document. The retained module/function/parameter mapping is unchanged.
- No May 13 benchmark input tables or plotted numerical CSV observations changed.
- Main and supplement build through the existing Pandoc/DOCX path and convert
  with LibreOffice. The main remains 25 pages; the supplement remains 16 pages.
- Parent inspected rendered main pages 4, 7, 12, 14, 16, 18, 19 and 20, including
  every main figure, Table 1 and the conclusion. Figure 1 is now on page 4,
  before Methods. The entire Discussion and conclusion fit together on page 20.
  Figures and their substantive captions stay together; repeated italic image
  descriptions no longer appear. The final Figure 5 axis label is fully visible.
- Generated Matplotlib SVG paths contain upstream serializer whitespace;
  source-text whitespace checks are assessed separately from generated artwork.

Build commands, from the OpenHCS repository:

```sh
.venv/bin/python paper/figures/build_slas_visual_story.py
.venv/bin/python paper/figures/build_slas_agent.py
.venv/bin/python paper/figures/build_slas_cellprofiler.py
.venv/bin/python paper/figures/build_slas_benchmark.py
.venv/bin/python paper/build_docx_from_markdown.py paper/openhcs_nature_methods_draft.md paper/review/slas-accessibility-revision-20260914/input/manuscript.docx
.venv/bin/python paper/build_docx_from_markdown.py paper/supplementary/README.md paper/review/slas-accessibility-revision-20260914/input/supplement.docx
```

## Fixed follow-up panel

[Assignment and inputs](../review/slas-accessibility-revision-20260914/assignment.md).
Reviewers receive the same editorial-accessibility remit as the earlier panel,
fresh contexts and no previous feedback. This is a simulated reader review,
not a journal decision or a test with the author's actual PI.

- Main PDF: 25 pages; SHA256
  `2d27f020373f2181a130dadb3380a92d2d5e21285d80d6b53cae33babaa71bde`.
- Supplement PDF: 16 pages; SHA256
  `50530ef8fbf21a9c76d3122c23b50cdcfa3d35023d4bbad93659488dd687eb8f`.
- Panel reports and synthesis are saved beside the assignment. The PDF inputs
  are frozen while reviewers read them; any later revision receives a new copy.

All three fresh Sol reviewers completed their reports: 25 ordered reactions
each, 75 total, with final syntheses and supplementary checks. The parent read
their complete reports and recorded source-checked dispositions in the
[combined assessment](../review/slas-accessibility-revision-20260914/summary.md).

Author-list order, complete affiliations, funding, contributions and conflict
declarations still require the author's confirmation. No publication or
scientific-evidence upgrade is implied by this editorial pass.

## Final author copy after local follow-up

The panel input PDFs above remain byte-for-byte unchanged. A separate
[author reading copy](../review/slas-accessibility-revision-20260914/author-copy/manuscript.pdf)
finishes four small clarity repairs identified during the read:

1. The Introduction explains preparation before naming compilation.
2. Figure 1 explicitly labels its image input, function input and workflow-to-
   compilation paths. None is labelled as an unsupported feedback loop.
3. The empty sentence about profiles providing their respective operation sets
   is removed; the substantive desktop, headless and hosted distinctions remain.
4. Results names the illumination-array and translocation image comparisons,
   showing that the latter overlaps the SQLite category without adding another
   repeated count matrix.

The three page-by-page reports apply to the frozen panel PDFs, not to these
four subsequent refinements. No extra blind panel was run on the author copy.
The parent checked the changes and downstream layout; main/supplement page
counts remain 25/16, all six embedded figure PNGs match their generated files,
and a complete PDF-text comparison shows only the three intended prose edits.
All scientific values and reference-comparison counts are unchanged.

- Final main SHA256:
  `8b55d891e58503aa7f4dee7ae88f412e9b138638f9105b5b2442204e0bee0d48`.
- Final supplement SHA256:
  `94ba2fec7108e7c97a6cbbf65baf85fb2b5528a3f27e0e8d2c57487c8e013b24`.
