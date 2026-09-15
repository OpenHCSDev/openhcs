# OpenHCS SLAS manuscript: proposed accessibility edits

Status: approved by the author and implemented. See the
[implementation and verification ledger](slas_accessibility_implementation_20260914.md).
The intended reader is a biology PI with microscopy and
experimental expertise, but little software-engineering background. Preserve
the technical contribution for SLAS Technology readers.

Basis: three fresh Sol page-by-page reviews of the 25-page manuscript, followed
by parent checks of their suggestions against the text, figures and retained
agent evidence. See the [panel synthesis](../review/slas-accessibility-20260914/summary.md)
and [reviewed PDF](../review/slas-accessibility-20260914/input/manuscript.pdf).
PDF SHA256: `b91067cdc6710896116dd020c0870be3ac6c0674faa0f38a59a0fbe7081f2af7`.
Page numbers below refer to that fixed PDF, not to a future reflowed copy.

## Editorial contract

Make the reader perform less translation without making the system less
specific. Teach what happens, explain why it matters, then introduce its exact
technical name. Retain concrete examples, technical identifiers where they are
evidence, and the distinction between a supported capability and a tested result.
Prefer moving or replacing existing sentences to adding explanations everywhere.

The shared-workflow mechanism remains central. Function declarations supply
parameter information and catalog descriptions; the configured workflow and
image inputs also determine execution. MCP operation declarations are distinct
from processing-function declarations. New registered functions are discovered
through generic operations, not automatically exposed as one MCP tool per
function. The prose must retain these distinctions.

## Complete proposed change list

### 1. Reorder the abstract around the shared editable analysis

**Where:** Abstract, page 1.

**Change:** Put the scientist and agent working on the same editable pipeline
before the sentence about registered processing functions. Then explain how
parameter definitions supply controls, Python representations and searchable
function descriptions, and how pre-run preparation checks the configured steps
against the selected images. Retain the current evidence and closing benefit;
do not put all implementation terms in the opening sentence.

**Why:** All three readers understood the benefit but had to decode the
mechanism before reaching it. Reordering supplies a concrete object to which
the technical explanation can attach.

**Keep:** Declaration-derived information, configured workflow/input resolution,
scientist editability, selected-value comparison scope and the single detailed-
prompt agent demonstration. A signature alone does not determine a whole run.

### 2. Introduce the OpenHCS answer before the extended tool survey

**Where:** Introduction, pages 2–3.

**Change:** Preserve the opening account of iterative microscopy analysis.
Move the complete shared-workflow explanation ahead of the longer related-tool
inventory. Keep the literature grouped by the roles it already identifies:
analysis/viewing, data access, workflows and agent assistance.

**Why:** The current survey interrupts the problem-to-solution connection.
Readers should know what OpenHCS contributes before locating it among adjacent
systems.

**Keep:** Relevant citations and accurate descriptions of other tools. Do not
invent a claim that no competing system supports a particular capability.

### 3. Explain essential technical terms at first use

**Where:** Abstract and first relevant Methods paragraphs, pages 1–6.

**Change:** Use brief functional explanations in place, rather than adding a
separate glossary that readers must consult:

| Term | Intended explanation |
|---|---|
| MCP | A protocol through which an AI client requests defined OpenHCS operations. |
| Function signature | The function's declared parameters, types and defaults. |
| Compilation | Pre-run preparation that resolves selected images, connects step inputs/results and checks requirements. |
| Source mapping | Assigning acquired images to named inputs and coordinates such as channel, site and Z plane. |
| Processing group | The selected images processed together for an operation; use a verified concrete example, not a universal equation with a well. |
| Inherited default / override | A shared setting used by a step unless that step supplies its own value. |
| Worker / queue depth | An execution unit handling assigned samples, and how much work is assigned to it; distinguish processes from the available thread mode. |
| Native reference output | A retained result produced by CellProfiler, not an original/raw microscopy image. |
| Side effects / configured roots | Changes an operation can make / the permitted filesystem locations. |

**Why:** Expanding an acronym or replacing it with another technical noun does
not explain its role. The panel identified these as recurring translation costs.

**Keep:** The exact terms after their first explanation. Do not replace them
with vague words such as “automation” or “integration.” SWC already has a
neuron-morphology gloss; elaborate only if needed in the final sentence context.

### 4. Give Methods a specimen-to-result thread

**Where:** Workflow definition, image sources and intermediate results, pages 3–5.

**Change:** Introduce a short illustrative sequence using operations already
described in the paper: select a nuclear channel, segment nuclei, pass the named
labels to a measurement step, and inspect/save the linked results. Organize the
surrounding explanations around input identity, step connections, execution and
inspection. Introduce format/backend inventories after these actions.

**Why:** Readers currently encounter many supported routes at the same level.
A concrete sequence makes the relationships intelligible without deleting any
capability or pretending the illustration is an additional experiment.

**Keep:** Acquisition coordinates versus file locations; configurable grouping
and stacks; 2D/3D function dependence; array conversions; independent saving and
viewing; named-result provenance; experimental/read-only support boundaries.

### 5. Keep the library table, but make its purpose and entries readable

**Where:** Reusable workflow infrastructure and Table 1, pages 5–6.

**Change:** Explain first that these packages implement reusable mechanisms
which OpenHCS combines with its microscopy functions and configurations.
Replace opaque descriptions such as “declared implementation families” with
accurate descriptions of what is discovered, generated, tracked or transported.
Keep the eight package names and links in the main table.

**Why:** The reviewers found the table hard to enter, not technically invalid.
Moving it out solely because it is software-oriented would weaken the reusable-
infrastructure contribution. Explain its relevance instead.

**Keep:** Separate package responsibilities and their real declaration owners.
Do not imply that a second complete domain application has been demonstrated.

### 6. Organize deployment details by what each mode permits

**Where:** Agent access through MCP, page 5.

**Change:** Lead with the operational distinction between editing a live
desktop session, running without the GUI and using the restricted hosted
service. Follow with the transport and access-control details. Keep the
operation-definition paragraph distinct from function discovery.

**Why:** “stdio,” “headless,” “HTTP,” bridges and roots currently arrive as an
inventory. The reader needs to know which scientific action each configuration
enables before learning how messages travel.

**Keep:** Authentication, revision checks, allowed paths, read-only hosted scope
and the distinction between local and hosted behavior. Do not recast these as
a proved security guarantee.

### 7. State the CellProfiler comparison scope before its file-selection rule

**Where:** Comparison Methods and Results, pages 7–8 and 11.

**Change:** Identify the reference values as CellProfiler-produced results and
give the execution/value-comparison distinction before CSV, SQLite and NPY
selection details. Keep a concise result summary in Results and the precise
selection policy in Methods; avoid repeatedly adding all counts everywhere.

**Why:** Readers temporarily interpret “enabled comparisons” too broadly until
the next page supplies the denominator. Changing the order fixes that reading
without adding a defensive paragraph.

**Keep:** This frozen release result is 30 executions, 25 selected-value cases,
two image-selected cases and five execution-only cases. The image policy is
not “image-only profiles”: it excludes CSV-bearing profiles and includes a
translocation profile with SQLite output. Preserve tolerances, categorical
rules and the unselected images in 14 CSV-bearing profiles. Later benchmark
fixes must be introduced as separate dated evidence, not folded into this old
release result by changing a number.

### 8. Lead the complex-workflow examples with their biological operations

**Where:** Imported-workflow breadth and complex workflows, pages 11–12.

**Change:** Describe the advanced example's channels, organelles and linked
measurements, and the monolayer example's volumetric segmentation, before their
module/step/function-call counts. Consolidate overlap between the adjacent
assay list and operation list while retaining representative biological variety.

**Why:** Those examples are already persuasive to the primary reader. Putting
their biological content first makes the counts evidence of structural scale
rather than unexplained numbers.

**Keep:** Exact counts, named object relationships, selected-output checks and
separate code-reconstruction checks. Keep the Comet explanation and Figure 4.

### 9. Make the agent result and subsequent scientist review one clear sequence

**Where:** Agent Results, pages 10–11.

**Change:** Present the recorded sequence together: the agent constructed and
executed the workflow; checked requested outputs and viewer state; subsequent
scientist review found the crossover; a later corrected demonstration changed
the branch/path counts. Use “agent inspection” or “output checks” where “review”
could be mistaken for independent biological validation.

**Why:** The current page break separates the memorable autonomy result from
the concrete example of scientist-led refinement. Connecting them shows what
shared editability and inspectable outputs enable.

**Keep:** Exact original/later versions, counts and timing boundaries. Any
sentence naming the precise algorithmic correction must first be checked
against its retained source record. Do not imply manual edits to measurements
or that the later correction occurred during the original unattended run.

### 10. Clarify error categories and the agent-run permissions without inventing motives

**Where:** Agent Methods and Results, pages 6 and 10.

**Change:** Give one short classification of the reported errors, with the full
table remaining supplementary. Distinguish the prompt's authorized actions,
the client's bypassed approval/sandbox controls, and the tool use observed in
the trace. Retain the existing factual disclosure, phrased in ordinary language.

**Why:** Thirty operation-error responses can be mistaken for thirty failed
analyses; a prompt restriction can also be mistaken for enforced containment.
Both are avoidable interpretation errors.

**Keep:** 140 attempted calls, one tool-level failure and 30 operation-error
responses. These include discovery/query/UI issues, not only authoring errors.
Do not call them all harmless or expected. Do not invent why safeguards were
bypassed or claim the run was designed to test security.

### 11. Explain benchmark work units and timing once, then use them consistently

**Where:** Performance Methods/Results, pages 8–9 and 12.

**Change:** Define the repeated inputs as image assignments scheduled as wells
by the runtime, not distinct biological replicates. Explain worker count and
queue depth next to the experiment that varies them. Keep execution-only timing
and cross-workflow summary language consistent with Figure 5.

**Why:** A biology reader naturally interprets “wells” as independent assay
samples. The current text defines repetition but later reverts to shorter labels
that can lose that meaning.

**Keep:** Actual scheduling semantics, all numerical results, one recorded run
per workflow-condition, within-run worker reuse, CPU/source scope, output-saving/
record/pruning policy, individual workflow variation and maximum RAM. Do not
relabel the measurements as end-to-end throughput or a matched CellProfiler
speed comparison.

### 12. Consolidate Discussion repetition while keeping the short conclusion

**Where:** Discussion and concluding paragraph, pages 13–14.

**Change:** Preserve the practical “import, remap, adjust, inspect, rerun”
scenario. Combine the adjacent overlapping statements about shared workflows
and familiar viewers where they add no new connection. Keep the brief closing
paragraph; make the graphical editor an explicit scientist revision route
rather than assuming Python is familiar to every reader.

**Why:** This is already the most accessible section. A small consolidation
improves momentum without turning the conclusion into another abstract.

**Keep:** The mechanism, reusable infrastructure and each evaluation's meaning.
Do not add another complete validation-count list or generic limitations block.

### 13. Produce a PI-friendly reading layout from the same manuscript source

**Where:** Figure placement, metadata and caption layout throughout.

**Change:** Place Figure 1 near the first substantial mechanism explanation;
place the other figures close to their relevant passages where layout permits.
Fix the closing paragraph stranded on page 14 after metadata was added. Remove
redundant italic image-description lines from the visible figure presentation,
while preserving useful alternative text and full substantive captions.

**Why:** Readers currently carry verbal architecture for many pages before
seeing its clearest diagram. The nearly blank conclusion page and repeated
caption leads add reading friction without adding content.

**Keep:** One canonical manuscript and existing build machinery, rather than
maintaining a separately edited PI version. Preserve the frozen review copies.
Do not shrink text or add conclusion prose to solve pagination. The six main
figures and one table remain the same evidence set.

### 14. Give Figure 1's arrows and execution options plain labels

**Where:** Figure 1, reviewed page 15.

**Change:** Label edit versus import routes directly where useful; identify the
image/function connections without introducing a new color taxonomy. Put the
function-dependent CPU/GPU qualification close to the corresponding symbols.

**Why:** The figure is the strongest overview, but some readers interpret its
bent input paths as feedback loops or assume all functions can use either
processor. Short labels resolve those readings.

**Keep:** The shared pipeline, asymmetric CellProfiler import arrow, compilation,
within-run worker lifetime, experimental OMERO label and inspectable results.

### 15. Strengthen Figure 2's readable evidence without losing the main UI

**Where:** Figure 2, reviewed page 16.

**Change:** Retain the full main-window context and the existing readable
code/control details. Improve the relative sizing or add a focused callout for
the two pipeline steps and connection status if the caption continues to ask
readers to identify them. Remove only visual clutter unrelated to those claims.

**Why:** The full screenshot establishes the real application, while the
enlargements establish the parameter match. Neither should be asked to serve
the other's role at an unreadable scale.

**Keep:** Exact 99.8/99.6 values, parameter order, genuine same-session captures
and the recorded round trip. No replacement with a synthetic interface.

### 16. Make Figure 3's workflow and review meaning visible

**Where:** Figure 3, reviewed page 17.

**Change:** Label the two function-name boxes as analysis steps so they cannot
look like processed-image panels. After checking the exact original/corrected
records, mark the relevant crossover if it is visible in the retained image.
Consider a small corrected inset only if it adds an intelligible comparison
without crowding the figure. Clarify the interpretation of `_um` columns next
to the table only to the extent the calibration record supports.

**Why:** This is the most direct biological illustration of why an inspectable,
editable agent result matters. The current panel does not locate the finding
discussed in Results, and native column names may suggest a unit not established
by the caption.

**Keep:** Original pixels and source identity; overlays as documented annotations;
separate provenance for any later inset; no inferred physical calibration.
The crossover location, correction and unit statement are evidence-dependent,
not permission to guess or add a generic warning.

### 17. Keep Figure 4's exact mapping but explain its code-facing labels

**Where:** Figure 4, reviewed page 18.

**Change:** Add brief plain labels for input configuration, processing function
and plate-wide export beside the relevant exact identifiers. Simplify redundant
heading hierarchy where it costs space. Preserve the aligned module/function
rows and object relationships.

**Why:** A biology reader should understand the diagram without knowing what
`PipelineConfig` or `FunctionStep.func` means, while a developer should still
be able to identify the precise objects shown.

**Keep:** The 16-module/12-step/16-call distinction, repeated measurements and
Comet/CometHead/CometTail identities. The initial “A” in the graphic's title is
an indefinite article, not an erroneous duplicate panel label.

### 18. Improve Figure 5's interpretation and print readability

**Where:** Figure 5, reviewed page 19.

**Change:** Use an axis/subtitle that makes repeated well assignments and
pipeline-execution time explicit. Add a visible “log scale” label; improve
contrast of the individual-workflow traces while leaving medians prominent.
Keep the existing benchmark conditions together in a compact caption section.

**Why:** The plotted distribution is useful, but a faint trace or implicit
timing unit undermines it. This is a labeling/contrast improvement, not a new
analysis or a different chart type.

**Keep:** All source values, per-workflow lines, medians, maximum-memory result
and output-policy conditions. If naming the maximum-memory workflow becomes
useful, derive that label from the retained data rather than entering it by hand.

### 19. Link the selected object to its entry in Figure 6

**Where:** Figure 6, reviewed page 20.

**Change:** Add linked callouts/enlargements connecting a displayed object with
its actual ROI entry and, for napari, its recorded coordinates. Label the panels
as separate demonstrations. Replace “native ROI Manager entries” with “entries
in Fiji's ROI Manager.”

**Why:** The present full-window views show the viewer destinations, but small
text makes the object-to-entry relationship harder to inspect. “Native” adds
an unnecessary ambiguity in this context.

**Keep:** Correct object/row correspondence, original captures and the explicit
absence of a cross-viewer segmentation comparison. Do not fabricate a matching
selection that the source image does not show.

### 20. Align supplementary navigation with the revised terminology

**Where:** Supplementary index and matching captions/prose.

**Change:** Carry the chosen terms through the supplement and data index.
Explain “serial CellProfiler projection” by its actual calculation once that
calculation is checked, rather than leaving “projection” to imply a measured
paired run. Retain the clear organization separating release comparisons,
historical timing, agent records and regression tests.

**Why:** The supplement should deepen an explanation, not silently switch
vocabulary or require readers to reconstruct what an evidence label means.

**Keep:** Raw recorded field names, exact provenance, detailed selection rules,
tables and source links. No new glossary or second manually maintained evidence
ledger is needed.

## Changes I would not make

- Remove the library table or architectural mechanism just to reduce technical
  content. Their presentation should improve; their contribution should remain.
- Replace the manuscript with generic claims about intuitive software or AI
  empowerment, or introduce “not X, but Y” framing.
- Repeat every exclusion, validation count or limitation in the abstract,
  Methods, Results, all captions and conclusion.
- Add a generic security assurance or a guessed motivation for sandbox bypass.
- Interpret every failed operation as harmless exploration or an authoring error.
- Change the historical 25-value result to 30 because a newer code branch now
  has additional reference exports. That requires a separate evidence update.
- Turn this accessibility pass into new experiments, a new benchmark, a new
  agent recording or a literature-review expansion.
- Fix asserted clipping that could not be reproduced. Parent renders show
  intact Figure 3/5 titles and reference brackets; retain those review comments
  as unconfirmed rather than manufacturing repairs.
- Add the full numerical results to the short conclusion to fill its orphaned
  page, or shrink typography to conceal the layout problem.
- Infer author order, funding, conflicts or acknowledgements. Those remain
  author-confirmed metadata, outside this editorial plan.

## Implementation and verification order

1. Apply the prose ordering and first-use explanations, without changing facts.
2. Resolve the limited source checks for proposed correction/unit annotations
   and evidence labels; omit unsupported additions.
3. Update existing figure generators and caption/layout handling. Derive labels
   and data from existing authorities; retain provenance for crops/annotations.
4. Rebuild through the configured manuscript builder. Inspect affected and
   downstream pages, figure legibility, citation resolution and the conclusion's
   placement. Preserve the original review PDFs.
5. Read abstract and conclusion independently, then the complete main text.
   Check that explanations retain declaration ownership, configurable grouping,
   runtime lifetimes and the separate scopes of the evaluations.

Expected outcome: the same technically specific paper, with its reasoning and
practical meaning available earlier. The plan does not depend on making it
longer, deleting its architecture or commissioning new experiments.
