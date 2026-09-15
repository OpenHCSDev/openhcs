# CI-evidence manuscript revision

## Editorial contract

Target: `paper/openhcs_nature_methods_draft.md`, its supplementary README and
Figure 1/5 generators. Venue: SLAS Technology, Self-Driving Laboratories special
issue. Broad narrative reader: scientist or laboratory-automation practitioner;
venue precision reader: software/instrumentation referee. No new abstract limit
was verified; the supplied venue guidance suggests fewer than 7,000 words and
seven main figures/tables. Keep the existing six figures and one table.

Style authority: papers repository `docs/papers/writing_style_guide.md`, used
through `paper-style-guide-pass`. The separate reviewer skill remains unavailable;
the repository neutral page-by-page prompt governs panel procedure. This second
assessment returns to the original collaborators and is not an independent
blinded review.

Central claim: scientists and agents edit one configured workflow, with function
declarations supplying controls, Python and catalog descriptions, and the
compiler combining requirements with configuration and image sources.

Protected distinctions: processing-function catalog versus operation request
schema; source coordinates versus storage paths; persistent execution server
versus within-run worker reuse; candidate execution versus retained native
reference; selected-value parity versus scientific accuracy; agent's original
run versus later correction; release parity versus May performance timing.

Protected landings: scientist takeover of agent-authored pipelines; named
intermediate results available for inspection; the concrete 99.8/99.6 editing
example; Comet module/function/object mapping; the later crossover correction.

Baseline: `paper/review/slas-panel-20260914/input/`, 24 main pages and 15
supplement pages. Revised build: `paper/review/slas-evidence-revision-20260914/`.
Original PDFs and reviewer reports remain unchanged.

## Edit ledger

| Location | First recoverable claim | Unresolved entry state | Pointer load | Missing/weakened landing | Smallest repair | Audience |
|---|---|---|---|---|---|---|
| Abstract comparison result | Imported workflows preserve selected values | Historical-only phrasing omits existing release CI | None | Current tested version absent | Name 0.8.5 and 30 executions /25 selected-value cases | Both |
| Comparison Methods | Native/candidate outputs are compared | Reader cannot identify execution producing result | Supplement pointer | Fresh candidate and cached native conflated | Describe pinned release CI, fresh candidate, retained native and output policy | Venue |
| Comparison Results | All reference-bearing cases agree | Wrong three-image count; empty references mixed with passes | One supplement +figure | Result denominator ambiguous | Correct two image cases; separate five execution-only cases | Both |
| Authoring Results | Screenshot demonstrates shared editing | Existing representative regression tests omitted | One supplement | Reader infers screenshot is sole test | Add short test-evidence paragraph; source index in Data6 | Venue |
| Performance Methods/Figures1,5 | Workers reuse loaded resources | Persistent-worker label suggests cross-request lifetime; replicated ambiguous | Existing performance supplement | Same worker scope not maintained | Within-run labels, repeated input assignments, one recorded run/condition | Both |
| Discussion | Evaluations support shared workflow | Old missing-record caveat presented as complete evidence state | None | Late confidence collapse despite existing CI | Describe release comparison distinctly from older scaling records | Both |
| Supplement/availability | Evidence can be inspected | CI artifact expires; original records missing from supplement | Source index | No stable local bundle | Preserve exact release files +hashes; link once; keep snapshot table single | Venue |

## Deferred, not asserted

At the PDF freeze, four discrepancies among the five newly exported workflows
remained under active source diagnosis. The parallel agent subsequently reported
a fresh five-case run with 5/5 cases and 8/8 declared artifacts equivalent;
its retained provenance and code validation are being completed separately.
No expanded 30-value result is included in this reviewed manuscript. Historical Figure5
hardware/software metadata is not inferred from the present machine. Author,
affiliation, funding and conflict statements require author facts. No publication
or push is implied by this editorial pass.

## Verification before re-review

- Built both DOCX files through the configured Pandoc builder and rendered with
  LibreOffice. A two-line conclusion overflow in the first render was repaired
  by consolidating duplicate Discussion prose, not shrinking typography or
  removing a result. Final main24pages/conclusion13/figures14–19; supplement16.
- Main hash `b9463ae38b605d2963c7a7ce03b87d3f210fa06b244ce460d9feab459e29cfb2`;
  supplement hash `4ff736d2ae557a59cf55315fddc8f9596e1a943460eb33951b7b2e5a337ef571`.
- Local links resolve; all28 citation keys resolve. Main retains six figures
  and one table. Numeric source tables and plotted-row CSVs were not changed.
- Parent checked comparison Methods, conclusion and new supplementary tables
  visually, along with updated Figure1/5 artwork. No clipped labels or table
  collisions were found. Contextless reader completed baseline and final main
  reads in `revision_readability.md`.
- Declined extra narrative caveats where current scope is already explicit.
  Reader's asserted literal `PipelineConfig + source bindings` label in Figure1
  is incorrect: parent rendered baseline page14 and inspected the actual image;
  it says `configuration + ordered function steps`. No repair needed for that
  assertion. Slightly faint per-workflow Figure5 lines remain a presentation
  preference, not a numerical discrepancy.
- Markdown/Python diff whitespace check and Black check passed. Matplotlib
  regenerated SVG path syntax includes its normal trailing whitespace; these
  generated files were retained with matching provenance hashes.
- Release observations were independently counted (30), checked for uncached
  candidate/cached native flags and zero recorded differences, and copied files
  verified byte-identical. Original reference tree and portable manifest have no
  tracked changes between the release commit and current HEAD.
- Returning original reviewers now assess the locked PDFs. This is an informed
  re-review after collaboration, not another independent blinded panel.

## Submission packaging follow-up

Three supplementary references currently resolve locally under ignored
`paper/review/`: the timing-boundary audit, figure storyboard and agent-trace
audit script. Before public deposition, retain any needed evidence in the
versioned supplementary package or replace these links with stable source
references. Local link resolution alone does not establish public availability.
The frozen review PDFs have not been changed to conceal this packaging task.
