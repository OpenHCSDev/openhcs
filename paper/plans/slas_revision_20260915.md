# SLAS revision: automation framing and complete workflow comparisons

## Editorial contract

Source: `paper/manuscript.md`; supplement: `paper/supplementary/README.md`.
Build declaration: `paper/build_paper.py`, using the pinned shared `paper-build`
package. Baseline: `paper/build/run-20260915T165555-9606087c` (25 + 16 pages).
Revised pair: `paper/build/run-20260915T172404-b6510b79` (26 + 17 pages).

Narrative audience: experimental biologists and laboratory-automation users.
Venue audience: SLAS Technology reviewers evaluating implementation, reuse and
experimental evidence. Style authority: the papers repository's
`docs/papers/writing_style_guide.md`; procedure: `paper-style-guide-pass`.
This is a targeted author-approved revision, not a new neutral reviewer panel.

Central claim: scientists and agents operate the same editable microscopy
workflow. Function declarations supply parameter controls and catalog descriptions;
workflow state supplies configured Python; MCP request declarations own operation
schemas; compilation combines function requirements, configuration and inputs.

## Edit ledger

| Location | Reader's first recoverable claim | Entry/pointer issue | Smallest repair | Audience |
| --- | --- | --- | --- | --- |
| Introduction, automation paragraph | Laboratory automation derives interfaces from shared declarations | Prior two-citation paragraph did not establish the mechanism's automation lineage | Add Tecan SDK, Lange infrastructure and Courtney autopilot; place before bioimage tools | Both |
| Introduction, OpenHCS paragraph | Apply interface derivation to microscopy analysis | Avoid unsupported universal absence and signature-alone MCP/compilation claims | Name controls, catalog descriptions and configured workflow Python separately | Both |
| Introduction, related AI tools | Tools expose different analysis authoring/execution models | Generic code generation is not evidence that other systems lack validation | State OpenHCS's validated, shared editable workflow positively | Venue |
| Introduction, closing paragraph | Editing round trip, reference agreement, agent run and scaling are demonstrated | Old paragraph listed examinations rather than findings | State demonstrated outcomes directly | Broad |
| Abstract and Results | All 30 workflows have selected reference-value comparisons | Draft described only older 25-workflow reference coverage | Add five-workflow extension and preserve run identities in Methods/supplement | Both |
| Agent Results | Validation rejected 17 authoring attempts; output checks missed a crossover error | Refusal and successful output checks were described apart from their scientific consequence | Connect exact observed validation behavior to later visual finding; count calls rather than distinct bugs | Both |
| Methods, comparison extension | Exported outputs of five workflows were compared on recorded environments | Neither historic dependency pins nor current environment identify prior runs | Report run-linked candidate and native versions only for the extension | Venue |
| Figure 5, Results and Supplementary Data 3 | Throughput counts repeated-image assignments | Wells, images and assignments sounded like different sample populations | Use assignments consistently and explain virtual-well CSV terminology once | Both |
| Supplementary Data 1 and snapshot table | Eight added artifacts provide five additional workflow comparisons | New evidence had no manuscript navigation | Link manifest, per-artifact table, observations and run environment directly; preserve originals | Venue |

## Evidence checked

- `label_aware_exact_commit_run/artifact_comparisons.csv`: 8 passing artifacts,
  5 distinct workflows, 5 categorical-label and 3 numeric-image comparisons;
  maximum reported absolute numeric difference `2.9802322387695312e-8`.
- `observations.jsonl`: all five candidates equivalent with zero differences.
- `run_environment.json`: execution source `7ca8ecb8e73a882ef0f15616d57b00f0dabf73e0`;
  candidate Python 3.12.3, NumPy 2.1.3, SciPy 1.18.0; native CP 4.2.8.1,
  Python 3.9.25, NumPy 1.24.4, SciPy 1.9.0. These are not asserted as release-CI
  or May timing environments.
- Original agent event-log SHA256 matches the evaluation record. It contains
  17 completed `openhcs_ui_validate_code_document` error calls, 30 operation-error
  calls in total, plus one separate failed operation-name call.
- Bibliography: 31 unique IDs; all 31 manuscript citation keys resolve. Added
  metadata checked against Crossref and author abstracts indexed by PubMed:
  Tecan DOI `10.1016/j.slast.2023.07.001`, Lange DOI
  `10.1016/j.slast.2025.100380`, Courtney DOI `10.1016/j.slast.2025.100279`.
  Lange's issue date is January 2026 (online December 2025).

## Validation

- Successful paired shared-package build; `current` points to the revised pair.
- 7 paper build/regression tests passed using two processes. Build-only pytest
  emits harmless warnings about runtime-only asyncio configuration options.
- Abstract: 206 whitespace-separated words.
- Rendered all 43 pages for layout overview; inspected enlarged introduction,
  agent Results and added supplementary evidence table. Figures remain present;
  no clipping or table/figure overlap observed in that inspection.
- Resolved all 3 manuscript and 31 supplement PDF local launch links to existing
  files. New citations render as numbered references, not unresolved keys.
- `git diff --check` passed. Unrelated uncommitted OpenHCS/CI changes preserved.

## Manager-preview visual evidence

Include the Plate Manager and Pipeline Editor list previews in the visual story,
alongside the matching configuration forms. Show one row expanded while another
stays compact, then the same field before and after saving. This makes the
configuration hierarchy and its live state visible in the main UI.

Use the existing native-capture storyboard and receipts in
`mcp_outputs/slas-validation-20260915/runtime/engineering/manager-preview/`.
Panels A-E already have stable manager/form captures; publication integration
remains pending. Retain full-window originals and derive any panel crops through
the existing capture/figure declarations.

Caption the two independent indicators accurately: underlining marks a raw
value different from its signature default; `*` marks a resolved live value
different from its saved baseline. A saved override keeps its underline but
loses its star. An inherited value can acquire a star without a raw override.
The underline is font styling, not a literal `_` character. Use the same field
and state in the manager and form panels so readers can see that correspondence.

Keep active flashing separate from this stable-state comparison. Maximum-opacity
and padded-mask claims require their own actual paint/capture receipts; the
stable preview screenshots alone do not establish them. Integrate through the
existing gallery scenario and figure declarations, without introducing another
caption or state authority.

## Still open: matched performance experiment

Supplementary Figure 6 and its historical data remain unchanged. Replacing it
requires new measurements with equivalent timing boundaries and outputs, not
replotting unequal historical intervals. Sol agent `close_parity_ci_gaps` is
developing a bounded pilot using native batched execution and the production
OpenHCS execution-server path. A one-workflow/single-worker pilot cannot replace
the existing multi-workflow figure or establish matched parallel throughput.

Match source assignment units, preserve groups/time-series and plate-wide exports,
record preparation separately, verify actual execution intervals and completed
outputs, retain environments and repeat observations. Higher-concurrency native
jobs must preserve image identities and support comparison of their exported
tables with production OpenHCS plate-wide results.

No general intra-well thread-budget capability is claimed. The author confirmed
it is prospective. Worker count and thread/process executor selection are
different controls. Historical thread settings are not expanded into an
unsupported universal guarantee.
