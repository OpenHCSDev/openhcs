# Confirmed-claim manuscript revision

Date: 14 September 2026.

## Editorial contract

- Source: [complete manuscript](../openhcs_nature_methods_draft.md).
- Venue: SLAS Technology, original research for the self-driving laboratories
  special issue.
- Narrative audience: life-science researchers and laboratory-automation
  scientists who need to understand what they can do with the platform.
- Venue audience: technology reviewers assessing implementation, interoperability,
  experimental scope and reproducibility.
- Canonical guide: `../papers/docs/papers/writing_style_guide.md`, resolved from
  the OpenHCS repository root. Read completely, with the
  `paper-style-guide-pass` skill.
- Build: `paper/build_docx_from_markdown.py`, Pandoc/citeproc to DOCX, then
  LibreOffice PDF export. Reading copies are under
  `paper/review/slas-confirmed-20260914/`.
- Baseline: `baseline.pdf`, 23 pages. Final: `revised.pdf`, 24 pages;
  `supplement.pdf`, 15 pages. These are local author-review artifacts.
- Abstract: 178 whitespace-delimited words in the submitted Markdown paragraph.
  The publisher guide returned HTTP 403, and the society's accessible journal
  page did not supply numeric length limits. No verified journal word/page limit
  or submission-format compliance is claimed by this editing pass.

The author authorized confirmed-claim editing while new reference comparisons
proceed. The [claim ledger](slas_framing_discussion_20260914.md) retains the
separate evidence decisions. Newly reported benchmark runs are not incorporated
until their receipts have been inspected.

## Protected meaning

Registered functions supply parameter declarations used by controls, editable
Python and catalog descriptions. MCP operations act on the shared workflow;
their request schemas describe those operations. Compilation also requires
function requirements, configuration and selected data.

Evidence remains separated into the editing round trip, historical reference
comparisons, one recorded agent analysis and replicated-well measurements.
Preserve the 25 reference-bearing cases, five export-free cases, single-field
agent scope, later crossover correction, historical timing boundaries and
unknown executed environments. No formal proof of numerical equivalence or
repository-wide absence of duplication is claimed.

## Edit ledger

| Location | Reader's first recoverable claim | Unresolved entry state | Pointer load | Missing or weakened landing | Smallest repair | Audience encountering friction |
| --- | --- | --- | --- | --- | --- | --- |
| Title/abstract | Scientists and agents share an editable workflow | Derivation mechanism previously implicit | None needed | Why interfaces stay connected | Name the shared workflow; explain function-derived controls/code/catalog before demonstrations | Both |
| Introduction | Processing choices survive movement between interfaces | Relationship between declarations and configured values | Existing literature citations retained | Scientist can revise agent-authored analysis directly | Add the concrete function-to-interface path and compiler inputs | Broad |
| Workflow Methods | Signatures describe parameters; configuration supplies values | Defaults versus edited/inherited values | One supplementary figure | How code represents the current analysis | State both inputs to form/code generation | Both |
| MCP Methods | Generic operations discover functions and edit workflows | Catalog descriptions versus tool request schemas | MCP citation retained | Additional functions use existing operations | Explain the two declaration roles without implying a per-function tool registry | Both |
| Infrastructure Methods/Table 1 | Eight packages implement reusable mechanisms | Availability list supplied names without roles | One table | Reuse below the microscopy layer | Give each library its checked role; link repositories once in the table | Broad |
| Comparison Methods/Results | 25 cases retain values; five have no exports | Boolean pass versus value denominator | Supplementary Data 1 | What the numerical evidence covers | State CSV/SQLite/array counts; distinguish current image-selection policy from measured pixel differences | Both |
| Execution/throughput | Workers are reused within a run | Persistent server versus worker lifetime | Supplementary Figure 2/Data 3 | Which reuse is actually supported | Describe resource creation/release; use workers consistently rather than cores | Both |
| Agent Methods | Both client protections were bypassed | Ambiguous scope of 'bypassed' | Original run record | Actual autonomy conditions | Add 'both'; verify the recorded launch flag | Both |
| Performance Methods/Figure 5 | Measurements concern the configured workload | Internal option names and pruning omitted from main prose | Supplementary Data 3 | What saving/record transfer/pruning change | Explain the options and pruning request in ordinary language | Both |
| Discussion | Shared declarations enable direct editing after agent operation | Evidence classes previously dispersed | Table 1 plus established evidence | Practical next use and evaluation | Reconnect mechanism to results; consolidate evaluation scope; retain concrete next experiments | Both |
| Supplement/availability | Archive records comparison status for 30 cases | 'Accuracy' could imply pixel or segmentation accuracy | Linked original CSVs retained | What 1.0 means | Explain Boolean summary and coverage; preserve original source tables | Venue |

## Reader check and verification

A contextless subagent read the complete style guide, all 23 baseline pages and
all 24 revised pages, including rendered figures, captions, table and references.
It independently recovered the declaration-derived mechanism and the four
evidence classes. Its checks prompted the worker/core and approval wording
repairs, the pruning condition and the comparison-status label. The pruning
request was verified in `f58bca4e9:benchmark/well_throughput_scaling.py` before
inclusion; specific historical removed steps are not asserted.

The final rebuild retains 24 pages. Main text ends on page 13, versus page 12
in the baseline. Figures occupy pages 14-19, and references begin on page 21.
Table 1 splits between rows across pages 5-6 with repeated column headers and
legible text. Parent inspection covered the final title/abstract, table,
performance Methods, Discussion ending, affected figure caption and supplement
coverage page. No empty pages, clipped table rows or new figure collisions were
found. The unchanged small measurement-table detail in Figure 3 remains an
artwork improvement for a later pass.

All 38 local links in the manuscript and supplement resolve; citation keys
resolve against `openhcs_references.json`. `git diff --check` passed. Scientific
images and archived numeric tables were not changed by this prose revision.

Final identities:

- Manuscript SHA256: `f1ac25c316410ceff531dc270746ce706a7a23e12817cb13a022e972d501f40b`.
- Supplement SHA256: `4d5db6ae51b4235a6f813f0af2fafa713e5b185872dcfba1625c6a55f7cd1faf`.
- Revised PDF SHA256: `c3d25fdd1cf3d5ca843243a7f44abd91587a6af10f174f70183ab48c57523900`.

This is a confirmed-claim editorial revision with an independent reading check,
not a submission-readiness certification or a neutral venue acceptance panel.
