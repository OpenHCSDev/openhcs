# Reuse analysis recipes and diagnosed failures

Agentic-J's [learned-memory skill](https://github.com/MMV-Lab/Agentic-J/blob/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/learned_memory/SKILL.md)
and version-scoped plugin packs distinguish reusable experience from a one-off
script. OpenHCS should retain that useful distinction through its existing
source-backed knowledge service, not create a second recipe database or silently
write to an agent's personal memory. This is a repository-knowledge workflow;
memory writes, external publication and held-out access need their own authority.

## Retrieve before retrying

Search by biological target plus observed failure: for example, nucleus split
inside one bright body, cytoplasm zero-growth, faint neurite lost after background
subtraction, or labels misaligned after resampling. Search exact technical error
text and callable/artifact owner when it is a compile or runtime failure.
Retrieve the relevant section, not every recipe sharing the word segmentation.

Compare input contract, versions, units, dimensions, channel identities and
validation scope before applying a repair. Official30 selected-value parity is
meaningful reference evidence, but not proof of new-assay raw biological support.
Do not turn a plausible explanation from an earlier run into an observed fact.

## Record an experience that can be tested again

Within an authorised trial log or repository contribution, retain:

- **Applicability:** target, stain/source assumptions, dimensionality, calibration,
  acquisition and relevant callable/model version or declaration reference.
- **Reproduction:** exact reviewed pipeline/parameter identity, bounded development
  input identity, compile/run receipt and persisted result/intermediate paths.
- **Failure witness:** observed symptom, native coordinates, channel/windows,
  raw-only/result-only/combined witnesses, and a positive/regression control.
- **Causal test:** predicted failed stage, one changed operation/parameter group,
  failed-predecessor receipt, candidate pipeline/parameter identity, rerun
  receipt, observed difference, remaining ambiguity and rejection/acceptance
  rationale. A proposed fix is not a successful repair until its rerun is
  inspected; execution-confirmed repairs are not yet biologically accepted.
- **Transfer boundary:** what was actually tested, what remains inferred, known
  regressions/exclusions, and whether the candidate is merely technical, a
  development acceptance, frozen or independently validated.

Do not embed held-out images, ground-truth labels, notebook answers or evaluator
scores in an agent-facing knowledge card. Store teaching examples outside blind
task answer paths; identify source overlap before evaluating a task. A lesson
from development data must not leak the validation answer.

## Promote through the existing owners

For a reusable contribution, place the source note in the existing
`docs/source/development/recipe_knowledge/` collection or a task-relevant skill
reference. Register that source once in
`docs/source/development/mcp_knowledge_base_manifest.json`, with search terms for
its task and failure; use the existing search/retrieval and package projection.
Keep function settings and backend semantics on their declaration owners; a
knowledge note links to those contracts and tested sources rather than copying
a second executable parameter catalogue. Retain attribution and source revision.

Follow the blind-recipe promotion guide before claiming reusable validation.
The metadata audit only checks claim coherence; it cannot authenticate receipts,
judge pixels, enforce access or establish correctness. Ask for biological input
when the target or ambiguity cannot be resolved from acquisition and raw data,
not for every ordinary implementation or diagnostic decision.

## Avoid importing another tool's incidental workaround

Agentic-J's MorphoLibJ pack records version-specific popup/parameter hazards;
its Cellpose wrapper records per-call process/model startup; its Coloc 2 pack
records retained result-window memory. These are upstream observations about
those Fiji routes, not evidence of the same leak or API error in OpenHCS.

Transfer the diagnostic pattern: identify the actual owner, inspect the exact
input/option contract, distinguish process startup from inference, and compare
resource lifetime before/after a bounded batch. A dialog requires a supported
MCP/UI control contract, not injected clicks. A timeout is not proof a job died;
check the same job/process before retrying. Do not add a blanket sleep, increased
timeout, arbitrary garbage collection or a copied foreign cleanup function.

## Evidence-based improvement

Test a proposed skill change independently on a realistic bounded development
scenario without supplying the intended answer. First assess decisions and
retrieval: channel verification, matched raw inspection, failed-stage diagnosis,
parameter units, regression controls and blinding. Then, with separate approval,
evaluate actual compiled/executed outputs and native biological witnesses on
the isolated display. Compare a frozen baseline and candidate under the same
data/access/resource budget. Documentation and search tests prove availability,
not an autonomous biological performance gain.
