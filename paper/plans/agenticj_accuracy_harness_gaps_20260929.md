# Draft: accuracy-oriented analysis harness follow-up

Baseline: OpenHCS main `0c7b898f852a8bedc0e1bc38b93f36088d301808`.
Status: research proposal plus a narrow implemented guidance checkpoint. The
existing typed QA policy now owns development continuation and intervention
provenance rules, plus distributed preprocessing-regression review. The existing
skill references describe their use and recipes for fast NLM, shared-field
illumination correction and the BaSiCPy readiness boundary.
No runtime trial controller, full NRA proof, blind accuracy improvement or
human-superiority claim is included. Keep this draft open while remaining
implementation surfaces and tests are resolved.

## Existing work, not new gaps

[PR136](https://github.com/OpenHCSDev/openhcs/pull/136) already adds domain
guides, source-backed retrieval, stage diagnostics, viewer QA and a metadata-only
recipe-promotion audit. [PR144](https://github.com/OpenHCSDev/openhcs/pull/144)
adds installer skill synchronisation. [PR149](https://github.com/OpenHCSDev/openhcs/pull/149)
adds typed custom-function guidance. [PR150](https://github.com/OpenHCSDev/openhcs/pull/150)
adds explicit example-selection evidence and isolated storage guidance.
Do not implement another knowledge catalogue or copy these guides.

## Observed gaps and candidate changes

1. **Make validated-example use observable in the blind harness.** Actual trial
   calls lacked Official30 pipeline retrieval; an intake log says public examples
   were skipped under the blinding restriction. Explicitly permit generic
   validated method examples while withholding the current task's solution,
   expected outputs and peer trials. Record exact search/section/source identity,
   applicable input contract, available validation scope and the adaptation or
   rejection decision before authoring. Existing knowledge DTOs and
   declaration-owned authoring contexts remain the source authorities.
   Acceptance: a fresh context-isolated author actually retrieves a compatible
   example or records a concrete mismatch, without consulting task answers.

2. **Catch custom-artifact ABI failures before a scientific run.** An observed
   custom measurement output compiled but failed during subject contextualisation.
   Investigate the existing callable/artifact declaration validation boundary and
   a bounded synthetic payload check through the real runtime contextualiser.
   Do not bypass validation or infer subject semantics from an output name.
   Acceptance: reproduce the failing declaration, reject it before scientific
   dispatch, and accept the corrected declaration with empty and ordinary payloads.
   Broad contract compatibility must be audited before changing compiler rules.

3. **Make matched visual review easier to perform correctly.** Existing MCP
   commands support source/result inspection and presentation changes; independent
   capture calls still require repeated identity, visibility and canvas checks.
   Assess composition of existing typed viewer commands into a bounded review
   operation before introducing a new surface. Preserve raw-only, result-only
   with every image hidden, and combined captures at identical coordinates and
   numeric windows; reject or recapture when presentation changes. Derive MCP
   exposure from the existing declaration owner, not a manual tool registry.
   Acceptance: real viewer tests with deliberate resize/pan/layer changes, no X
   input automation, bounded RAM, and personal bitmap review. Structural checks
   must never return a biological acceptance judgement.

4. **Retain reusable failures and evidence-qualified recipes.** Current guidance
   and `RecipePromotionEvidence` distinguish compile, execution and biological
   evidence, but the audit checks caller-supplied metadata, not receipt authenticity
   or pixels. Inspect the existing source-backed knowledge and trial-record owners
   before proposing a durable learning capability. Keep failed predecessor,
   semantic repair and rerun separate; expose only authorised, sanitised guidance.
   Acceptance: rejected or execution-only candidates cannot appear as biologically
   accepted recipes; altered/missing receipts are detected; test answers never
   enter author-facing retrieval. No parallel vector database or metadata mirror.

5. **Measure contribution, not just successful orchestration.** Compare recipe
   retrieval, stage checks and visual QA on/off independently with matched model,
   budget, dependencies, knowledge state and retry limits. Repeat independent
   sessions; retain failures, abstentions and unassigned objects in denominators.
   Distinguish human-only, agent-only and assisted results with uncertainty at the
   independent field/specimen level. Freeze before reference comparison; a
   solution-informed repair is a new development attempt, not another blind score.

## Implementation boundaries and remaining work

These are ranked hypotheses, not a completed architecture plan. Record the
ownership/dependency evidence appropriate to each change and distinguish focused
source/AST checks from complete NRA scans and native proofs. The owner permits
lighter checks when a large NRA scan would block useful delivery. Keep semantics
on existing nominal owners and use MI/MRO composition
where capabilities are independent. Never substitute a second registry, type-name
dispatch, fallback import or arbitrary metadata store for the owning contract.

The post-dispatch transport fallback defect was repaired in merged
[PR181](https://github.com/OpenHCSDev/openhcs/pull/181); the issue receipt records
an installed actual resident-session check preserving caller failure and
reconnecting to the same healthy process. Do not implement a competing fix.
Cold/preparation latency remains separate under
[issue178](https://github.com/OpenHCSDev/openhcs/issues/178). Preserve uncertain
mutation identities; never replay a Run or increase timeouts as a speed fix.
Optimise measured cold/warm behaviour separately from biological accuracy;
prewarming is useful only with scoped ownership and RAM limits.

## Source and evaluation limits

[Agentic-J](https://arxiv.org/pdf/2606.02080v1), Sections 2.2.2 and 3.3,
reports 88.89% classification accuracy with 50% sensitivity against expert
labels, not superior human accuracy or component ablations. Its recipe store
qualifies snippets mainly by successful execution; do not weaken OpenHCS's
biological evidence tiers to match it. Later official implementation features
are design evidence, not established causes of the published result.

This draft contains no scientific inputs, expected counts, notebook answers,
dataset-specific thresholds, held-out outcomes or tuned pipelines. Validation
includes packaging checks and four focused policy-projection tests. These prove
source guidance projection, not autonomous decisions or recipe execution. Actual
running MCP discovery/signature checks confirm the existing fast-mode ReduceNoise
and illumination calculation/application routes. Installed metadata shows no
BaSiCPy package in the current analysis environment; a wrapper's registry presence
does not establish readiness. A separate backend owner is checking the existing
`trissim/BaSiCPy` fork for Python 3.14 support. New guidance live MCP delivery,
remaining runtime infrastructure and controlled blind evaluation remain outstanding.
