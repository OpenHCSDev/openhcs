# Autonomous image-analysis validation: first executable tranche

Date: 17 September 2026

## What is implemented

The first tranche contains eight tasks transcribed from
[`human-eval-bia`](https://github.com/haesleinhuepf/human-eval-bia) commit
`f6edaa15545e84951f5428d07e16db04155f2266`. Each task is a nominal
`ValidationTaskDeclaration`. The task class owns its public prompt, pinned
source, expected output family, OpenHCS workflow obligations, held-out cases,
and assertion semantics. The corpus catalogue is derived from the declaration
registry; there is no parallel task list.

| Task | Output | OpenHCS decision under the current catalogue | Main stress |
|---|---|---|---|
| Otsu positive-pixel count | scalar | typed custom function | threshold/count composite and scalar artifact |
| Binary closing | array | registered primitive; square-footprint compatibility must be proven | parameter-contract inspection and split/merge review |
| Binary skeleton | array | registered function | disconnected paths and crossing review |
| Edge detection | array | registered function | saturation and tile-seam sensitivity |
| Expand labels without overlap | labels | typed custom function | object identity, splits, merges and area |
| Maximum-intensity projection | array | registered function | `variable_components=[Z_INDEX]`, grouping and projection |
| Region properties | table | typed custom function | two source bindings and typed table materialization |
| Segmentation and counting | scalar | typed custom function | sequential semantics and object count |

The registered/custom classification was checked against the current live
function catalogue. It is an expected starting point, not permission to skip a
fresh catalogue search or contract inspection during an evaluation run. In
particular, finding a binary-closing callable does not prove that its reflected
parameter surface can express the upstream task's square footprint.

The upstream notebooks and their `check` cells are protected by separate
SHA-256 identities. The local scorer is a typed transcription of those checks;
it does not import or execute the upstream evaluation harness. A provenance
audit against the pinned checkout passed for all eight notebooks and all eight
check cells.

## Blind boundary and operator protocol

The reproducible operator procedure is separate from this evidence report in
[`benchmark/agent_validation/OPERATOR_GUIDE.md`](../agent_validation/OPERATOR_GUIDE.md).
It pins and verifies the upstream checkout, creates fresh public bundles,
preserves every attempt, freezes the final pipeline and only then admits it to
held-out scoring.

The authoring bundle contains one HCS-shaped input folder and one `task.json`
per task. Its JSON states the processing objective, evidence obligations,
upstream provenance and source files. It contains no expected result or hidden
assertion. Multi-plane projection inputs are emitted as Z planes. Multi-input
measurement cases are emitted as channels so the agent must use source
bindings rather than recover roles from local filenames inside a callable.
The diagnostic bundle currently contains five independently scored candidate
failures: missing foreground, a disconnected skeleton, a split label and a
merged label, plus one complete but semantically flawed label-expansion
pipeline. Their public records expose only opaque probe identifiers; the
failure classes remain declaration-owned scorer evidence. The complete
pipeline is rendered from a typed `PipelineDocument`, declares NumPy/PURE_2D
execution and disk materialization, and has passed a real compiler artifact-plan
inspection. The injected failure classification remains scorer-owned even
though the public source necessarily exposes the parameter value to diagnose.

The public authoring bundle contains HCS-shaped input folders and answer-free
task records. The diagnostic bundle uses opaque probe identities and withholds
the injected failure classes. Rejected attempts remain evidence. Final parity,
diagnostic coverage and DSL fluency are scored separately after the frozen
pipeline boundary.

## MCP-derived attempt receipts

`McpAttemptRecorder` wraps one persistent `McpDevClient` session and writes
every complete MCP payload once, with SHA-256 identity, elapsed time and peak
process-tree RSS. It resolves each tool through the nominal capability
declaration and derives DSL evidence from successful typed responses:

- rendered `PipelineDocument` values prove `variable_components`, `group_by`
  and ordered function patterns;
- compiler artifact-plan results prove materialization planning;
- distinct successful compile and run job receipts with terminal statuses prove
  the compile/run boundary;
- registration, function detail, pipeline projection and UI code-document
  receipts jointly prove signature-derived exposure.

Failed commands are preserved but cannot create semantic evidence. Current-MCP
executions made outside the recorder can be imported with their measured
runtime/RSS, which keeps the evidence projection usable when the running UI is
newer than an isolated benchmark checkout.

## What the scorer separates

`AgentValidationCorpus.score` reports three independent outcomes:

- upstream-equivalent result assertions;
- coverage of required visual and quantitative diagnostics;
- OpenHCS DSL fluency and lifecycle correctness.

This prevents a lucky final array from erasing a poor diagnostic process, and
prevents polished screenshots from substituting for numerical parity. The
included mask diagnostic measures missed signal, unsupported mask, object
count, area quartiles, reference splits and merges, disconnected labels, and
quadrant foreground fractions. These measurements accept explicit signal and
reference masks; they do not infer truth from display colours.

The canonical typed QA policy also ranks rejected source candidates by nearby
signal support and records area, width, response, connectivity, border, debris
and already-owned dispositions. It separately ranks signal-supported residual
processes that remain unowned or unrooted. A cited screenshot must first be
localized to source coordinates and reproduced from current artifacts. Nested
current masks then attribute the miss: no accepted body is admission,
permissive-candidate-only is detection, current-candidate-only is rooted
connectivity, and an evidenced identity discontinuity is ownership. An adjacent
higher-sensitivity mask may nominate connected delta components for inspection,
but cannot become the replacement merely because it contains more pixels.
Missed-object review is therefore an admission/detection/connectivity/ownership
audit rather than a reason to lower a global threshold blindly; rejected
parameter changes remain evidence too.

DSL evidence is not a self-reported checklist. Each claimed obligation points
to a preserved MCP, UI, compiler, runtime or artifact record and includes the
agent's explanation of the observed semantics. The scorer penalizes direct
viewer/desktop automation, untyped boundary dictionaries and duplicated
metadata. Bypassing the DSL, externally preprocessing scientific inputs or
using an unregistered callable disqualifies the fluency score even when the
result pixels happen to match.

## Current evidence and remaining work

The local implementation has passed its focused unit suite, reference
implementations pass all transcribed assertions, the answer-free bundle builds,
and the pinned upstream provenance audit passes.

One fresh blind Sol diagnostic pilot is preserved at
`/tmp/openhcs-agent-validation-pilot-OtZEcG/sol-pilot`. The agent inspected the
live catalogue and contracts, registered a NumPy/PURE_2D custom function,
compiled and executed the public radius-zero candidate, inspected identical
coordinates under three percentile windows, stated one hypothesis, and changed
only `FunctionStep` radius from zero to one. Foreground increased from 7 to 19
pixels while all three label identities and every original labelled pixel were
preserved. The frozen pipeline SHA-256 is
`08c6cd0ff1e827c69393a2d8ee6b068616dc6422e0beb3418d363713511d2acb`.
After that freeze, an independent comparison against the held-out task
declaration passed exact array equality with zero mismatched pixels.

The pilot contains 79 immutable command/MCP ledger entries, raw payloads,
viewer snapshots, per-command timing/RSS, one baseline attempt and one frozen
attempt. Importing the current MCP receipts through `McpAttemptRecorder`
automatically proved artifact materialization and the compile/run boundary.
It deliberately did not award signature-derived UI exposure: the running UI
and current MCP resolved different custom-function module namespaces, so the
challenge pipeline could not be applied to the UI. The recorded no-op UI
round-trip concerned an unrelated existing pipeline. Variable/group evidence
also remains unawarded because this pilot did not obtain an MCP-rendered source
receipt. These are platform/evidence gaps, not silently completed obligations.

The next tranche is operational:

- run the remaining tasks through fresh bounded model sessions, preserving all
  attempts and eliminating the UI/MCP custom-module skew;
- extend the remaining four array-level perturbations into complete deliberately flawed
  pipeline declarations so repair can be scored at the authored semantic
  boundary as well as at the resulting pixels;
- score diagnostic action quality as well as repair success;
- add BBBC039, BBBC007 and BBBC013 once their independent-reference splits and
  acquisition manifests are frozen;
- add `cells3d` only after its redistribution licence is resolved.

The corpus therefore establishes the blind boundary and scoring substrate, but
does not yet constitute a completed cross-model benchmark.

## Current-source neurite QA proof

The corrected nuclear-seeded neurite implementation was independently executed
through the restored OpenHCS UI, a freshly replaced execution server and a
freshly replaced compatible napari viewer. The UI run completed against the
declared A01 nine-site mosaic in 134.3 s: 59.977 s in the neurite function and
52.411 s finalizing its image, ROI, graph and table artifacts. The current-source
materialized body and trace label arrays were byte-identical to the separately
computed accepted A029 arrays. They contained 1,238 body labels and 131,909
rooted-trace pixels.

A screenshot that appeared to show three conspicuously missed neurons was
localized to mosaic source coordinate `(1432, 1405)` at one-third scale. Its
normalized template correlation was about 0.894. Re-rendering that exact region
from A029 showed accepted bodies and rooted traces for all three neurons; the
reported defect was stale output rather than a current miss. The remaining
ranked evidence contains short faint terminal fragments and two small current
candidate fragments of 11 and 6 pixels that remain outside the rooted result.
It does not justify lowering source-object admission or the candidate threshold
globally.

A read-only bounded same-owner endpoint-continuation prototype tested five- and
six-pixel gap limits while preserving all 131,909 accepted rooted pixels. The
rules rejected unsupported pixels and foreign-owner crossings, but the two
bounds added only 103 and 171 pixels, respectively, mostly as tiny endpoint or
soma-edge decorations. Neither recovered the two representative current-candidate
connectivity residuals. That change was therefore rejected. The negative result
adds a QA constraint rather than an algorithmic mechanism: any future
thin-structure continuation must also exclude the accepted body neighborhood and
follow the existing terminal direction before its biological usefulness is
evaluated.
