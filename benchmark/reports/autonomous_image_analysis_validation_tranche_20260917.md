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

## How to prepare a blind run

Clone the pinned evidence separately and verify it:

```bash
git clone https://github.com/haesleinhuepf/human-eval-bia.git /tmp/human-eval-bia
git -C /tmp/human-eval-bia checkout --detach f6edaa15545e84951f5428d07e16db04155f2266
python -m benchmark.agent_validation verify-upstream /tmp/human-eval-bia
```

Create an answer-free authoring bundle in a new directory:

```bash
python -m benchmark.agent_validation build /path/to/run/authoring
```

Create the separate diagnostic-repair track with opaque probe identifiers:

```bash
python -m benchmark.agent_validation build-diagnostics /path/to/run/diagnostics
```

Give the authoring agent only that directory, the running OpenHCS UI/MCP
surface, the model/run identity, and the same bounded instructions used for
every model. Do not give it this source package, a scorer process, upstream
`check` cells, accepted output arrays, or a prior agent's pipeline.

The authoring bundle contains one HCS-shaped input folder and one `task.json`
per task. Its JSON states the processing objective, evidence obligations,
upstream provenance and source files. It contains no expected result or hidden
assertion. Multi-plane projection inputs are emitted as Z planes. Multi-input
measurement cases are emitted as channels so the agent must use source
bindings rather than recover roles from local filenames inside a callable.
The diagnostic bundle currently contains four independently scored candidate
failures: missing foreground, a disconnected skeleton, a split label and a
merged label. Their public records expose only opaque probe identifiers; the
failure classes remain declaration-owned scorer evidence.

## Required attempt loop

For every task, preserve each attempt under a distinct identifier and record:

1. the observed failure and one falsifiable hypothesis;
2. one declaration-owned semantic change;
3. the complete pipeline hash and compile result;
4. bounded runtime and peak resident memory;
5. raw, normalized, mask/ROI and measurement views at identical coordinates;
6. at least three declared percentile windows with their computed intensity
   bounds;
7. requested missed-signal, unsupported-mask, split, merge, disconnected-path,
   crossing/ownership, tile-seam, saturation, count, area and foreground checks;
8. evidence for the task's `variable_components`, `group_by`, function-pattern,
   source-binding, artifact/materialization and compile/run obligations.

Rejected attempts remain part of the run. A later attempt must name exactly one
semantic change and have a different pipeline identity. A final candidate is
admitted to scoring only after the pipeline is frozen. The held-out result is
then produced once unless a preregistered infrastructure failure invalidates
the execution.

For custom-function tasks, the run record must show that the agent searched the
live catalogue, identified the exact gap, registered a typed function through
OpenHCS, and observed the same signature/defaults in function detail, generated
code, the parameter form, and MCP. A standalone script can be useful during
private reasoning, but it does not satisfy the task.

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
and the pinned upstream provenance audit passes. No autonomous model result is
claimed yet.

The next tranche is operational:

- add the MCP-derived attempt recorder so compile plans, runtime observations,
  UI/code round trips and materialized artifacts populate `AttemptRecord`
  without agent self-report;
- run the eight tasks through fresh bounded Sol sessions, preserving all
  attempts;
- extend the four array-level perturbations into complete deliberately flawed
  pipeline declarations so repair can be scored at the authored semantic
  boundary as well as at the resulting pixels;
- score diagnostic action quality as well as repair success;
- add BBBC039, BBBC007 and BBBC013 once their independent-reference splits and
  acquisition manifests are frozen;
- add `cells3d` only after its redistribution licence is resolved.

The corpus therefore establishes the blind boundary and scoring substrate, but
does not yet constitute a completed cross-model benchmark.
