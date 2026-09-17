# How to run a blind OpenHCS agent-validation task

This guide is for benchmark operators. It keeps authoring evidence separate
from held-out answers and preserves every diagnose-edit-rerun attempt.

## Prepare the public bundle

Use a fresh output directory and a separately pinned upstream checkout:

```bash
git clone https://github.com/haesleinhuepf/human-eval-bia.git /tmp/human-eval-bia
git -C /tmp/human-eval-bia checkout --detach f6edaa15545e84951f5428d07e16db04155f2266
python -m benchmark.agent_validation verify-upstream /tmp/human-eval-bia
python -m benchmark.agent_validation build /path/to/run/authoring
python -m benchmark.agent_validation build-diagnostics /path/to/run/diagnostics
```

Give the authoring agent only the selected public task directory, a fresh
OpenHCS UI/MCP session, and the same resource limit used for every run. Do not
mount `benchmark/agent_validation`, upstream check cells, hidden arrays, scorer
outputs, or another agent's attempts into its working context.

## Record the authoring loop

Create one `McpAttemptRecorder` for each attempt and execute MCP commands
through its persistent `McpDevClient`. The recorder preserves raw typed MCP
responses, elapsed time, process-tree peak RSS, and evidence derived from the
compiler, catalogue, runtime, artifact, and UI authorities.

For each attempt:

1. Read the task and current pipeline through MCP.
2. Inspect raw data at the same coordinates under at least three declared
   percentile windows, including weak and strong clipping.
3. Compare raw, normalised, mask or ROI, overlay, and measurement evidence at
   those coordinates.
4. Preserve ranked rejected-source candidates and signal-supported unowned or
   unrooted residual structures in the attempt observation when applicable.
5. For an unexplained miss, make one adjacent higher-sensitivity diagnostic
   attempt, subtract the accepted candidate mask, and rank the added connected
   components by raw-signal support and valid-root connectivity. The permissive
   result is evidence; it is not automatically the replacement result.
6. State one falsifiable hypothesis and change one declaration-owned semantic
   gate.
7. Compile, run a bounded public case, and inspect the materialised outputs.
8. Finalise an `AttemptObservation`; never replace a prior attempt directory.

Use the image-analysis workflow guidance returned by OpenHCS as the canonical
QA procedure. Its gate and measurement wording is generated from
`ImageAnalysisQaPolicy`, rather than maintained as a second checklist here.

If a UI/runtime version mismatch prevents direct recorder execution, preserve
the current MCP command as `McpDevCommandExecution` with independently measured
elapsed time and peak RSS, then import it with `preserve_execution`. Record the
mismatch as platform friction; it does not excuse a missing semantic receipt.

## Freeze before scoring

After public-case review:

1. Save the complete pipeline source.
2. Capture its identity with `FrozenPipeline.capture`.
3. End authoring access.
4. Verify the frozen identity before the first held-out execution.
5. Execute held-out cases once, unless a preregistered infrastructure failure
   invalidates the run.
6. Score final parity, diagnostic coverage, DSL fluency, architecture
   violations, and lifecycle correctness independently.

Do not reveal a failed held-out assertion to the authoring agent and rerun it as
another edit cycle. That would turn the held-out set into training data.

## Audit the run

Before accepting a result, confirm that:

- every attempt has a distinct immutable receipt and pipeline hash;
- each revision names exactly one semantic change;
- failed MCP payloads contributed no positive DSL evidence;
- custom-function evidence correlates the same function identity across
  registration, detail, rendered pipeline, and UI code projections;
- compile and execution are distinct successful jobs with terminal statuses;
- all required views use identical coordinates and crop geometry;
- the frozen pipeline still matches its recorded SHA-256 identity; and
- held-out outputs were created only after the freeze boundary.

The implementation and current evidence inventory are described in
[`../reports/autonomous_image_analysis_validation_tranche_20260917.md`](../reports/autonomous_image_analysis_validation_tranche_20260917.md).
