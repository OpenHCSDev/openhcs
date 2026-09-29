# Measurement declaration checkpoint (#133, #204)

Implementation owner: Zeno. Integration owner: OpenHCS issue-batch coordinator.
Worktree: `/home/ts/wt/openhcs-exact-label-selection-20260929`.
Base: `openhcsdev/main` at `98d9b9d23`, fetched and merged normally on 2026-09-29.

## Implemented

- Measurement output validation belongs to `MeasurementsArtifactType`. Compilation
  requires a subject relation before invoking the callable. Schema-bearing rows and
  CSV materialization do not imply a measurement subject.
- Compile and runtime resolve subjects through the original relation owners. The
  error identifies the output and explains image, object, and artifact relations.
- CellProfiler catalog bindings project `require_parameter_name()`, not the optional
  raw `parameter_name`. The existing `select_object_sets_to_measure` selector is
  discoverable separately from the runtime-owned scalar `labels` parameter.
- Catalog guidance explains exact-name tuples and consumed compile-time selectors.
  No selector registry, artifact store, fallback, or ambiguity relaxation was added.

## Focused evidence

Using `/home/ts/code/projects/openhcs/.venv/bin/python` with this worktree and all
eight recorded submodule `src` directories on `PYTHONPATH`; all nine imported
package paths were verified inside this worktree. Submodules were initialized to
their recorded gitlinks without installed-source changes.

- `pytest -q tests/unit/agent/test_mcp_cellprofiler_function_contract_friction.py
  tests/unit/test_cellprofiler_artifact_identity_reconstruction.py`: 12 passed.
- `pytest -q tests/unit/test_function_artifact_outputs.py -k
  'measurement_subject or wraps_columnar_rows_with_compiled_measurement_identity'`:
  6 passed, 61 deselected. Missing and conflicting subjects fail before execution;
  the corrected image-subject declaration compiles and executes columnar rows.
- Runs used nonblocking batch validation `flock` and CPU-only mode. The resource
  guard reported 12.5 GiB available RAM and a warning for 11.7 GiB used swap.
  No large suite, JVM, MCP, or extra GUI was started.

Architecture review was focused source/ownership inspection, not a complete NRA
scan. It follows the NRA and current refactor-audit declaration-ownership rules.

## Remaining acceptance

- Continuous synthetic two-producer compile, exact-selector document roundtrip,
  runtime binding, and omitted-selector ambiguity regression for #204.
- Realistic current headless compile-inspection entrypoint for both issues.
- Coordinator-authorized actual UI code-document/live installation validation.
  Source tests do not establish installed readiness. Worker must not install or
  merge, and must not inspect Euler's blind input or output.
- Correct #204's diagnosis after the complete selector proof; retain its original
  observed failure. Both issues remain referenced, not claimed closed here.

No owned large scratch artifacts have been created. Viewer-bind and ROI
materialization implementation surfaces remain with their assigned owners.
