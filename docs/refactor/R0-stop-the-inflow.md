# R0: Stop the inflow

**Head audited:** OpenHCS `main` at `c86f562e`. **Rules:** [00-RULES.md](00-RULES.md). **First, before any other surface.**

## Why

In the last 24 hours, OpenHCS added code worse than the code it joined: per 1,000 lines, 27 `None` checks against the package's 19, 12 `isinstance` against 7, 6 foreign probes against 4, 2 broad `except` against 1. A quarter of the day's commits described themselves as "owned", "declared", "nominal" or "typed", and several measurably added the debt they described removing. agent-comms and Toad reject those patterns in CI; OpenHCS has nothing that does. Its parity checks, the behavioural contract, run only on pushes to `main`, so 25 numeric performance changes merged within ten minutes were checked only afterwards, together.

## Target

1. **The ratchet on every PR:** agent-comms' packaged `agent-comms-ratchet --root openhcs`, installed as a tool in CI (`uvx --from git+https://github.com/OpenHCSDev/agent-comms agent-comms-ratchet`), never copied. It carries every measure rule 5 lists, including the class-size threshold and, once C0 lands there, string dispatch and type switches.
2. **NRA's R1 detectors on every PR,** scoped to changed files so the scan stays fast: redundant type checks, unmodeled record shapes, and mapping reads that bypass a declared class. The overlay found 199 raw shapes that bypass an existing class; these are the detectors built for exactly that.
3. **Parity on pull requests:** the integration workflow's parity jobs also trigger on `pull_request`, filtered to `processing/`, `interop/cellprofiler/`, `core/` and `formats/`, and are required.
4. **The PR template** from rule 6: persisted formats, and for fixes, the owning declaration the fix changed.

## Open work

The open PRs and active branches are small in production code (the largest is 513 lines); their earlier, larger totals were mostly tests, evidence and benchmarks. `perf-radial-reduction` has already merged (#260). Each remaining piece merges only after the ratchet and, where it touches numeric code, parity; [the index's distribution](01-INDEX.md#distribution-across-new-and-existing-prs) says what each must do first.

## Done when

The ratchet, NRA's changed-file scan and PR parity are required checks on `main`, and the open branches above have passed them.

## Dispatch

> **`ohcs-r0`:** Complete R0 per `docs/refactor/R0-stop-the-inflow.md`. Install the ratchet as a tool, never a copy; make parity run on pull requests; then hold the open branches until they pass.
