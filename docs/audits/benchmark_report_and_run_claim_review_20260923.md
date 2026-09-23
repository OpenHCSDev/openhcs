# Benchmark report and run-claim authority review — 2026-09-23

This review covers the declaration-owned comparison report and the exclusive
first receipt for a new comparison run. It is a documentation claim review, not
a publication-grade timing or equivalence result.

| Page | Diátaxis need | Checked claim and disposition |
| --- | --- | --- |
| `README.md` | Explanation / entry point | The expert report is read-only; a new comparison refuses an occupied destination. Updated the benchmark paragraph without claiming MCP suite submission. |
| `docs/source/appendices/research_impact.rst` | Explanation | A typed report improves inspectability but does not establish scientific equivalence or execution authority. Updated. |
| `docs/source/concepts/module_structure.rst` | Reference | Benchmark report projection belongs to the benchmark extension, not the OpenHCS pipeline job owner. Updated. |
| `docs/source/guide_for_biologists/domain_expert_onboarding.rst` | How-to | A scientist can request the expert report after a reviewed run, but cannot submit or cancel a comparison through that route. Updated. |
| `docs/source/user_guide/mcp_clients.rst` | How-to | Named the expert MCP and CLI report routes, observation warnings, and empty-destination preflight. Updated. |
| `docs/source/architecture/mcp_distribution.rst` | Explanation | The report consumes the typed receipt and observation artifact; first receipt publication is exclusive. Updated. |
| `docs/source/architecture/measurement_equivalence_system.rst` | Explanation | The comparison runner retains its measured-output boundary and now refuses to replace an occupied run directory. Updated. |
| `docs/source/development/extension_workflows.rst` | How-to | Registered CLI commands, typed receipts, and measured pipeline jobs remain the same distinct owners. Re-read; no prose change needed. |

Authority check: `BenchmarkRunInspectionRequest` and `BenchmarkRunReport` are
typed contracts; `BenchmarkControlService` applies the read policy and derives
the report from inspection; `ComparisonRunArtifact.OBSERVATIONS_JSONL` names the
only observation input. The report parses bounded observation records back into
`CellProfilerComparisonObservation`, rejects records outside the receipt's
suite/case/repetition declaration, and does not calculate a matched-concurrency
speedup. `RunBenchmarkCommand` and `run_comparison_suite` both preflight the
destination, and `ComparisonSuiteRunReceipt.write_new` atomically claims the
initial receipt.

Local evidence: 255 related CellProfiler and benchmark control/comparison
tests passed with the CI numeric dependencies; a fresh
current-checkout MCP client discovered `openhcs_report_benchmark_run` on the
expert `full` surface and invoked it against a historical Official30 directory.
That directory has no current typed suite receipt, and the tool correctly
reported the missing receipt instead of promoting its 30 JSONL lines to
validated case outcomes. A fresh Python 3.12 environment installed the
`bc25b8896` OpenHCS wheel, the eight local foundation distributions, and its
MCP dependencies from the offline cache. With no source checkout on its Python
path, a new stdio client reported healthy packaged resources, discovered the
six expert benchmark capabilities, and rendered the typed one-case corrected
Official30 run as one successful equivalent observation with no evidence
warnings. Its native timing cell was blank because that run used a cached
reference, so this is a distribution/inspection proof, not performance
evidence. Suite submission, cancellation, and matched-concurrency publication
remain separate gates for the active benchmark goal.
