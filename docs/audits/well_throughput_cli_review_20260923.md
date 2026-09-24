# Well-throughput CLI authority review

The registered `run-well-throughput` command now projects the existing
manifest-owned modes and worker start method into the ordinary measured-pipeline
wrapper. It offers a read-only plan, refuses ambiguous mode requests and
unrequested output-directory reuse, and exits non-zero when an observation row
records failure. It does not add a second execution or job-status authority.

I re-read the complete dependent `README.md` and active pages
`mcp_distribution.rst`, `extension_workflows.rst`, `research_impact.rst`,
`module_structure.rst`, `domain_expert_onboarding.rst`, and `mcp_clients.rst`
against the changed CLI and its registered-command tests. Their claims about
benchmark command registration, ordinary execution ownership, MCP's read-only
inspection boundary, and the limits of a receipt remain supported. The
task-specific how-to lives in `benchmark/manifests/README.md`; these seven pages
do not need a second copy of that procedure.

Local evidence: 59 affected unit tests and two live ZMQ integration tests
passed. A source-backed `ExamplePercentPositive` probe used eight virtual wells
and two workers through the installed development CLI; its receipt reports
eight successful axes and two verified source snapshots. This is infrastructure
validation, not a repeat of the archived Figure 5 workload or a native
CellProfiler comparison. The focused manifest how-to validator passed. The
fresh installed-wheel and full CI gates remain separate.
