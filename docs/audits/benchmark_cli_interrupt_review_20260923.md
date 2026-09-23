# Measured-run CLI interruption authority review

The `run-measured` command now obtains the ordinary accepted job before waiting.
`ExecutionSessionService.wait_job` owns the bounded wait over that retained job;
the CLI invokes the same service's `cancel_job` on Ctrl-C or a nonterminal wait
timeout. The CLI reports the cancellation result and writes no success receipt
on either path. An unapplied cancellation is not represented as a stopped job.

I re-read the complete dependent README and these active pages against the
changed CLI, execution service, and focused tests: `mcp_distribution.rst`,
`progress_runtime_projection_system.rst`,
`zmq_execution_service_extracted.rst`, `extension_workflows.rst`,
`mcp_development.rst`, `research_impact.rst`, `module_structure.rst`,
`domain_expert_onboarding.rst`, and `mcp_clients.rst`. The existing claims about
ordinary job ownership, progress, cancellation, benchmark inspection, and
scientific limits remain supported. The MCP client how-to gained the practical
Ctrl-C/timeout instruction; the other pages needed only authority-digest
refreshes. This is a targeted review, not a new scientific benchmark.

Local evidence: 143 affected unit and live ZMQ integration tests passed,
including the accepted-job wait, both CLI cancellation exits, and the live
ordinary source-backed CLI success path. `scripts/validate_docs.py` passed on
the edited MCP client page. Exact-head CI remains a separate publication gate.
