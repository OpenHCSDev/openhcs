# Outcome-only measured-run documentation review (2026-09-22)

The ordinary execution service gained a typed value-or-outcome observation
scope. The benchmark wrapper remains a consumer of ordinary submission,
status, cancellation, and completed results; it is not a second execution
engine. I re-read the complete affected pages against the changed service,
server, wrapper, receipt, tests, and benchmark CLI before updating their audit
digests. The following checks follow each page's existing Diátaxis need.

| Page | Need and review result |
| --- | --- |
| `architecture/external_integrations_overview.rst` | Explanation: the changed server hook still leaves transport/lifecycle with ZMQRuntime and microscopy execution policy with OpenHCS. No prose change. |
| `architecture/abstraction_lattices.rst` | Explanation: capability metadata still comes from the nominal declaration registry; the new scope is an ordinary runtime enum projected through that request, not a parallel benchmark catalogue. No prose change. |
| `architecture/mcp_distribution.rst` | Explanation: clarified that measured receipts validate either a value or outcome export; outcome-only is not value equivalence. |
| `architecture/measurement_equivalence_system.rst` | Explanation: separated full-value comparison evidence from per-axis outcome evidence and stated the declared axis-count check. |
| `architecture/streaming_boundary_and_wrappers.rst` | Explanation: server export changes do not alter viewer registration, streaming, or settlement ownership. No prose change. |
| `architecture/progress_runtime_projection_system.rst` | Explanation: the agent still projects the retained client's ZMQRuntime-owned progress observation, independently of the chosen runtime export scope. No prose change. |
| `architecture/zmq_execution_service_extracted.rst` | Reference: named the typed scope and its parent-retention consequence at the ordinary auxiliary boundary. |
| `development/mcp_development.rst` | How-to: documented the `values` default, `outcomes` choice, and export-path requirement. |
| `development/extension_workflows.rst` | How-to: specified that a measured receipt consumes a validated value or outcome export rather than assuming retained arrays. |
| `README.md` | Explanation: added the outcome-only CLI choice without suggesting equivalence or performance proof. |
| `appendices/research_impact.rst` | Explanation: the new observation choice is still provenance, not scientific or performance validation. No prose change. |
| `concepts/module_structure.rst` | Reference: benchmark still owns comparison contracts and reporting, while normal runtime owns execution. No prose change. |
| `guide_for_biologists/domain_expert_onboarding.rst` | How-to: read-only comparison inspection and its scientific caveat remain correct. No prose change. |
| `user_guide/mcp_clients.rst` | How-to: clarified value/outcome validation and documented the shared CLI/MCP scope choice near execution guidance. |

Local checks for the scope wiring: the focused service and MCP-schema tests and
the live synthetic ZMQ `run-measured --observation-scope outcomes` test passed.
The previous-head Documentation job exposed stale authority hashes; this
review closes that ledger gap. A fresh installed-wheel MCP/CLI run and the
new-head CI are separate gates and are not claimed here.
