Local MCP argument errors and session recovery
=============================================

Owner: parent integration thread, issue283. Base merged main5a56ee5d.
This is a concrete CLI correction, not completion of the archive's wider S1
DTO work or permission to replay an uncertain scientific request.

Original installed viewer-client evidence misclassified malformed local JSON
as mcp_transport_failed before tool dispatch. Expanded persistent-client
regressions reproduce four failures with the original source: malformed JSON,
array, null and scalar. The existing missing-port control passes. Original
XML remains in the parent ledger as issue283-original-failure-20260930.xml.

Ownership correction (BOUND-1/2)
-------------------------------

The existing parse_json_object boundary projects malformed/non-object JSON
through McpDevCliUsageError. That existing type composes argparse.ArgumentTypeError
and ValueError so argparse preserves the informative diagnostic without losing
the existing local-validation catch contract. No exception-text classification,
new parser, registry, timeout increase or broad ValueError transport catch.

CallCommandSpec declares this converter on its --arguments option. Both dispatch
and rendering consume the same decoded Namespace field. Its two replaced JSON
reads are deleted. Valid values still use the external JSON-object syntax;
malformed values get usage exit2 before transport dispatch. Other optional JSON
argument consumers retain the same original boundary owner.

Executed evidence
-----------------

Thirty-one persistent-client, actual transport-failure and config-renderer
regressions pass in11.36s, zero skips/deselections. Existing initialized-once
coverage now includes a raw call and checks one argument decode across dispatch
and rendering. Each local-error case asserts zero tool dispatch. Real transport
failure coverage stays intact. Original intermediate assertion failures remain
separate from the passing final XML, issue283-final-acceptance-20260930.xml.

The affected installed user entrypoint runs outside source with PYTHONPATH unset
and one real nonresident MCP. Its continuous shell journey is health, malformed
raw call, non-object raw call, valid raw call, health. All three successful
responses are healthy on the same child3328944 and installed source tree.
Both invalid inputs report specific CLI usage diagnostics on stderr, with no
transport-failure payload. Aggregate exit2 is expected for local usage errors;
the later valid call and health succeed without restart/reconnection. Ordinary
observations remain10s. No viewer/scientific execution or external provider.

Durable actual response and diagnostics:
parent ledger issue283-installed-shell-20260930.jsonl and .stderr.
Source tests and this live diagnostic are not biological acceptance, full NRA
proof, all dependency-source alignment, or a passing complete ZIP refactor.
Retained H002 history, frozen candidates and held-out/reference data unchanged.
