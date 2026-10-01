S1: configuration-schema presentation ownership
================================================

Source and integration owner: parent Codex. Audited main:
0c0563e6538af313345391f2dc314270a86933a0. Isolated worktree:
/home/ts/wt/openhcs-config-schema-s1-20261001.

This is one remaining S1 family, not completion of S1 or the full ZIP scope.
Existing PR334 supplies the actual typed framing and renderer mechanism.
Arendt owns PR338 and the generated-command issue339; Darwin owns the separate
H003g runtime repair. Neither source worktree nor frozen blind input is changed.

Observed boundary and required relation
---------------------------------------

Before-source config.py has204 lines,19 get calls and5 isinstance calls.
After-source has141 lines, zero get calls and zero isinstance calls. These are
direct AST/source measurements, not a global architecture proof.

BOUND-2: ConfigSchemaRenderer declares ConfigSchema while reading its fields,
ConfigFieldSchema and ConfigTypeSchema through mappings. BOUND-1: its five type
checks reinterpret values whose schema already states their type. The existing
McpDevToolBatchResponse ingress and McpDevTypedOutputRenderer decode_payload
already descend recursively through the original python-introspect codec.
Extend these actual owners, not a config-specific codec or DTO facade.

Producer ConfigReferenceService -> ConfigSchema -> MCP serialization -> existing
McpDevToolResult framing/output binding -> shared typed renderer -> config field
presentation. Consumers include generated config-schema and generic call.
Configuration lazy/inheritable flags, explicit user default_repr="None", nested
authoring paths and source type inheritance must remain facts of the existing DTOs.
This presentation does not resolve None inheritance or change configurations.

Target and migration closure
-----------------------------

ConfigSchemaRenderer inherits McpDevTypedOutputRenderer and supplies only the
typed render_payload and small presentation helpers. Delete its raw extraction,
per-field validation, envelope rendering, extra render entrypoints and original
JSON fallback. No decoder registry, duplicate store, compatibility wrapper,
consumer subtype/name switches or manually maintained output membership.

Arendt approved two exact shared-owner hooks in this PR: the typed ancestor's
unavailable_summary defaults to its current generic heading; the config member
declares its original config-specific heading. Existing nullable text projection
accepts a keyword-only absent_text with its unchanged default. Config requests
the existing root label through that owner, preserving empty strings as present.
No overriding copied procedure or parsing/replacing rendered text is introduced.
Arendt integrates these hooks normally after merge; no competing339 patch.

New-case experiment: a real ConfigSchema subclass, with one additional declared
fact, reuses ancestor registry/MRO presentation without consumer/registry edits;
decoded object identity and nested typed values are retained. This family does not
have independent overlapping capabilities requiring new MI. Existing shared
ancestor ownership is the intended inheritance, not artificially deep hierarchy.

Tests and guards
-----------------

Family checks exercise generated command and generic call, filtering/bounding,
lazy/inheritable/required/ui-hidden flags, authoring collection paths, nullable
defaults, empty collections, nested typed identities, new subtype reuse, native
transport errors and malformed nested record rejection. A local AST guard forbids
get/first_tool_payload/sequence_of_mappings/getattr/isinstance or a new codec call
in the config leaf. Existing shared boundary owns strict contract validation.

Fixtures now contain the real required server identity and complete declared
transport failure fields; no product fallback is added to tolerate invalid frames.
The old incomplete raw fixtures cannot prove actual installed MCP framing behavior.
All filtering/field assertions and the original unavailable heading remain.

No numerical processing, CellProfiler semantics, external configuration schema,
MCP tool bytes, persisted result format or durable store changes. Compact human
rendering is internal but existing observable behavior is preserved at completion.
No migrations, global installs or skill synchronization changes.

Source evidence and remaining acceptance
-----------------------------------------

Existing interpreter/dependencies only, one CPU, <=512MiB combined process-group
RSS and60s per shard. Local setup.py build_ext --inplace3.46s203.28MiB. Initial
test collection failed because own native extensions were not built; retained.
Initial typed tests exposed incomplete historical fixtures, retained and aligned
to actual nominal contracts rather than weakening the production boundary.

Four-family source roster:49PASS,7.51s wall273.86MiB peak. Two warnings report
disabled optional asyncio pytest plugin configuration; no tests are skipped.
The unchanged original R0 rejected the first draft's newly exposed foreign
absence probe at payload.path_prefix. No guard was changed or suppressed:
nullable text policy now belongs to the existing shared owner with a configurable
absent label. Added controls cover None, empty text, zero, false, default and
custom labels; shared generic headings and config-specific headings stay exact.

Receipt logs currently in owned scratch:
/home/ts/.cache/agent-scratch/mcp-contract-fixtures-340-20261001/config-*.log
These will be retained persistently before scratch retirement. R0/full-context R1
and installed real config-schema/generic-call acceptance are NOT yet assessed.

Done when: config raw readers and repeated validation are deleted; existing
diagnostic heading preserved through the shared owner; family and new-case checks,
unchanged R0/R1 evidence and installed user entrypoint validated at the final head.
Do not claim a passed complete architecture audit from the local AST guard.
