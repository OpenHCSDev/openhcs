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
Final production config.py has145 lines, zero get calls and zero isinstance calls. These are
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
These are retained persistently in the adjacent receipt archive before scratch
retirement. Final source50PASS8.53s wall272.32MiB. Original packaged R0 at
main0c0563e ->684d0f36a PASS13.66s83.95MiB, no measure increases or exceptions.
Ruff passes on the config leaf and changed tests; shared renderer has six
pre-existing UP037 quoted-annotation warnings outside the five added/three
removed lines. No unrelated lint rewrite is included.

Installed acceptance at production head684d0f36a
-----------------------------------------------

Built the actual wheel without isolation/dependency downloads in6.48s250.09MiB:
openhcs-0.8.7-cp311-abi3-linux_x86_64.whl, SHA256
c062a06ce1ac5781858238294e4f8100d9effd2455a03b6aee7e0395d41ed838.
Fresh own venv at acceptance/venv, sharing existing read-only dependency paths.
No global, existing candidate, frozen blind environment or harness changed.
Installed package origin is acceptance/venv/lib/python3.12/site-packages/openhcs;
both changed production files compare byte-for-byte with the reviewed source.

Nonblocking validation.lock admitted a single fresh stdio shell, one CPU/native
thread pools1, own XDG cache, DISPLAY91, no native execution or viewer launch.
Health reports0.8.7, packaged_resources_ready, no stale source or reconnect flag.
First-use context plus generated config-schema pipeline --contains lazy --limit3
and generic call describe_config_schema complete0 in13.62s,537.81MiB peak.
Pipeline schema has27 real reflected fields;20 match lazy,3 shown; generic call
shows20 of27. Lazy flags, inherited fields, source authoring and nominal type
inheritance are visible through the actual installed user entrypoint.

A separate fresh shell read health, first_use, pipeline context, capability search,
nested napari_display_config schema and an intentional invalid-schema control.
Nested schema8 fields/2 shown. Invalid schema retains the original
Config schema: unavailable heading plus native mcp_tool_failed diagnostic, and
the shared typed boundary also records why that error receipt is not ConfigSchema.
Expected exit1,10.73s537.27MiB. These are read-only CLI acceptance, not biological
analysis, viewer QA or evidence of resolved inherited configuration values.

Initial shell JSON quoting error caused local argparse exit2 after healthy MCP;
retained unchanged. Original process816261 exited before corrected requests.
Successful/read-only shell processes818734 and823412 are gone; validation.lock
released. No timeout restart, scientific candidate replay or foreign process kill.

Full-context R1 status remains separately recorded. Original check first stopped
before analysis because main's PolyStore object database lacked recorded commit
84f322e; fetched that exact existing fork Git object only, without checkout,
dependency installation or source edits. All eight recorded root dependency
objects then available. A second unchanged original check uses pinned NRA0844525,
original roots openhcs/scripts/benchmark and all recorded dependency source,
bounded55s512MiB. Its outcome is not replaced by the R0/local AST result.

Actual second R1 outcome: INCOMPLETE. Source scan reaches its original deadline
inside parse_python_module at55.000s/55.000s. No baseline/head assessment or
finding comparison was produced. No complete architecture-audit pass is claimed.
The administrative resource supervisor also hit a disappearing temporary
directory during scan cleanup, so no final peak-RSS summary exists for that
attempt; its original traceback is retained. The owned supervisor now tolerates
file disappearance during output retirement. The R1 child and supervisor are
terminal; no orphan scan is running. No rerun with weakened roots/detectors,
increased timeout or suppression is used to turn this into a pass.

Locally/live-qualified shipment and full-scope completion remain distinct.
Source/new-case checks, original R0 and installed affected CLI path are validated;
full-context R1 remains incomplete and is retained as unfinished full-goal scope.
No numeric processing changed, so no new CellProfiler numerical-parity assertion
is made. Hosted CI is not a waiting gate under the explicit owner override.
