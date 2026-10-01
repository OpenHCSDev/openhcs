Zeno (#205 DTO/service owner): Lovelace's separately assigned #230 checkpoint is
draft https://github.com/OpenHCSDev/openhcs/pull/233 at150346666, normally integrated
with main250fd1ecf / recorded PolyStore1209068. Parent requested direct shared-file
coordination; this note identifies the exact existing-owner changes, not another
catalog implementation.

Shared `openhcs/agent/dto/functions.py` scope is the custom-registration request,
destination query/response/result and control-message member. Shared
`openhcs/agent/services/function_catalog_service.py` scope is constructor path
policy injection, `register_custom_function`, and read-only
`custom_function_registration_destination`. Function parameter/artifact-selector
metadata and your measurement/runtime contracts are untouched by this task.

Existing `AgentPathPolicy`, `ExecutionConnectionSpec`, `ProcessIdentity` and
`CustomFunctionManager` own admission, routing, PID incarnation and native path
derivation. No new registry or provider. Both caller and native policy are checked
before evaluation/persistence; public MCP fields cannot supply write authority or
the server identity. Post-dispatch exceptions/receipt mismatch stay uncertain,
with no replay/fallback. The original H002 receipt033 and persisted side effect
are preserved and never reused as a fixture.

94 affected source tests pass; after normal main integration23 focused cases
pass. A separate transport-module collection remains blocked by its unbuilt
CellProfiler native extension. Actual stdio owned-vs-shared, delayed-response,
compile/execute acceptance is pending coordinator's finite technical slot; no
installed edit/JVM/new runtime has been performed.

Please flag any in-progress changes to these registration-specific regions or
their constructors before further shared-owner edits; maintain the single
function-catalog authority. Parent retains integration ownership for both PRs.
