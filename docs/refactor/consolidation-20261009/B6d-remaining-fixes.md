# B6d: the fixes from B6 that main still needs

B6 (#1195) repaired main's CI in one branch that also reformatted 412 files and re-pinned the documentation audits. #1212 took its E1 boundary fix and #1214 its trigger restructuring. This is the rest: each fix below changes behaviour. Formatting commits, the ratchet mixin moves, the documentation re-pins, the workflow edits and the pyqt-reactive pin are not carried.

## Fixes

Tests named here fail on main `ae6ddace5` and pass on this branch unless marked otherwise.

| Fix | Cause | Evidence |
|---|---|---|
| Requestless UI-bridge operations pass the connection by keyword | the connection landed in the request slot | `test_capabilities.py::test_requestless_ui_bridge_capability_passes_connection_as_connection` |
| A batch stopped while compiling ends cancelled | the stop surfaced as an execution failure | `test_execution_control_stop_during_compile.py` |
| Metadata document targets follow the backend's declaration | a virtual backend (OMERO) got a local metadata document | `test_function_outputs.py::test_metadata_document_targets_follow_backend_declaration` |
| Catalog leaves out modules whose distributions the package markers exclude | Intel macOS excludes `openhcs-basicpy` but the catalog imported its module | `test_library_registry_discovery.py` (7 cases) |
| Cache preparation uses `os.cpu_count()` where there is no affinity API | macOS prepared the kernel cache serially | `test_preparation_admission.py::test_platform_without_affinity_admits_its_online_cpus` |
| Scalar components are reduced per pixel group | contributors were pooled across runtime planes, dropping `site` | `test_aggregate_source_scope.py::test_axis_varying_between_runtime_planes_is_kept_not_reduced` |
| The one-plane label projection belongs to every plane label mode | it lived only on `MatchImageStackLabels` | `test_singleton_rgb_label_invocation_477.py` (`SliceAlignedLabels` case) |
| Benchmark adapter keeps the imported config's inheritance and declared output policy | `dataclasses.replace` froze unset fields; a results path was forced | `test_openhcs_adapter.py::test_openhcs_adapter_preserves_declared_main_flow_output_policy` |
| Packaged knowledge recipes are placed by case name within a path budget | installed paths exceeded Windows MAX_PATH | `test_build_mcp_knowledge_assets.py` (does not import on main) |
| GUI smoke waits for the window's endpoint start, reports the status name, and gives the bridge connection its transport config | the catalog was read before the endpoint existed; the result held a class; U4 moved the connection spec to formbridge, where `transport_endpoint` takes the config | `test_smoke_installed_gui.py` (does not import on main); `smoke_local.sh` GUI step |
| Unit session creates its `QApplication` first; sibling test modules import through `tests` | an MCP transport created a `QCoreApplication`; bare imports fail under importlib mode | `test_ci_import_guards.py` guards the imports; it passes on main once the test files are fixed, so no production test fails on main |
| STEP_INPUT filters match stored source paths | they matched virtual workspace names | no touched local test fails on main; B6 found it in the backend-microscope CI jobs |
| Passthrough outputs keep their producer's filename qualifier | sibling surfaces merged into one file | same |
| BaSiC reads metadata through `ImagePayload.of` | `.metadata` was read off plain arrays | not shown failing on main locally; B6 found it in CI |
| Dataset rows carry the finished execution's error; demo reads `ViewerType.value` | the installed demo failed without a reason | installed demo job only |
| Measured-run silence is counted from `begin_run` | server startup time counted as execution silence | not isolated by a local test |
| `mahotas` is a core dependency | core catalog modules import it; it sat in an extra | packaging; python-314 job |
| MCP smoke sends `partition_values` | G2 renamed `wells` | wheel-integration job only |
| Windows: granularity accepts `'L'` uint32; custom-function sources are written as bytes; Ctrl+Break stops the CLI; dataset writability is probed by creating a file; `.gitattributes` keeps committed bytes; test process reaping skips process groups | each is a Windows-only difference | Windows jobs only; the POSIX paths are run by the touched tests |

## Ratchet

`OpenHCSMainWindow` and `PatternGroupExecutionRequest` are at their size budget. The window's four theme methods had no caller and are deleted (**unused**; guarded in `test_dead_ui_code_guards.py`). The passthrough helpers sit on `PatternGroupExecutionScope`.

## Done when

Touched tests pass, `smoke_local.sh` prints `smoke rc=0` with the GUI step, `guardrails_local.sh` ends `guardrails rc=0`, and the 30-workflow parity check passes.
