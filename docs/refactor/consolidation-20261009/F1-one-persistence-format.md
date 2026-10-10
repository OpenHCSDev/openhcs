# F1: One persistence format

**Head audited:** `openhcs` `main` at `1c1059867` (#1172). **Rules:** [00-RULES.md](00-RULES.md). **Step 2.**
*Uses:* the pycodify document path already behind every code editor: `PipelineDocumentCodec` (renamed from `PipelineDocumentAuthority`, rule 1b), `FunctionStepDocumentCodec` (renamed from `FunctionStepDocumentAuthority`), pyqt-reactive `FunctionPatternCodeDocumentService`. *Builds:* nothing new.

## What is wrong

**User state is saved two ways: as generated Python through the code editors, and as dill pickles through three file controllers that restate the same save and load (IMPL-3, a second mechanism for one relation).** The owner has used only `.py` and `.cppipe` pipelines for months and has no pickle files to keep (decision G1-Q1, extended here).

- `pyqt_gui/widgets/pipeline_editor.py:957-1037` `load_pipeline_from_file` unpickles a step list (`dill.load`, :967); `save_pipeline_to_file` (:1039-1054) pickles `pipeline_steps` and drops the plate's `PipelineConfig`. The menu dialogs (`services/main_window_workflows.py:771-805`) offer `*.func` and default to `pipeline.func`. `main.py:1384-1397` branches `.py` vs "pickled files" a second time for the agent load path.
- `pyqt_gui/widgets/step_parameter_editor.py:73-181` `StepSettingsDialogRequest` + `StepSettingsFileController` pickle `ObjectState.get_current_values()` to `.step` files (`dill.load` :149, `dill.dump` :172). No button reaches it: the action bar holds only "Code".
- `ui/shared/pattern_file_service.py` (215 lines) `PatternFileService` pickles patterns to `.func` files. Nothing imports it.
- The step and pattern code editors already save and open `.py` through `SimpleCodeEditor._save_as/_open_file`; those are the real persistence path for step settings and patterns.
- Leftovers of the pickle formats: `core/path_cache.py` keys `FUNCTION_PATTERNS` (.func), `PIPELINE_FILES` (.pipeline), `STEP_SETTINGS` (.step), `DEBUG_FILES` (.pkl), plus six never-used "future use" keys; `service_adapter.show_cached_file_dialog` (only caller: the step controller); `launch.py` lists dill as "Pipeline serialization"; a test that a legacy UI-config pickle is ignored.
- `tools/cutover/g1_axis_family.py`, `tests/unit/test_g1_cutover_tool.py`, `tests/fixtures/g1_cutover/`: the owner confirmed nothing is left to convert (G1-Q1 closed).

Other pickle uses in `openhcs/`, classified:

| Site | Is it user persistence? |
|---|---|
| `core/orchestrator/worker_execution.py`, `runtime/viewer_protocol.py`, `runtime/napari_viewer_server.py`, `agent/services/viewer_window_service.py`, `pyqt_gui/services/ui_bridge_server.py`, `omero/.../views.py` | No: ZMQ/multiprocessing transport, in memory |
| `core/pipeline/compiler.py:1723` (dill) | No: diagnostic dump of compiled worker plans (`CompilationDebugConfig`), runtime state |
| `processing/backends/cellprofiler/zernike.py:592` | No: derived cache, reset on install |
| `runtime/zmq_execution_observation.py:107-223` | No: per-execution observation/outcome export read back by the client of the same run (runtime) |
| `core/equivalence/cells.py` | No: `pickle.dumps` feeds a digest, nothing is stored |
| `core/image_file_serialization.py` | No: `np.load/save(allow_pickle=False)` |
| `pyqt_gui/services/desktop_update.py:491,615` → ObjectState `save_history_to_file`/`load_history_from_file` (dill) | Not durable: a one-shot restart handoff written by the closing process and consumed by the next; declarations in the same session are already `.py`. Pickling lives in ObjectState (L6 owns the library); recorded there, not edited here |

## Target

- A pipeline file is the pipeline code document: save writes `code_document_source()` (config plus steps, the same text the code editor shows); load of `.py` runs `_handle_edited_code`, `.cppipe` runs the CellProfiler importer, anything else raises. `main.py`'s agent load path calls `load_pipeline_from_file` instead of re-branching.
- Step settings and patterns persist only through their code editors (`FunctionStepCodeDocumentDriver`, `FunctionPatternCodeDocumentService`) and the editor's Save/Open `.py`.
- **Deleted:** both pickle branches in `pipeline_editor.py`; `StepSettingsDialogRequest`, `StepSettingsFileController`, `load_step_settings`, `save_step_settings`; `ui/shared/pattern_file_service.py`; `show_cached_file_dialog`; every path-cache key but `PLATE_IMPORT` (the pickle-format keys and nine never-read ones), the module's "backward compatibility alias" functions and `get_cached_path`, and the `pyqt_gui/utils` re-export package nothing imports; `*.func` dialog filters; the dill "Pipeline serialization" entry; the legacy-pickle UI-config test; the G1 cutover tool, test and fixtures.
- Rule 1b: `PipelineDocumentAuthority` → `PipelineDocumentCodec`, `FunctionStepDocumentAuthority` → `FunctionStepDocumentCodec`, with every caller (71 files), and the "canonical" docstrings in the touched modules.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| `.func`/`.pipeline` pickled pipelines, `.step` pickles, pickled `.func` patterns | durable, deprecated by the owner | not read; none exist |
| `.py` pipelines, config documents | durable | unchanged |
| `path_cache.json` entries for deleted keys | runtime preference | ignored (keys no longer looked up) |

## Guards

`tests/unit/pyqt_gui/test_one_persistence_format.py`:
- no `pickle`/`dill` import or `dump`/`load` call anywhere under `openhcs/pyqt_gui/` or `openhcs/ui/shared/` except the named ZMQ transport module (`ui_bridge_server.py`, `dumps` only);
- no `.func`, `.pipeline`, `.step` dialog filter strings in those trees;
- `PathCacheKey` has no pickle-format key.

## Tests

One round trip per persisted kind, offscreen: pipeline (widget save → new widget load → identical rendered source), step settings (step driver source → `.py` → apply → identical source), pattern (pattern document → `.py` → `pattern_from_source` → equal pattern). Deleted: `test_g1_cutover_tool.py`, the legacy-pickle UI-config test.

## New-case experiments

Today a new persisted editor kind needs a code document *and* a pickle controller, dialog request, cache key and filter. After: its code document only; the code editor's Save/Open supplies the file.

## Done when

The guards pass; the three round trips pass; no pickle or dill save/load remains in GUI persistence; the cutover tool is gone.

## Leftovers recorded for other surfaces

- **L4:** pyqt-reactive `core/path_cache.py` still restates `FUNCTION_PATTERNS`, `PIPELINE_FILES`, `STEP_SETTINGS`, `DEBUG_FILES` and the browser keys, used by `EnhancedPathWidget` behaviours; `openhcs/core/path_cache.py` is a copy of that module. One open key family in the library should replace both.
- **L6:** ObjectState history persistence is dill; the restart handoff could store history as a document like the declarations beside it.
- pyqt-reactive `AbstractManagerWidget.handle_code_execution_error` docstring still describes old-format migration (L4).
- Rule 1b, not renamed here: `FunctionStepTransportAuthority` (153 sites) and the sibling `PlateManagerCodeDocumentAuthority`/`ConfigDocumentAuthority`; whichever surface next touches them renames them the same way (`…Codec`).
- `openhcs/core/xdg_paths.py:181` still migrates `path_cache.json` from a legacy directory (L4, with the path cache).
