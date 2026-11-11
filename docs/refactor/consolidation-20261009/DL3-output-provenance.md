# DL3: an output dataset says what produced it

Branch `refactor/DL3-output-provenance`. Gap 6 of `D1-cellpose-n2v2-custom-functions.md` (PR #1230).

**Lands after DL1 and after four library releases.** Two pins cannot be installed from PyPI yet:

- `python-introspect>=0.3.0,<0.4` (set in `pyproject.toml`; 0.3.0 is on PyPI). ObjectState,
  formbridge, pyqt-reactive and zmqruntime all declare `python-introspect<0.3`, so the resolver
  refuses this branch until each of them releases with the bound widened to `<0.4`. Their
  submodules run against 0.3.0 here (formbridge and ObjectState suites: no failure; zmqruntime: two
  IPC transport tests fail with `EOFError` in `multiprocessing`, not in the codec; pyqt-reactive
  not run).
- PolyStore: the storage part is PolyStore PR OpenHCSDev/PolyStore#41, to be released as **0.6.4**
  (0.6.3 is the arraybridge 0.5.0 migration and requires `arraybridge>=0.5.0,<0.6`). OpenHCS main
  is on arraybridge 0.4.1 until `refactor/DL1-device-and-memory-types` merges. Until then the
  submodule `external/PolyStore` points at `5301d35` (branch `feat/file-content-identity`, still
  based on PolyStore 0.6.1 and still titled 0.6.3) and `pyproject.toml` still says
  `polystore>=0.6.3,<0.7`, which is wrong. At that time set: `polystore>=0.6.4,<0.7`,
  `arraybridge>=0.5.0,<0.6`, submodule at the 0.6.4 tag.

**Current state: see "Third hand-off" at the end.** Earlier sections are the first two agents';
where they describe a union decoded by its fields, one metadata transaction, or
`OpenHCSMetadataTarget.saved_path_producers`, the third hand-off replaces them.

## What is wrong (measured on `origin/main` at `1b5fe99f5`)

- `openhcs_metadata.json` of an output dataset has no pipeline, function, parameter, source-hash
  or model-hash key (keys of a real output: `subdirectories.<dir>.{workspace_mapping,
  source_metadata, source_projection, image_files, ...}`; `OpenHCSMetadataFields`,
  `openhcs/core/virtual_workspace_metadata.py:325`).
- The pipeline code that reaches the server is rendered with `clean_mode=True`
  (`openhcs/core/pipeline_document.py:96`); function kwargs equal to the signature default are
  dropped (`openhcs/serialization/pycodify_formatters.py:150`). No non-GUI caller passes `False`.
- A declared input file is resolved to an absolute path and checked to exist
  (`CompilationPathResolver.resolve`, `openhcs/core/pipeline/compilation_session.py:102`); no
  content identity is taken. PolyStore hashes only to verify a caller-supplied hash
  (`DataSource.read_verified_source_bytes`, `external/PolyStore/src/polystore/base.py:366`).
- Config resolution already returns, per field, the scope and class that supplied the value
  (`ObjectState.resolve_saved_object`, used at `compiler.py:923`), and
  `ResolvedPipelineDefinition.step_provenance` keeps it for steps. The compiler reads one field of
  it (`compiler.py:1727`) and the orchestrator discards it for the pipeline config
  (`orchestrator.py:1057`). Nothing writes it out.
- The producer of an output is stated in exactly one typed place:
  `CompiledStepPlan.producer_identity(...)` (`compiled_step_plan.py:386`) builds a
  `StreamProducerIdentity` (step name, pipeline position, step scope id, output kind and key). It is
  sent with every viewer item (`viewer_transport.py:343`). On disk only its `output_key` survives
  (`function_outputs.py:869`), plus a `_step<N>` token in artifact file names
  (`path_planner.py:2289`). Measurement tables, ROI archives and label images are not listed in the
  metadata document at all.
- Function identity: `FunctionMetadata.composite_key` (`registry:name`); the library version is
  known per registry only (`LibraryRegistryBase.get_library_version`); a custom function's source
  hash is stamped on the callable (`declaration_revision`) but its text is not kept with it.

## Design

Standard used: P10 Definition 2.1(c) and Proposition 6.1 (the output carries the declaration that
produced it), P9 Theorem 5.3 (a log or private attribute does not make the source recoverable; it
has to be in the declared output), P9 "Several fact versions" (evidence that crosses versions
carries the version), P9 "Only executed, contract-guaranteed channels count" (always written, no
opt-in), P9 Theorem 5.5 (no parallel side table once the record determines the source).

**One record, one writer, one time.** The compiler builds a `RunRecord` for each compilation, from
the facts only it holds, and puts it on the `CompiledExecutionBundle`. The parent process fills in
the content of declared input files when execution starts, and the existing single writer of the
output dataset's metadata, `OpenHCSMetadataTarget.finalize_completed_dataset` (parent process, one
locked transaction per `openhcs_metadata.json`, also on failure), stores it in that document:

```
openhcs_metadata.json
  subdirectories: {...}                      (unchanged)
  run_records:   {<record id>: RunRecord}    record id = sha256 of the record's canonical JSON
  produced_files: {<path relative to dataset root>: {"run_record": <id>, "producer": {...}}}
```

A record no file refers to any more is dropped in the same transaction, so a dataset written twice
keeps exactly the records its files need.

**What the record holds (sufficient to re-run).**
- `pipeline_code`: the pipeline document rendered complete (`clean_mode=False`: every function
  parameter and every stored config field is written). `global_config_code`: the saved global
  config rendered the same way. These are the *stored documents*; rebuilding executes them.
- `configuration`: the *resolved* configuration, one entry per leaf field of the effective config
  and of each step: the value (as its Python expression, from pycodify) and its source: the scope
  id and class ObjectState reported, or "set here" when the object itself holds the value. This is
  a different read kind from the document and is kept beside it, never merged into it.
- `software`: OpenHCS version, Python version, platform.
- `steps[]`: name, pipeline position, step scope id (the two fields a producer identity carries),
  declared input and output memory type, the assigned device per framework, and `functions[]`.
- `functions[]`: identity (below), `parameters` and `declared_files`.
- `custom_sources`: `{sha256: source text}`, each text once.

**Function identity is content.** The function reference family answers it
(`FunctionReference.identity_record`): the registry key or import path, the distribution and version
of the module that defines the function, and the distributions and versions of the modules that
module imports (this is where Cellpose's version comes from for a custom function: its source's
imports). A custom function adds the sha256 of its source; the text is stored once under
`custom_sources`. The text is kept on the source's own namespace object
(`CustomFunctionSourceNamespace`), which already owns the hash.

**Defaults are recorded.** Each parameter of the function's signature appears in `parameters` with
its effective value and a source: `pipeline` (written in the pipeline), `function_default` (taken
from the signature of this function at the recorded version), or `run_time` (supplied by the
platform: an artifact input, a bound config value). The source is a small family of classes; its
JSON `kind` is derived from them. The editable pipeline the user saves is not changed: it stays
concise (`clean_mode=True`). Only the record's copy is rendered complete.

**Declared files are identified by the storage layer.** PolyStore gains
`DataSource.file_content(path) -> FileContent`, a family: `HashedFileContent(sha256, size_bytes)`
or `UnhashedFileContent(reason)`; `FileManager.file_content(path, backend)` delegates to the
backend. The path declaration family says what its kind needs
(`DatasetPathDeclaration.content_at_run_start`): an input file is hashed; an input directory, an
output file and an output directory are recorded as not hashed, each with its reason. Hashing
happens once per file per run, in the parent process when execution starts (not at compile: a
compiled plan can be executed later, and the bytes that matter are the ones the run reads). At
the end of the run the writer asks again for size and modification time; a file that changed
during the run is recorded as `changed_during_run`. Functions hash nothing.

Cost, measured here on a 1 GiB file (`.claude/scratch/hashcost.py`, NVMe, CPU with SHA
extensions): sha256 0.58 s with the file in the page cache, 2.15 s after dropping it; blake2b
1.03 s, md5 1.22 s. That is cheap enough to be always on, so there is no switch. A backend with no
physical file answers `UnhashedFileContent` with its reason; the record never omits the entry.

**Per-output linkage is the existing producer identity, written down.** No second linkage: the
`StreamProducerIdentity` a viewer item already carries is the value stored under
`produced_files[path].producer`. Workers already report what they saved
(`StepExecutionObservation`); that report gains the producer of each saved path, taken from the
same two calls the streaming path uses (`producer_identity_for_main_flow`,
`producer_identity_for_artifact`). The reader matches a producer to its step by step scope id and
pipeline position. A measurement row is linked through its table file; a viewer item through the
identity it arrived with. The `_step<N>` file-name token is not read by anything here.

**One reader.** `RunRecord.for_dataset(root)`, `RunRecord.for_output_file(path)` (walks up to the
dataset's metadata document; returns the record and the step) and `RunRecord.rebuild()` (registers
the recorded custom sources after checking their hashes, executes the two documents, returns the
pipeline document and global config). The agent capability `openhcs_read_run_record` (MCP tool and
generated CLI command) wraps the same calls.

**Dependencies on sibling branches.**
- DL1 (device and memory types): the device is read from `CompiledStepPlan.device_assignment`, the
  place it is stated at this branch point. If DL1 moves or extends that statement (CPU devices,
  conversions), the record follows by reading the new one.
- DL2 (declared files between steps): an input file an earlier step of the same run writes does
  not exist when the run starts. At this branch point compile rejects that pipeline; when DL2
  lands, such a file must be hashed after its producer finishes. `content_at_run_start` is the
  single place that decision is made.

## Guards and tests

Unit (`tests/unit/test_run_record.py`): default parameters appear with `function_default`; a custom
function's record changes when its body changes and its name does not; a declared input file is
hashed by the file manager and a declared output file is recorded as not hashed with a reason; the
resolved configuration names the scope and class of an inherited value; the record id is stable
for equal input; a file with no entry is reported as unrecorded, not guessed from its name.
Integration (`tests/integration/test_run_record_round_trip.py`): run a small pipeline, read the
record from one output file, rebuild, run again, compare outputs byte for byte.

## Done when

The Cellpose example leaves a record with the custom source hash, every parameter, Cellpose's
version and the device; the N2V2 denoise example records the model file's hash; gates pass.

## Progress notes

**Wired (commit `c2d689e61`).** `CompiledExecutionBundle.run_declaration` (required; built in
`compile_pipelines` before `_resolve_pipeline_once`, step values added after it; pickles with the
bundle). `StepExecutionObservation.producer_by_saved_path`, filled by
`OpenHCSMetadataTarget.saved_path_producers` at the two places a step's observation is built.
`execute_bundle_request` calls `RunRecord.at_run_start` before workers exist and passes the record
to `finalize_completed_dataset`; `reconcile_completed_dataset` writes it inside its one `update`.
A dataset root that received only non-image files gets a document; a document the run saved
nothing under (the input plate) is left untouched. The real ZMQ journey writes a record (59 kB for
one step, of which 246 installed distributions are most).

**What the design had wrong, and what was done instead.**
- `clean_mode=False` did not write a parameter the pipeline leaves out (it only stopped dropping
  written ones). Complete rendering now adds the signature default of every parameter of every
  pattern function (`with_every_parameter_written`, `pycodify_formatters.py`), except parameters
  the platform supplies when it calls the function (artifact inputs, `slice_by_slice`,
  `dtype_config`): writing their signature default would replace the supplied value.
- Two default kinds had no formatter and would have stopped compilation (`range` in
  `skimage:filters.frangi`, `numpy.sum` in `skimage:measure.block_reduce`). Both now have one;
  `test_every_registered_function_default_can_be_written_in_the_record` guards the registry
  installed here (283 functions; CuPy and pyclesperanto are not installed on this machine).
- The WIP stored the *effective* config as the global document. Rebuilding against it gave equal
  values but different sources (everything inherited from the global scope). The record now stores
  the saved global config (`global_config_code`, as this design says); with none set it stores the
  default-constructed one, which the round trip shows resolves identically.
- A step's values are read from `AbstractStep.configuration_parameters()` (the function pattern is
  not configuration). An inherited path is checked before descending: a nested config the step
  leaves unset is inherited whole and ObjectState lists it as one path.
- The producer of a main-flow image is the step that produced the pixels. A step that returns its
  image unchanged saves a file whose producer is the earlier step: the same identity the viewer
  item carries.
- A rebuilt run writes every parameter, so its record says `pipeline` where the first said
  `function_default`. Nothing else differs apart from the plate path and the submission scope
  (`submission_<id>` in step scope ids). Output files (TIFF and CSV) are byte-identical.

**Not done.** `changed_during_run` (asking again for size and modification time at the end of the
run): the design text above still describes it; it is dropped, a file modified during a run is
not detected.

## Hand-off (2026-10-12): state, results, what remains

A fresh agent continues from here. PolyStore part: PR OpenHCSDev/PolyStore#41 (branch
`feat/file-content-identity`, commit `8ee8ce4`, version 0.6.3, not merged, not on PyPI). This
branch pins `polystore>=0.6.3,<0.7` and points the submodule at that commit.

### Implemented and committed

| Commit | What |
|---|---|
| `7ea5440e1` | this receipt's design |
| `1786bbc13` | `openhcs/core/function_identity.py`; `identity()` on the function reference and registry entry families; custom source text kept on `CustomFunctionSourceNamespace`; `content_at_run_start` on the declared path family; `openhcs/core/run_record.py` |
| `c2d689e61` | bundle carries `RunDeclaration`; workers report `producer_by_saved_path`; `RunRecord.at_run_start` in `execute_bundle_request`; one-transaction write in `reconcile_completed_dataset`; complete rendering writes every parameter; `tests/unit/test_run_record.py` (17), `tests/integration/test_run_record_round_trip.py` |
| `09a712ad5` | `openhcs_read_run_record` capability (`openhcs/agent/services/run_record_service.py`), `tests/unit/test_run_record_capability.py` (7) |
| `d33b72496` | merge of `origin/main` |

### Acceptance run (CPU venv, torch 2.14.1+cpu, Cellpose 3.1.1.3, 3 BBBC039 fields)

Scripts and outputs: `.claude/scratch/acceptance/` (untracked). NumPy-declared Cellpose source
from commit `47fbed348` (the torch-declared one cannot compile without CUDA; DL1's gap).

- Cellpose then `measure_labelled_objects`: a label TIFF resolves to step `segment`, a
  measurement CSV to step `measure`. `custom_source_sha256` equals sha256 of the source file.
  All 7 Cellpose parameters are recorded as `function_default`; `min_area_px=20` as `pipeline`.
  `imports.libraries`: cellpose 3.1.1.3, numpy 2.0.2. Record 78,764 bytes, metadata document
  97,633 bytes. Compile 2.53 s, execute 19.97 s.
- Body changed, name kept: source hash `a2824fff…` -> `bca58da6…`, record id `7ce7240d…` ->
  `37e46efc…`; each dataset stores its own text.
- Re-run from the record in a fresh process with nothing registered: 3 main images, the label
  TIFF and both step CSVs byte-identical. ROI zips differ only in an embedded absolute
  `source_path` and zip timestamps (all `.roi` members identical); `segmentation_summary.txt`
  lists absolute paths; `metaxpress_style_summary.csv` has a different `Plate ID`.
- N2V2 denoise (NumPy-declared copy; model file left at its default): `declared_files` entry
  `declared_as: "input file"`, `hashed: true`, sha256 `0340245e…`, 124,144,631 bytes, equal to
  hashlib; after overwriting the model the recorded hash is `5a2582ea…`.
- Hash cost: standalone 1 GiB, sha256, 0.58 s warm and 2.15 s after dropping the page cache
  (blake2b 1.03 s, md5 1.22 s). Through `filemanager.file_content` under load (full suite running,
  2 GB free RAM): 12.56 s first read, then 1.29 s and 1.46 s.
- Capability default response: 52,808 bytes for a dataset root, 68,175 for one file.

Example (Cellpose step, trimmed):

```json
{"name": "segment", "pipeline_position": 0,
 "step_scope_id": "…/runA/source::pipeline::submission_7fd30cd3c3c0::step_0",
 "input_memory_type": "numpy", "output_memory_type": "numpy", "assigned_gpu_devices": [],
 "functions": [{
   "identity": {"key": "openhcs:cellpose_segment", "module": "openhcs.processing.custom_functions",
     "name": "cellpose_segment",
     "imports": {"libraries": [{"distribution": "cellpose", "version": "3.1.1.3"},
                               {"distribution": "numpy", "version": "2.0.2"}],
                 "modules_without_distribution": ["openhcs"]},
     "custom_source_sha256": "a2824fffc06b7c906d3af193fa4ff21ba24a7a5ddf0a16e54419aa7eb077d9af"},
   "parameters": [
     {"name": "image", "value": "<supplied when the function is called>", "source": {"kind": "run_time"}},
     {"name": "model", "value": "cellpose_segment.__openhcs_source_a2824f….__openhcs_member_….NUCLEI",
      "source": {"kind": "function_default", "function": "openhcs:cellpose_segment"}},
     {"name": "diameter", "value": "None", "source": {"kind": "function_default", "function": "openhcs:cellpose_segment"}},
     {"name": "flow_threshold", "value": "0.4", "source": {"kind": "function_default", "function": "openhcs:cellpose_segment"}}],
   "declared_files": []}]}
```

### Gates

- `guardrails_local.sh` on `d33b72496`: **rc=1**. Lines: `ratchet openhcs exit 1`,
  `ratchet scripts exit 0`, `ratchet benchmark exit 0`, `38 passed, 22 warnings in 68.54s`,
  `nra-r1 exit 1`, `guardrails rc=1`. Ratchet delta: `GodClassExcess PipelineCompiler +7`,
  `GodClassExcess OpenHCSMetadataTarget +24`, `LongBooleanChain +1`,
  `BooleanChainTerms openhcs/core/steps/abstract.py +1`,
  `BooleanChainTerms openhcs/core/virtual_workspace_metadata.py +4`,
  `ForeignAbsenceProbe` +1 in `virtual_workspace_metadata.py` and +1 in
  `serialization/pycodify_formatters.py`, `StringSubscript +21`,
  `AnyAnnotation openhcs/core/run_record.py +6`. NRA increased: `unmodeled_record_shape` in
  `openhcs/core/run_record.py` and `openhcs/agent/services/run_record_service.py`.
- `verify_branch.sh DL3`: see "Full suite" below.
- Not run: `smoke_local.sh`, official30 parity (required: compilation, execution and
  materialization changed).

### What remains, in order

1. **Model the record as nominal types** (clears `StringSubscript`, `AnyAnnotation`,
   `unmodeled_record_shape`): `RunRecord` holds `content: Mapping[str, Any]` and the reader and
   the capability service index it by string. Replace with frozen dataclasses (software, step,
   function, parameter, declared file) that encode to and decode from JSON in one place;
   `RunRecordService` reads attributes.
2. **Move the added code out of the two oversized classes**: `saved_path_producers` out of
   `OpenHCSMetadataTarget` (it belongs with `ProducedFiles`), the declaration calls out of
   `PipelineCompiler`. Remove the two new absence probes and the lengthened boolean chains
   (`StepExecutionObservation.is_empty`, `reconcile_completed_dataset`).
3. **Defect: a declared path left at its default is recorded as written in the pipeline**, with
   the resolved absolute path as its value. `CallableContract.resolve_declared_paths`
   (`callable_contract.py:~1296`) puts the resolved default into the kwargs and `_parameters`
   (`run_record.py`) treats every kwarg as written. Record the written or default value with its
   true source and keep the resolved path only in `declared_files`. Failing test first.
4. **`enabled`** is written in `pipeline_code` function kwargs but has no `parameters` entry.
5. **Device on CPU**: `assigned_gpu_devices: []` does not say the step ran on host memory. State
   it explicitly from the place DL1 leaves the assignment.
6. **Enum defaults of custom functions** render as
   `name.__openhcs_source_<sha>.__openhcs_member_<hex>.MEMBER` (same mangling as D1 gap 10).
7. **Transitive libraries**: `imports.libraries` lists direct imports only (torch is not listed
   for Cellpose; it is only in `software.installed_distributions`). Decide: record the
   requirement closure of the direct imports, or state the rule in the record.
8. **Plate-level outputs are unrecorded**: `results/metaxpress_style_summary.csv` (analysis
   consolidation) has no `produced_files` entry; `for_output_file` raises `UnrecordedOutputFile`
   for it. It needs a producer identity of its own kind (it is not a step output).
9. **Record size**: 59 to 79 kB per record, mostly installed distributions and per-step
   configuration repeating absolute scope ids. The capability's shortened response is still 53 kB.
10. **Fallback to remove or justify**: with no saved global config, `RunDeclaration` stores a
    default-constructed one.
11. **Reader API**: no public "is this a dataset root"; `ProducedFile` has neither dataset root
    nor relative path, so the capability's read of the metadata document above a file bypasses
    the agent path policy; a directory without metadata reports as an unrecorded file.
12. `changed_during_run` is not implemented; update the design text or implement.
13. Reproducibility leaks found by the round trip, outside this branch's scope: ROI zip metadata
    and `segmentation_summary.txt` embed absolute source paths; zip timestamps.
14. Gates: guardrails to `rc=0`, `verify_branch.sh`, `smoke_local.sh`, parity under
    `heavy_slot.sh` and `official30.lock`. Then mark the PR ready. PolyStore #41 must merge and
    release 0.6.3 before CI here can install the pin.
15. Delete `.claude/venv-cpu` (2.3 GB) and `.claude/scratch/` in this worktree.
16. For the #1230 branch: nothing in the example functions has to change for this gap; the count
    table's own `model` and `diameter_px` columns are no longer the only place those are stated.

### Full suite (`verify_branch.sh DL3`, on `d33b72496`, lines verbatim)

```
suite: = 7 failed, 11754 passed, 25 skipped, 358 warnings, 6 subtests passed in 1948.52s (0:32:28) =
collected 11785, reported 11761, crash lines 0
new vs known: 5
only on DL3:
tests/unit/agent/test_mcp_server.py::test_mcp_stdio_server_roundtrip_returns_errors_as_payloads
tests/unit/test_mcp_dev_client_terminal_input.py::test_long_terminal_command_reuses_original_parser_and_client[...]
tests/unit/test_pycodify_formatters.py::test_function_step_round_trip_omits_injected_values_but_keeps_runtime_settings[False-expected_kwargs1]
fails on both with a different error:
```

Failing ids outside `known.fail` (5), with the believed cause (none investigated beyond this):

| Id | Rerun alone | Believed cause |
|---|---|---|
| `tests/unit/test_pycodify_formatters.py::test_function_step_round_trip_omits_injected_values_but_keeps_runtime_settings[False-expected_kwargs1]` | fails on DL3 only | **This branch.** `clean_mode=False` now writes every parameter; the test expects only the written kwargs in the full rendering. Same change of meaning as the one already made in `tests/unit/agent/test_authoring_roundtrip_boundaries.py`; restate the expectation for the full rendering, keep the clean one. |
| `tests/unit/test_mcp_dev_client_terminal_input.py::test_long_terminal_command_reuses_original_parser_and_client[...]` | fails on DL3 only | **Probably this branch**: the generated CLI gained `read-run-record`, or the complete rendering changed a long command's text. Not looked at. |
| `tests/unit/agent/test_mcp_server.py::test_mcp_stdio_server_roundtrip_returns_errors_as_payloads` | fails on DL3 only in the gate's rerun; passed alone earlier (`1 passed` with `-k stdio_server_roundtrip`) | Seen before as a 5 s stdio-initialize timeout under load (acceptance run and suite ran together). Rerun on a quiet machine before treating it as real; if it persists, the new tool lengthens server start. |
| `tests/unit/agent/test_mcp_affine_inspection_progress.py::test_resident_continuous_connections_keep_affinity_and_wire_progress[original-continuous]` | passed on rerun (both trees) | load-dependent |
| `tests/unit/test_ack_return_route_journey.py::test_two_native_stream_producers_keep_deferred_ack_ownership[TransportMode.IPC]` | passed on rerun (both trees) | load-dependent |

The remaining 2 of the 7 failures are the ids in `known.fail`. Fix the first two rows as step 0
of "What remains".

## Second hand-off (2026-10-12): what changed, what remains

Commit `3a55d1fe4` (pushed). Stopped at the context limit after items 1 and 2 of the continuation
brief; nothing else is started in the tree.

### Done

**Brief item 1: the record is nominal types** (`openhcs/core/run_record.py`,
`openhcs/core/function_identity.py`).

| Type | Holds |
|---|---|
| `RunRecord` | `software`, `pipeline_code`, `global_config_code`, `configuration`, `steps`, `custom_sources` (text by sha256, each once) |
| `SoftwareEnvironment` | OpenHCS, Python, platform, `installed_distributions` (version by name) |
| `StepRecord` | `calls: StepCalls`, `configuration: tuple[ConfigValuesFromOwner, ...]` |
| `StepCalls` | name, pipeline position, step scope id, memory types, `assigned_gpu_devices: tuple[GpuDevice, ...]`, `functions` |
| `FunctionRecord` | `identity`, group, position, memory types, `parameters`, `declared_files` |
| `FunctionIdentity` / `CustomFunctionIdentity` | key, module, name, `defined_in` and `imports` (`ModuleLibraries`); the custom one adds `source_sha256`. The text is not copied into the identity: `source_texts()` reads it from the registered `CustomFunctionSourceNamespace` that owns the hash, and the record stores it once under `custom_sources` |
| `RecordedParameter` | name, value (Python expression, `None` when no declaration states it), `source: type[ParameterSource]` |
| `ParameterSource` family | `WrittenInPipeline` (`pipeline`), `FunctionDefault` (`function_default`; the function and version are the identity of the enclosing `FunctionRecord`), `SuppliedAtRunTime` (`run_time`). Each says how its value is written (`value_expression`) |
| `ConfigValuesFromOwner` | `owner: ConfigValueOwner(source, scope_id, type_name)`, `values` by field path. `source` is `type[ConfigValueSource]`: `SetOnObject` (`set_here`) or `InheritedFrom` (`inherited`) |
| `DeclaredFile` | parameter, `declared_as`, path, `content: HashedFileContent \| UnhashedFileContent` (PolyStore's family) |
| `DatasetRunRecords` | the two keys of the metadata document: `run_records` by id, `produced_files: Mapping[str, StoredProducedFile(run_record, producer: StreamProducerIdentity)]` |
| `ProducedFile` | what the reader returns for one file: `record`, `producer`, `.step -> StepCalls` |

**One codec.** Encode is `python_introspect.to_jsonable`, decode is
`python_introspect.dataclass_from_mapping` (`external/python-introspect/src/python_introspect/
jsonable.py`, `dataclass_projection.py`); `RunRecord.to_json` / `from_json` and
`DatasetRunRecords.in_document` only call them. No `to_record` method is left in OpenHCS. A class
of the two source families is stored as its registry key (`AutoRegisterMeta`, the codec's existing
rule for `type[Family]`). The identity family and the file-content family carry data, and the codec
has no nominal tag for a family *instance*: they are declared as unions of dataclasses and the
decoder picks the member whose declared fields match exactly (it rejects undeclared fields and
raises on an ambiguous match). `test_stored_json_reads_back_as_the_same_record` covers every type.
**Open point for the owner:** that union decode is by field set, not by name. If that is not
acceptable, the fix belongs in python-introspect (a registered family instance stored as key plus
fields), not in a second codec here. PolyStore's `FileContent.to_record` / `from_record`
(`hashed: bool` key) is now unused by OpenHCS and can be dropped from #41 when it is rebased.

**Reader and capability return the types.** `RunRecord.for_dataset`, `RunRecord.for_output_file`,
`ProducedFile.step`. `openhcs_read_run_record`: `RunRecordEntry(record_id, steps: tuple[StepCalls,
...], record: RunRecord | None)`; the request flag is `include_full_record` (was
`include_sources`); the digest-and-`shortened_fields` form is gone. Contract fixture regenerated
(only that tool changed).

**Size (part of brief item 5, measured on the two-step unit pipeline in the shared venv, 246
distributions):** default response `steps` 2,277 bytes; full record 47,633 bytes (software 5,252,
pipeline_code 12,000, global_config_code 7,453, configuration 9,846, steps 12,984). Grouping
resolved values by owner took the pipeline configuration from 22.9 kB to 9.8 kB and each step's
from 12.3 kB to 5.3 kB. Not re-measured on the Cellpose run.

**Brief item 2: the two suite failures.**
- `test_pycodify_formatters.py::test_function_step_round_trip_omits_injected_values_but_keeps_runtime_settings[False-...]`:
  the first agent had changed what `clean_mode=False` means (the hook was in
  `FunctionStepFormatter.format`). The test states the stored-document promise (every stored
  field, no parameter the pipeline does not state) and it holds again: the hook is removed, and the
  two tests that had been weakened for it (`test_authoring_roundtrip_boundaries.py`,
  `test_source_round_trip.py`) are restored to main's text. The record's copy is its own
  rendering, `PipelineDocumentCodec.render_with_every_parameter` (completes each step's pattern
  with `with_every_parameter_written`, then renders unabridged).
  `test_saved_pipeline_text_stays_short_and_the_record_copy_is_complete` asserts all three.
- `test_mcp_dev_client_terminal_input.py::test_long_terminal_command_reuses_original_parser_and_client`:
  not this branch. It pumps a 4 kB+ command through a PTY child with a 15 s deadline. Alone on the
  branch at load average 13: 13.4 s and 8.5 s (passed), then 19.4 s and 17.3 s (one failed). With
  the child importing `origin/main`'s package under the same load: 15.07 s and 15.01 s, both
  failed, twice. Left as is.
- `test_mcp_server.py` stdio tests: 5 s `session.initialize()` timeout under `-n 4`; `2 passed`
  alone.

Tests run here: `tests/unit/test_run_record.py`, `test_run_record_capability.py`,
`tests/integration/test_run_record_round_trip.py`, `test_mcp_tool_contract.py`,
`test_pycodify_formatters.py`, `test_source_round_trip.py`,
`test_authoring_roundtrip_boundaries.py`: all pass. Full suite, guardrails, smoke and parity were
not run after these changes.

### What remains, in order (numbers are the continuation brief's)

3. **Shrink the two oversized classes; ratchet to no increase.** Not started. Expected to be
   cleared by item 1 but unverified: `StringSubscript`, `AnyAnnotation`, `unmodeled_record_shape`.
   Still present: `GodClassExcess PipelineCompiler +7` (the seven lines are the
   `RunDeclaration.before_step_resolution` call, `with_resolved_steps`, and `run_declaration=` at
   three bundle constructions), `OpenHCSMetadataTarget +24` (`saved_path_producers` and the
   additions in `finalize_completed_dataset`), the boolean chains in
   `StepExecutionObservation.is_empty` and `AtomicMetadataWriter.reconcile_completed_dataset`,
   and two absence probes (`ModuleExportedCallableFormatter.can_format` in
   `pycodify_formatters.py`; one in `virtual_workspace_metadata.py`). Notes from reading the
   compiler: the declaration needs the submitted documents before `_resolve_pipeline_once`
   replaces the steps in place, and the per-step provenance that only
   `ResolvedPipelineDefinition` holds; nothing on the bundle or the plans carries that
   provenance, so the orchestrator (the single caller, `orchestrator.py:739`) cannot build it
   after the fact without the compiler handing something over. The two early returns in
   `compile_pipelines` build the same empty bundle twice. `saved_path_producers` belongs with
   `ProducedFiles` in `run_record.py`. Then merge `origin/main` and run `guardrails_local.sh`.
4. **Defects in what is recorded**, failing test first, none started:
   (3) declared path left at its default: `CompiledFunctionInvocation.from_normalized_item`
   (`function_patterns.py:~926`) replaces the kwargs with `resolve_declared_paths`' result, so the
   invocation no longer knows which paths the pipeline wrote; it has to keep that (the stated
   value and its source per declared path) so `_parameters` can say `function_default` and
   `declared_files` holds the resolved path. (4) `enabled` has no parameters entry. (5) device on
   a host run: `StepCalls.assigned_gpu_devices` is still an empty tuple; state it positively from
   `FrameworkDeviceAssignment` and note the DL1 dependency. (6) enum defaults of custom functions
   render with the mangled path. (7) libraries: direct imports only; add the requirements
   closure, each list named. (8) plate-level outputs have no `produced_files` entry. (10) no
   saved global config: `RunDeclaration.before_step_resolution` still falls back to
   `GlobalPipelineConfig()`. (12) `changed_during_run`: still in the design text, not
   implemented.
5. **Reader**: a public "is this a dataset root / which dataset contains this file" answer
   through the dataset access owner; `DatasetRunRecords.of_dataset` and `_dataset_root_of` still
   read the metadata file directly, and `RunRecordTarget.at` probes for the file, so the
   capability's read of the document above a file is not checked by the agent path policy. Size:
   re-measure on the Cellpose record.
6. **PolyStore 0.6.4**: not started. Rebase #41 onto PolyStore main, version 0.6.4, drop the
   unused `to_record` / `from_record` if the owner agrees, suite in a fresh venv, merge, annotated
   tag, publish. Then this branch's pin (see the top of this document).
7. **Acceptance re-run** (Cellpose on CPU, three BBBC039 fields), then delete `.claude/venv-cpu`
   (2.4 GB) and `.claude/scratch/` (1.2 GB): both still present in the worktree. The acceptance
   scripts under `.claude/scratch/acceptance/` read the old dict form and need the typed reader.
8. Gates (the landing agent's): guardrails `rc=0`, `verify_branch.sh`, smoke, parity. The PR is
   still a draft; its body does not yet say "lands after DL1".
9. Outside this branch, unchanged: ROI zip metadata and `segmentation_summary.txt` embed absolute
   source paths; zip timestamps.

## Third hand-off (2026-10-12): steps A and B done, C to E not started

Commits `18c4d56ae` (A) and `1a1c8c1eb` (B), on a merge of `origin/main` at `6845c3a36`.

### A. Stored family members name their class

**Where the tag is declared.** python-introspect 0.3.0 (PR OpenHCSDev/python-introspect#23,
merged, annotated tag `v0.3.0`, on PyPI through the manual script after the publish workflow sat
queued for 34 minutes). `python_introspect.jsonable`:

- `MemberFamily.declared_by(annotation)` says whether a declared field type admits several
  classes: a union with two or more dataclass members (`UnionMembers`), an abstract dataclass
  (`ConcreteSubclasses`: its concrete subclasses, as loaded), or a class whose metaclass is
  `AutoRegisterMeta` (`RegisteredMembers`: the registry). The three are subclasses; each answers
  `members()`; the registered one reads a tag through `registered_class_from_key`.
- `class_tag(member)` is the one place a tag is derived: the registry key when the class is
  registered (stable when the module or class is renamed), otherwise `__name__`.
- Stored form: `{tag: fields}` (one key; no reserved field name). `to_jsonable` now follows each
  dataclass's declared field types through optional, `Annotated`, tuple/list/sequence/set and
  mapping declarations; `dataclass_from_mapping` reads the class from the tag.
- Errors: unknown tag is `ValueError` naming the known members; a value outside the declared
  family, a non-string registry key, or two members with one tag is `TypeError`; an untagged
  object in a family field is refused, never matched by its fields.
- A type with its own `to_jsonable.register` projection keeps its whole stored form (P1
  Proposition 3.3 is about the guess; those types already write a nominal key of their own).
- Cost of reading declarations when encoding: a dataclass whose field types do not resolve at run
  time is a `TypeError` naming it. One encoded class was affected and is fixed
  (`UiLiveMeasurementEntryState.preview`, import moved out of `TYPE_CHECKING`). A live import of
  about 2,545 first-party dataclasses found 92 whose annotations do not resolve; none of the others
  was found at a `to_jsonable` call, but call sites that encode arbitrary values were not all
  traced (`formbridge/bridge/object_state.py:257`, `core/debug_view_models.py:199`,
  `core/materialization/core.py:3015`, `mcp/dev_client_rendering.py:375,397`,
  `agent/services/artifact_plan_inspection_service.py:443,586`). The full suite is the check.

**The record's two families** are registered and the fields are declared by the family:
`FunctionRecord.identity: FunctionIdentity` (`defined_by`: `installed_module`, `source_text`) and
`DeclaredFile.content: FileContent` (PolyStore, `content_kind`: `hashed`, `not_hashed`).
PolyStore's `FileContent.to_record` / `from_record`, the `hashed` flag and its hand-kept
`_kind_by_hashed` table are deleted on the #41 branch (certificate: **derived**, the registry and
the codec own both facts; nothing in OpenHCS called them).

**Every user of the codec, checked** (live import plus `rg`; about 470 dataclasses reachable from
about 300 decode targets):

| Kind | Where | Effect |
|---|---|---|
| Union of dataclasses decoded by fields | only the two record fields above | now registered families |
| Registered or abstract family with its own projection | `PositionedAxis.spec: AxisSpec` (`PayloadAxes.to_mapping`), `source_spatial_domain: SourceSpatialDomain` (`to_mapping`, key `spatial_dimensions`), `MeasurementTable.rows: ColumnarRows`, `SourceImageProvenance*` | unchanged: they write their own nominal key |
| Field typed with one registered class, decoded | `DebugSnapshotReadResponse.snapshot: DebugSnapshot` (zmq debug response), `ViewerWindowValidationSummaryResult.state: ViewerWindowStateResult \| None` (MCP result) | now `{registry key: fields}` |
| Registered family fields, encoded only | `SourceBindingsConfig.bindings` / `match_plan` (and the step and lazy variants), `GlobalPipelineConfig` / `PipelineConfig` streaming configs, `ObjectRelationship.declaration`, `Output.content`, CPA workspace panels and axes, `DebugProgressRecord.context` / `.snapshot`, `benchmark/openhcs_measured_run.py:101` | tagged in what they encode; `SourceBindingsConfig.declaration_identity()` hashes that JSON, so its value changes (whether it is persisted was not checked) |
| Concrete dataclass with dataclass subclasses as the field type | formbridge `UiActionIdentity`, `UiCodeDocumentIdentity`, `UiStateSurfaceIdentity`, `UiWindowIdentity`, `UiSemanticAddress`, `EndpointConnectionSpec`; `NapariDisplayConfig`; `ViewerPayloadControlOptions`; `GallerySourceEvidence` | **not a family, unchanged.** A subclass instance in such a field is written with its own fields and the decoder then refuses the undeclared ones. Open point: either the codec refuses a subclass instance when encoding, or these bases declare a family |

**Stored formats that changed:** the `run_records` section of `openhcs_metadata.json` (new on this
branch, nothing released), MCP results and zmq debug responses that carry the fields in the third
and fourth rows (both ends are the same version), and the source-bindings declaration identity.
**Nothing on disk has to be regenerated:** no tracked JSON holds a run record (searched all
12,378 `*.json` / `*.jsonl` files), the only fixture decoded through the codec
(`tests/fixtures/mcp/start-owned-runtime-400.json`) has no family field, and MCP tools publish
`dict[str, Any]` as their result schema. Files under `paper/figures/slas/` hold UI summaries with
`identity` / `semantic_address` objects (the last row: unchanged form) and no code decodes them.
`paper/**`, `validation/**`, `benchmark/results/**` were not touched.

**Dependants whose upper bound excludes python-introspect 0.3.0:** ObjectState 4.0.0
(`>=0.2.0,<0.3`), formbridge 0.1.4 (`>=0.2.7,<0.3`), pyqt-reactive 0.8.0 (`>=0.2.6,<0.3`),
zmqruntime 0.6.4 (`>=0.2.5,<0.3`). pycodify and PolyStore do not depend on it; arraybridge has no
upper bound. None was released from here.

Tests: python-introspect 191 pass on Python 3.10, 3.12 and 3.13 (round trip per member of each
kind of family, members with identical fields, containers and optional fields, unknown tag,
untagged data refused, own projection kept, unresolved field type). OpenHCS: the three run-record
test files and `test_mcp_tool_contract.py` pass; of the 2,951 tests in files that touch the codec,
the failures were a test-order leak (`tests/unit/test_axis_family_witness.py` leaves the
RemoteSensing axis family active for the files that follow it in the same xdist worker; with that
file left out the 40 affected files give 1,410 passed and 1 failed,
`test_installed_mcp_demo.py::test_portable_source_normalization_defers_catalog_and_execution_runtimes`,
which fails inside `RegistryService.metadata_for_canonical_key` in a subprocess and was not
compared with main).

### B. The two oversized classes and the ratchet

- `OpenHCSMetadataTarget` and `AtomicMetadataWriter` are byte-identical to main again
  (`function_outputs.py` differs from main only in `finalize_function_step_outputs`, which asks
  `ProducedFiles.stated_by_step`). Deleted: `OpenHCSMetadataTarget.saved_path_producers` (moved,
  same body), the `run_record` / `produced_files` parameters, `ProducedFiles.write_into`
  (certificate for all: **derived**, the same statements now run in `run_record.py`).
- **The record is stored by its owner in a second locked update.** `RunRecord.store_with_saved_files`
  (called in the same `finally` as `finalize_completed_dataset`, so also after a failure) asks
  `RunRecordWriter(AtomicMetadataWriter).store` for each dataset root the run saved a file under.
  This replaces the design text's "one locked transaction": the dataset's `subdirectories` and the
  record are now two consecutive transactions on the same document, each under its lock. A crash
  between them leaves a dataset without its record. That is the price of not putting the record's
  logic into the writer's transaction; if one transaction is required, the writer needs an
  extension point, which adds lines to it.
- **The compiler still makes the two declaration calls.** The previous note holds: the documents
  must be rendered before `_resolve_pipeline_once` replaces the steps, and only its result carries
  the per-step provenance. What changed is that both empty-compilation returns go through
  `CompiledExecutionBundle.with_nothing_to_run`, so `PipelineCompiler` is 3 lines smaller than on
  main instead of 7 larger.
- `StepExecutionObservation.is_empty` is `not any(field values)`, derived from the dataclass
  fields (all six were in the hand-written chain). The absence probe in
  `virtual_workspace_metadata.py` went with the revert; the `ModuleExportedCallableFormatter`
  probe is not counted by the ratchet and is unchanged.
- Two `StringSubscript` hits: `del parameters["func"]` (now a filter on the value being the
  step's pattern) and a quoted annotation in `run_record.py`.
  `CustomFunctionSourceNamespace.attribute_of_revision` names the namespace attribute once.

Gate (the one this job runs), after merging `origin/main`:

```
ratchet openhcs exit 0
ratchet scripts exit 0
ratchet benchmark exit 0
38 passed, 22 warnings in 39.28s
nra-r1 exit 0: "increased": []
base 6845c3a363b1d24a6eeaf006f2efce3658e7804f head 1a1c8c1ebe8ae8021fe17f463b7471388add4e44 guardrails rc=0
```

Tests run for B: the run-record files, `test_function_outputs.py`,
`test_orchestrator_lane_planning.py`, the four publication test files restored to main's text,
and 73 unit files that touch custom functions, observations, bundles or compilation: with the
witness file left out, 913 passed, 1 failed
(`test_mcp_server.py::test_mcp_stdio_server_roundtrip_returns_errors_as_payloads`, the 5 s stdio
timeout under xdist the second hand-off describes). Full suite, smoke and parity were not run.

### What remains, in order

C. **Defects in what is recorded**, failing test first, none started. The second hand-off's
   item 4 is still the exact list: (3) declared path left at its default, (4) `enabled`,
   (5) device on a host run (depends on DL1), (6) enum defaults of custom functions, (7) direct
   imports and the requirements closure, (8) plate-level outputs, (10) no saved global config
   (`RunDeclaration.before_step_resolution` still falls back to `GlobalPipelineConfig()`),
   (12) `changed_during_run`.
D. **PolyStore 0.6.4.** Clone at `.claude/ps-clone` (branch `feat/file-content-identity`, pushed
   at `5301d35`: #41 plus the registered family). Still to do: rebase onto PolyStore main
   (`5fdb617`), version 0.6.4 with `uv.lock`, retitle the PR, suite in a fresh venv, merge,
   annotated tag, publish. The pre-rebase commit `5301d35` is what the submodule needs until DL1,
   so keep it reachable (push it under another branch name before the rebase is force-pushed).
E. **Reader** (second hand-off item 5: dataset-root answer through the dataset access owner; the
   capability's metadata read through `openhcs/agent/path_policy.py`), then the **acceptance
   re-run** with the scripts in `.claude/scratch/acceptance/` moved to the typed reader, the
   short-response size on the Cellpose record, then delete `.claude/venv-cpu` and
   `.claude/scratch/` (both still present, with `.claude/pi-clone` and `.claude/ps-clone`).
F. Decide the two open points above: one transaction or two for the record; concrete bases with
   subclasses in codec fields.
G. Gates (the landing agent's): `verify_branch.sh`, smoke, parity. The PR stays a draft.
H. Outside this branch, unchanged: ROI zip metadata and `segmentation_summary.txt` embed absolute
   source paths; zip timestamps; `test_axis_family_witness.py` leaks the active axis family.
