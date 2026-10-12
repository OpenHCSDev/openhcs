# DL3: an output dataset says what produced it

Branch `refactor/DL3-output-provenance`. Gap 6 of `D1-cellpose-n2v2-custom-functions.md` (PR #1230).

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
