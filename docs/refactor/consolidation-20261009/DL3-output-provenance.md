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

(filled in as work proceeds)
