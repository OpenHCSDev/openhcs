# DL2: a file one step writes is an input of a later step; one result per plate

**Head audited:** `main` at `1b5fe99f5`. **Rules:** [00-RULES.md](00-RULES.md). Closes gaps 3 and 9 of
the Cellpose/N2V2 investigation (draft PR #1230, `D1-cellpose-n2v2-custom-functions.md`).

## What is wrong (measured at this head)

1. **Silent overwrite.** A `PlateOutputFile` parameter resolves to one path for every invocation of
   the step (`callable_contract.py:1277`, `function_patterns.py:926`). An axis-scoped step runs once
   per well and per pattern group, so 50 wells write one file from several processes; last writer
   wins.
2. **No link.** A `PlateInputFile` is checked for existence at compile (`vfs_protocol.py:153`), so a
   file an earlier step writes fails with `Declared input file does not exist`.
3. **No step sees more than one well with images.** The unit of execution is one value of the
   partition axis (`core/axes.py:107`); `variable_components` and `group_by` exclude that axis
   (`axes.py:593`). The only once-per-plate mechanism is `execution_scope(PLATE)`, which forbids a
   memory type (`funcstep_contract_validator.py:873`), must be terminal
   (`funcstep_contract_validator.py:626`, `bundle_execution.py:455`) and runs after every well
   finished (`bundle_execution.py:297`). The two "group by plate" compile failures in D1 are not
   step grouping at all: they redefine the plate's partition value in the source-binding rule
   (`source_binding_workspace.py:1245` keeps the site from the filename, so two wells get one plane
   address; `source_projection.py:1252` rejects an unencoded token). That route erases well identity
   for the whole pipeline and is the wrong tool.
4. **Input loading is eager.** `load_input_stack` (`function_runtime.py:581`) builds one array per
   call; no lazy or chunked image input exists.
5. **Output declarations resolve against the input plate** (`compiler.py:1571`).

## Design

**What a produced file is.** A location the author names and the function's own code writes. Its
identity is `(producer step, output-file parameter)`; its path is known at compile time. It is not
an artifact: an artifact is a value returned to the platform, stored per scope in the runtime value
store, at a path the platform chooses. The two mechanisms answer different questions and are not
unified; the declared-file family (`DatasetPathDeclaration`) is extended, and nothing new carries
values between steps. A declared input file with no producer (template, macro, pretrained weights)
has no artifact reading at all, which is why the file family cannot be folded into artifacts.
(P1 Prop. 3.1 / Thm 3.2: two meanings that need different answers keep different names.)

**Relations and their owners.**

| Relation | Declared once by | Derived by the compiler |
|---|---|---|
| a parameter is a file the function writes / reads | the annotation (`PlateOutputFile`, `PlateInputFile`) | which root it resolves against: behaviour on the declaration class (output: output dataset root; input: input plate) |
| the path of a produced file | the producer step's argument (or signature default) | the resolved absolute path, recorded on the compiled invocation |
| a consumer reads a produced file | the consumer step's argument: `OutputFileOf(step="fit", parameter="model_file")` in place of a path | the consumer's resolved path (the producer's), that the producer is an earlier step, and the run-time existence check after the producer finished. An argument that is a path means an existing file, checked at compile, as today |
| who writes a path | nothing new: the step's scope and grouping | the set of invocations per path over all compiled contexts of the plate; more than one writer of one path is a compile error naming both |
| a step runs once for the plate | `execution_scope(PLATE)` (existing) | stages: runs of axis steps separated by plate steps, executed in pipeline order; a plate step's files and artifacts exist before any later step starts |

**Plate scope with images.** A plate-scoped callable may declare a memory type. It then receives
`images: PlateImages`, an iterable that loads one well's stack at a time in the declared memory type
on the assigned device (the loader an axis step already uses), so memory is bounded by one well. It
does not change the image flow: the next axis step reads what the plate step read.

**Reruns.** Nothing depends on a file happening to exist. "Fit again" is the pipeline with the fit
step (it overwrites its own declared output: one writer). "Reuse this model" is the pipeline without
the fit step whose denoise step names a path.

**Identity exposed for provenance (DL3).** Each compiled invocation carries `declared_files`: one
record per declared path parameter that has a value (files and directories; a parameter whose value
is `None` has no record). DL3 hashes from that list; DL2 computes no hash. Exact shape, as built:

- Attribute path: `bundle.runtime_contexts[axis].step_plans[step_index].compiled_function_pattern
  .iter_invocations()` yields `CompiledFunctionInvocation`; its field
  `declared_files: tuple[DeclaredFile, ...]` (`openhcs/core/function_patterns.py:504`). It is an init
  field, so `__reduce__` carries it to worker processes (checked through
  `for_transport_serialization().transport_contexts` and pickle).
- `openhcs.core.vfs_protocol.DeclaredFile` (frozen): `parameter: str`, `path: Path` (absolute),
  `backend: str`, `declaration: DatasetPathDeclaration` (the instance; `declaration.writes_file` is
  true for `PlateOutputFileDeclaration` only).
- `openhcs.core.vfs_protocol.LinkedInputFile(DeclaredFile)` (frozen), for an argument written as
  `OutputFileOf(...)`: adds `producer_step_index: int`, `producer_step_name: str`,
  `producer_parameter: str`. Its `path` equals the producer's `DeclaredFile.path`.
- The same step's invocation in another well carries equal records (paths are per plate), and a step
  that runs once for the plate has the record in every context's plan; only the plan with
  `owns_runtime_outputs` runs it.
- A pattern compiled without a `CompilationPathResolver` (`compile_function_pattern(...)` with the
  default `path_resolver=None`, used by unit tests only; the compiler always passes one) has an empty
  `declared_files` even for absolute paths. That `None` mode predates DL2 and is a candidate to remove.

## What changes for existing callers (gap 9)

- `global_output_folder` (`config.py:1109`) defines the output root, so it cannot resolve against
  it. It gets its own declaration class and stays relative to the input plate.
- `CompilationDebugConfig` bundle (`config.py:1400`): `<plate>/debug/bundle.pkl` becomes
  `<output dataset>/debug/bundle.pkl`.
- `n2v2_processor_torch.save_model_path` (`:322`): moves to the output dataset.
- Absolute paths are unchanged.

## Tests

Compiler level, one per rule: output resolves against the output dataset; two writers of one path is
a compile error naming both; a linked input compiles without the file existing and resolves to the
producer's path; a link to a later or unknown step is a compile error; an unlinked missing input is
still a compile error; plate step followed by axis steps compiles into stages. Integration, through
the execution server: fit once per plate, denoise every well, two denoise runs identical.

## Progress notes

- [x] facts measured, design written (this commit)
- [x] part A: declaration roots, `OutputFileOf`, single writer, `declared_files` (notes below)
- [ ] part B: plate scope with images, stages
- [ ] N2V2 acceptance, gates, PR

## Part A: what was built

Public names (all in `openhcs/core/vfs_protocol.py` unless said otherwise):

- `OutputFileOf(step=..., parameter=...)` (`:104`), frozen, keyword-only. Written as the argument of
  an input-file parameter. Pipeline source generation emits it with its import and loads it back
  equal (`tests/unit/test_source_round_trip.py`, pattern `file_of_an_earlier_step_kwarg`).
- Roots are behaviour on the family: `DatasetPathDeclaration.root(roots)` (`:231`), supplied by two
  intermediate classes, `InputDatasetPathDeclaration` (`:296`) and `OutputDatasetPathDeclaration`
  (`:303`). `PlateInputFileDeclaration` and `PlateInputDirectoryDeclaration` inherit the first,
  `PlateOutputFileDeclaration` and `PlateOutputDirectoryDeclaration` the second.
- `OutputParentDirectoryDeclaration` / annotation `OutputParentDirectory` (`:380`, `:401`): the
  declaration of `PathPlanningConfig.global_output_folder` (`config.py:1109`); relative to the input
  dataset because it defines the output root.
- `DatasetPathDeclaration.linked_file(...)`: rejects an `OutputFileOf` with `TypeError`;
  `PlateInputFileDeclaration` overrides it and asks the compiler's table.
- `DatasetPathDeclaration.writes_file` (class fact, true for `PlateOutputFileDeclaration`): the one
  place that says a parameter is a file with one writer. The table of produced files, the compile
  check and the run-time claim read it.
- Records `DeclaredFile` (`:143`) and `LinkedInputFile` (`:171`); errors `DeclaredFileLinkError`
  (`:115`, a `ValueError`) and `SeveralWritersOfDeclaredFileError` (`:119`, a `ValueError`);
  `DeclaredFileWrites` (`:123`), the per-execution set of claimed output files.

Compiler (`openhcs/core/pipeline/compilation_session.py`):

- `InputDatasetPathResolver` (`:267`) knows only the input dataset; `CompilationPathResolver`
  (`:321`) inherits it and adds `output_dataset` and `produced_files`.
  `CompilationPathResolver.for_dataset` (`:331`, called at `compiler.py:1571`) resolves
  `path_planning_config` with the first (so `global_output_folder` is absolute), computes the output
  root with `PathPlannerPathAuthority.build_output_dataset_root`, then builds the second. An
  output-rooted declaration inside the config that defines the root raises `TypeError`. The error
  note of `resolve` names the declaration class and the root used.
- `ProducedFiles.from_pipeline` (`:166`, called once per pipeline through `reading_files_of` at `compiler.py:1591`, before
  per-axis compilation) builds the table from each step's normalized function pattern
  (`ArtifactGraph.invocation_items()`) and each callable's `writes_file` parameters (authored
  value or signature default), then resolves every declared path of every step once with the step
  named in the error. Link errors (`DeclaredFileLinkError`): unknown step; step name shared by
  several steps; parameter not an output file of that step; several callables of the step declare
  it; producer value `None`; producer not earlier. An output parameter given a link is a `TypeError`.
  An unlinked missing input is still `FileNotFoundError` at compile.
- `require_one_writer_per_declared_file(compiled_contexts)` (`:425`, called at `compiler.py:1632`,
  right after `_compile_axis_values`) raises `SeveralWritersOfDeclaredFileError` naming two writers
  (step, callable, parameter, axis, group key) and the count of the rest. It counts invocations of
  plans with `owns_runtime_outputs`, so a step that runs once for the plate is one writer.

Run time:

- `CompiledFunctionInvocation.before_call` (`function_patterns.py:637`) runs each record's
  `before_call`. Called at the two places an invocation is called: per-axis
  `PatternGroupData.execute_chain` (`function_runtime.py:1508`) and the once-per-plate call
  (`bundle_execution.py:568`). A `LinkedInputFile` that does not exist raises `FileNotFoundError`
  naming the consumer call and the producer step and parameter. A written file is claimed in
  `ExecutingContext.declared_file_writes` (`processing_context.py:195`); a second claim of one path
  raises `SeveralWritersOfDeclaredFileError` naming both calls. The parent directory of a written
  file is created before the call, so a function needs no `mkdir`.

**Can the compiler enumerate the calls within one well? No, not for every step.** The number of
calls of one invocation in one well is the number of pattern groups (`function_execution.py:789`,
`_detect_patterns`). For the first step the grouped files come from the source projection, which the
compiler has. For every later step they come from `step_output_manifest(context).producer_paths_for(plan)`:
the files the previous step actually wrote in this execution. A function may return a different
number of planes than it received, so that set does not exist before the previous step ran. The
compile check therefore covers what compilation knows (wells, group keys, chain positions) and the
executor refuses the second call (test
`test_second_call_writing_a_declared_file_in_one_well_is_refused`). Consequence for authors: an
axis-scoped step with a declared output file compiles only on a one-well plate and runs only when
its grouping gives one call; the general case is the once-per-plate step of part B.

**Output directories.** `PlateOutputDirectory` has no user left in `openhcs/` after
`global_output_folder` got its own declaration. A directory is shared by the files written into it,
so the one-writer rule is not applied to it.

**Facts that differ from the brief or the design.**
- `pycodify_formatters.py` needed no change: it coerces only `str` to `Path`, and the dataclass
  formatter already emits `OutputFileOf` with its import. The round-trip test proves it.
- There are two call sites of an invocation, not one; the check is a method of the compiled
  invocation called from both.
- GUI: a function pane builds with an `OutputFileOf` value and returns it unchanged
  (`tests/unit/pyqt_gui/test_function_pane_file_of_earlier_step.py`). It is shown by the ordinary
  path widget; there is no editor for choosing a producer step. Not built here.
- MCP / function catalog describe the parameter from its annotation, which did not change; no code
  there reads the declaration family (grep: only `pycodify_formatters.py` outside `core/`).
- Ratchet: `PipelineCompiler` and `FunctionCoreExecutor` are over the class-size limit, so the
  resolver construction lives on `CompilationPathResolver` and the call check in
  `PatternGroupData.execute_chain`.
- New tests were written together with the change and were not observed failing first; the old
  behaviour is recorded by the research run (`e6`: bundle under the input plate).

**Deletion certificates.**
- `CallableContract.resolve_declared_paths`: **derived**. `CallableContract.declared_files` returns
  the records; the kwargs are `{record.parameter: record.path}` (`function_patterns.py:945`).
- `CompilationPathResolver.dataset_scope` field renamed `input_dataset` (two roots now): **contract**
  (no compatibility names).
- `PlateOutputDirectory` on `global_output_folder`, and relative output files resolving against the
  input plate: **contract** (this design, "What changes for existing callers"). Absolute paths are
  unchanged. A saved pipeline with a relative `compiled_execution_bundle_path` or `save_model_path`
  now writes under the output dataset.

**Left for part B.** Once-per-plate step with images and stages (a plate step must still be terminal,
so a consumer cannot yet follow a plate-scoped producer); the N2V2 acceptance; an editor for
`OutputFileOf` in the function pane if wanted.
