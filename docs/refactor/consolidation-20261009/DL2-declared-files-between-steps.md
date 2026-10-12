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
record per declared file parameter with the parameter name, the resolved path, the declaration class
(input or output) and, for a linked input, the producer `(step index, parameter)`. DL3 hashes from
that list; DL2 computes no hash.

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
- [ ] part A: declaration roots, `OutputFileOf`, single writer, `declared_files`
- [ ] part B: plate scope with images, stages
- [ ] N2V2 acceptance, gates, PR
