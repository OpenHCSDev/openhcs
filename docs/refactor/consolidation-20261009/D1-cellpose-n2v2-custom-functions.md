# D1 (demonstration): Cellpose and N2V2 as custom functions

Investigation, 2026-10-12, branch `feature/cellpose-n2v2-custom-functions`, PR #1230.
No file under `openhcs/**`, `external/**`, `paper/**`, `validation/**` or `benchmark/results/**` is
changed. Everything added is under `examples/custom_functions/`, one test file and this receipt.

**Thesis tested (owner):** the platform's function contract is enough to add a real
deep-learning tool as a user-written custom function.

**Verdict:** true for Cellpose inference and for N2V2 fit/denoise as functions: both register
through the user path, get controls and an MCP description from the signature alone, and run
through the execution server on CPU and on a GPU with no core change. It is false for three
things a deep-learning user needs: one trained model for a whole plate, running a
torch-declared function on a machine without CUDA, and preparation before readiness. One
unrelated core bug blocks any torch use in an ordinary install (gap 1).

## 1. Capability table

"Workaround" means the function or the run had to do something a user should not need to do.

| # | Capability | As a custom function today | Evidence | What the platform would need |
|---|---|---|---|---|
| 1a | Cellpose inference: stack in, label image out | **yes** | 50 official BBBC039 test fields compiled and run through the ZMQ execution server; 50 label TIFFs, 50 ROI zips, 50 count tables (`.claude/scripts/run_pipeline.py`, logs `run-cellpose-test*.log`) | nothing |
| 1b | Typed parameters become controls with no extra code | **yes** | offscreen `FunctionPaneWidget`: model = combo box (nuclei, cyto3, cyto2), diameter/thresholds = spin boxes, channels = tuple editor, do_3D = check box, a help button per parameter. Screenshot `D1-cellpose-controls.png` | nothing |
| 1c | Typed parameters become the MCP description with no extra code | **yes, one wording trap** | `FunctionCatalogService.get("openhcs:cellpose_segment")` returns each parameter with annotation, default, enum members and docstring text. A docstring continuation line that contains a colon is cut off (the parser reads it as a new parameter) | docstring parser: only treat `name:` at the argument indent as a new parameter |
| 1d | Label image and counts as typed outputs | **yes** | `ArtifactSpec(..., ObjectLabelsArtifactType)` and `MeasurementsArtifactType` in the custom source; the count table gets well/site/channel columns added by the platform | the editor templates only show the untyped tuple form (`templates.py:380-420`); add a typed-label template |
| 1e | A second custom function consumes the labels | **yes** | `measure_labelled_objects` declares `ArtifactSpec.input("cellpose_labels", ObjectLabelsArtifactType, parameter_name="labels")`; rows are tagged `object_name=cellpose_labels`. The compiler refused the first two attempts with exact messages (missing subject relation; relation pointing at an unknown spec) | nothing; the errors were sufficient |
| 2a | N2V2 as `fit` (images in, model file out) and `denoise` (model file + images in, images out) | **yes** | `n2v2_fit(model_file: PlateOutputFile)`, `n2v2_denoise(model_file: PlateInputFile)`; GPU pipeline runs: fit 24.3 s, denoise 4.1 s and 2.9 s; the two denoise runs give byte-identical output images (sha `ec8010ee…` twice) | nothing |
| 2b | Fit and denoise in one pipeline | **no** | compile fails: `Declared input file does not exist: …/authoring/models/probe.txt` (`vfs_protocol.py:153-166`, checked at compile in `compilation_session.py:102-121`) | link a later step's `PlateInputFile` to an earlier step's `PlateOutputFile` of the same resolved path |
| 2c | One model for the plate | **no** | default grouping: fit is called once per well (50 calls for 50 wells, each sees one plane), all 50 write the same file from 2 worker processes, last writer wins, no warning. Grouping by plate alone: `Duplicate source projection address`. Declaring the plate as the grouping field through the filename rule: `Generated virtual filename is not parser-readable` | see section 3, gap 3 |
| 2d | Rerun with the same model is deterministic | **yes** | two denoise runs on GPU: identical output hashes; unit test compares tensors on CPU | nothing |
| 2e | The compiled pipeline records which model each output came from | **path only** | the declared path is resolved to an absolute path at compile; no content hash; the recorded pipeline omits the path when it equals the default (`func=n2v2_denoise`) | hash declared input files into the plan and the output metadata |
| 3 | Preparation before readiness (weights, load, warm-up) | **with workaround, and late** | `@torch_function(prepare=_warm_up)` is accepted for a custom function. Cold start: server ready at 35.8 s without having run the hook; the hook ran in the first compile (15.0 s, of which 13.3 s weight download + load + warm-up). Worker processes are spawned per execution, re-execute the source and reload the model (0.13 s on CPU from cached weights; first call 4.2 s against 3.7 s steady) | run custom-function hooks in serving preparation; give the hook the step's parameters and device; see gap 5 |
| 4a | Torch tensors in and out through the declared memory type, device from the platform | **yes on a CUDA machine** | GPU check, GTX 1080: the function receives `torch.uint16` on `cuda:0` with values bit-identical to the file; no device code in the function except `image.device` | nothing |
| 4b | Mixed libraries around it with no manual conversion | **yes** | CuPy `percentile_normalize` → Cellpose (torch) → scikit-image measurement (NumPy). Trace: NumPy→CuPy host upload; CuPy→torch DLPack, shared buffer; torch→NumPy host download (section 2) | nothing to run it; visibility is gap 8 |
| 4c | The same torch-declared source on a CPU-only machine | **no** | compile: `No GPU device is available through: PyTorch.` (`framework_device_resolver.py:55-58`); direct calls of the registered function with CPU tensors work (unit tests) | gap 2 |
| 4d | Labels returned as GPU tensors | **no** | `can't convert cuda:0 device type tensor to numpy` at `runtime_object_label_building.py:150` | gap 4; the function returns the NumPy labels Cellpose produced |
| 5 | Optional dependency | **yes at registration; no at reload** | Without Cellpose: `ValidationError: Code execution failed: No module named 'cellpose'` at registration, nothing published. But a persisted source whose import fails later makes `load_all_custom_functions` fail and publishes none of the user's custom functions (`manager.py:217-262`) | gap 7 |
| 6 | Which Cellpose | 3.1.1.3 recommended | section 5 | — |
| 7 | Provenance in the outputs | **no** | the output dataset holds no pipeline code, function name, parameters, source hash or model hash (`openhcs_metadata.json` keys listed by `.claude/scripts/metadata_keys.py`; counts 0 for `cellpose_segment`, `pipeline`, `sha256`). The count table carries model and diameter only because the function writes them into its rows | gap 6 |

### Measured numbers

| Run | Device | Fields | Execute | Mean per-image F1 (IoU 0.5) | Pooled F1 | TP / FP / FN |
|---|---|---|---|---|---|---|
| Cellpose 3.1.1.3 `nuclei`, defaults, NumPy-declared variant (commit `47fbed348`) | CPU, torch 2.14.1+cpu, 1 process, 4 threads | 50 test | 185.9 s (3.7 s/field) | **0.9225** | 0.9439 | 5144 / 36 / 576 |
| Same model, torch-declared source (this branch) | GTX 1080, torch 2.6.0+cu124 | 50 test | 24.4 s (0.49 s/field) | **0.9137** | 0.9403 | 5196 / 136 / 524 |
| Manuscript, three agents (`paper/manuscript.md:151`) | — | 50 test | — | 0.898 to 0.903 | — | — |

Scorer: `benchmark.validation.scoring.instance_segmentation_metrics` (`scoring.py:307`), the one
behind the manuscript's agent numbers; references from `python -m benchmark.validation prepare`;
5,720 reference nuclei, matching `paper/manuscript.md:151`. Scoring 50 fields took under 10 s.

CPU and GPU results differ because Cellpose differs, not OpenHCS: in one process, on one
unchanged `uint16` field (20641_A12_7), `CellposeModel.eval` returns 18 objects on CPU and 45 on
the GPU (`.claude/scripts/probe_cpu_gpu_diff.py`). No label image is identical between the two
runs. The GPU run has one 7-nucleus field at F1 0.0 (CPU: 0.44). Whether this is specific to the
GTX 1080 is unknown until the check runs on a second GPU.

Main moved during this work (#1231, "no JIT after readiness", merged into this branch). The
cold preparation timing and the GPU check were repeated on the merged tree: the warm-up hook
still runs in the first compile after the server reports ready (hook 4.1 s inside a 4.3 s
compile), and the conversion table in section 2 is unchanged.

## 2. GPU and arraybridge (owner addition)

Correction to the brief: this machine's GTX 1080 is usable with torch 2.6.0+cu124 (the desktop's
torch) and CuPy 14.2; current torch (2.14.1+cu130) ships no `sm_61` kernels. All GPU results
below were run here in a private venv.

Conversions arraybridge performed in the three-step pipeline (4 fields, 2 runs, from
`examples/custom_functions/gpu_check/conversion_trace.py`):

| Boundary | Conversion | Route | Shares buffer | Calls | Requested by |
|---|---|---|---|---|---|
| disk → CuPy step | numpy (cpu) → cupy (cuda:0) | host upload | no | 8 | `core/memory/__init__.py:59 stack_runtime_slices` |
| CuPy step → Cellpose | cupy (cuda:0) → torch (cuda:0) | **DLPack** | **yes** (same device address) | 8 | same |
| Cellpose → NumPy step | torch (cuda:0) → numpy (cpu) | host download | no | 8 | same |
| Cellpose output → file | torch (cuda:0) → host | host download | no | 8 | `core/image_file_serialization.py:306 prepare` |

- The conversion happens when a step's input planes are stacked into its declared type on the
  device the compiler assigned (`framework_device_resolver.py`), one call per plane.
- `MemoryType.convert_to` (`external/arraybridge/src/arraybridge/types.py:995-1018`) tries DLPack and
  falls back to host; it logs only the fallback. The compiled plan stores each step's declared
  input and output memory type and device, not the conversion or its route. So the conversion is
  not visible today without a diagnostic (gap 8). The trace module is that diagnostic: a
  `sitecustomize.py` on `PYTHONPATH` wraps four `MemoryType` methods in the server and workers.
- Direct check, 16.8 MB array: CuPy→torch 0.18 ms shared buffer; torch→CuPy shared buffer;
  torch→NumPy 14 ms copy.
- **Cellpose forces one host copy.** In 3.1.1.3 and 4.2.1.1 `eval` documents NumPy input, and
  `transforms.convert_image` does `if torch.is_tensor(x): … x = x.cpu().numpy()` with the warning
  "torch array used as input, converting to numpy" (3.1.1.3 `transforms.py:474-476`; 4.2.1.1
  `transforms.py:486-489`). Masks come back as NumPy in both. A GPU tensor cannot go in without
  a host round trip unless `eval` is bypassed. Measured cost of that copy on the GTX 1080: 1.0 ms
  for a 520×696 field, 10.4 ms for 2048×2048, 367 ms for 8×2048×2048 (against about 490 ms per
  field of inference).
- Peak GPU memory during the pipeline: 1,243 MiB against a 333 MiB baseline, so about 0.9 GB for
  Cellpose 3 `nuclei` on 512×512 images.
- GPU timings: server ready 22 to 25 s, first compile 1.7 to 2.8 s (includes the warm-up hook),
  execute run 1 3.1 to 6.3 s, run 2 1.2 s for 4 fields.

### GPU check, ready to run

Needs in one environment: OpenHCS from this branch, torch with CUDA, `cupy-cuda12x`,
`cellpose==3.1.1.3` (which pins `numpy<2.1` and will downgrade NumPy, tifffile, imagecodecs and
roifile). The desktop does not have Cellpose, so the owner must install it there or use a
separate venv; I did not touch the desktop.

```bash
git fetch origin feature/cellpose-n2v2-custom-functions && git checkout FETCH_HEAD
python examples/custom_functions/gpu_check/run_gpu_check.py --work-dir /tmp/openhcs-gpu-check
# prints: environment; direct conversions; Cellpose host copy; timings; conversions per boundary
# writes: /tmp/openhcs-gpu-check/gpu_check_report.json, pipeline.py, conversions.jsonl
```

It will fail at server start ("The execution server did not become ready") unless either CuPy,
JAX and TensorFlow are all importable or gap 1's one-line fix is applied. I ran it here with that
line changed locally and reverted it before committing.

## 3. Platform gaps, ranked

| Rank | Gap | Evidence | Smallest change that closes it |
|---|---|---|---|
| 1 | **Catalogue preparation crashes when torch is installed and CuPy, JAX or TensorFlow is not.** The server never becomes ready; the client only reports a failed connect. | `dxf_mask_pipeline.py:316` returns `Union["torch.Tensor", "cp.ndarray", "jnp.ndarray", "tf.Tensor"]`; `get_type_hints` evaluates `cp.ndarray` with `cp = None`: `AttributeError: 'NoneType' object has no attribute 'ndarray'`. `OPENHCS_CPU_ONLY=1` avoids it by hiding every torch function. | Annotate the return as `"torch.Tensor"` (one line). Then surface the server's preparation error in the client's connect failure. |
| 2 | **The torch memory type means "GPU".** A torch-declared function cannot compile without CUDA, so one source cannot serve CPU and GPU machines, and the N2V2 prototype raises `CUDA required`. | `framework_device_resolver.py:55-58`; `compiled_step_plan.py:514-541`; arraybridge `MemoryType.TORCH.is_gpu`. | Let the resolver assign the CPU device for frameworks that have one (torch, JAX, TensorFlow) when no GPU is present, with `device_id=None`; keep the error for CuPy and pyclesperanto. |
| 3 | **One model for the plate cannot be expressed.** (a) No image step receives more than one well: the plate scope takes only `RuntimeArtifactBatch` and forbids memory types (`funcstep_contract_validator.py:884-910`). (b) A declared output file of one step is not linked to a declared input file of a later step. (c) Many invocations resolving one declared output path overwrite each other silently. | Experiments E1 to E5, `.claude/scripts/grouping_experiments.sh`. | (c) first, it is a correctness hole: reject at compile a `PlateOutputFile` whose resolved path is shared by more than one invocation. (b): accept a `PlateInputFile` that an earlier step declares as `PlateOutputFile`, and order on it. (a): allow a plate-scoped callable to declare a memory type and receive the stacked images of all wells, or a sample of them. Untested route that may work today: an axis step emits training patches as an artifact, a plate-scoped custom function (precedent `export_to_spreadsheet`) writes the model, and denoising runs as a second pipeline. |
| 4 | **Label artifact outputs bypass the memory-type conversion.** A label stack returned as a CUDA tensor crashes. | `runtime_object_label_building.py:150` `np.asarray(self.labels)`. | Convert there through `MemoryType(detect_memory_type(labels)).to_numpy(labels)`. |
| 5 | **Preparation is late and blind for custom functions.** The hook runs at first compile, not before readiness; it takes no arguments, so it cannot prepare the model or device the step selected; workers do not inherit what it loaded. | section 1 row 3; `callable_contract.py:2049-2093`; `registry_service.py:180-200`. | Include published custom functions in `prepare_in_current_process`. Then pass the hook the step's resolved parameters at compile. Relates to `R1d-catalog-prepare-cold-start.md`. |
| 6 | **Outputs carry no provenance.** | section 1 row 7. | At execution, write beside `openhcs_metadata.json` the submitted pipeline code, the content hash of each custom source it uses (already computed: `CustomFunctionSource.content_sha256`), and the hash of each declared input file. |
| 7 | **One custom source with a missing import disables all persisted custom functions**, and in CPU-only mode a torch-declared function registers but is absent from the catalogue (`UnknownFunctionIdError`). | `.claude/scripts/probe_missing_dep_startup.py`; `manager.py:217-262`. | Publish the sources that load; report each failing source by name with its import error. |
| 8 | **Conversions are invisible.** | section 2. | arraybridge: one debug record and counter per conversion (pair, device, route, shared buffer). Plan inspection: show the declared type pair at each step boundary. |
| 9 | **Declared paths resolve against the input plate.** The model lands in the source dataset (`…/authoring/models/n2v2.pt`). | `compilation_session.py:102-121`. | Resolve `PlateOutputFile` against the output dataset root. |
| 10 | Smaller: recorded pipelines omit parameters equal to defaults, so the model name and model path are not visible in the record; enum parameters appear in the MCP entry under a mangled path (`…__openhcs_source_<sha>.__openhcs_member_<hex>`); `import os` is forbidden in custom sources (`validation.py:108-122`) while `pathlib` does the same things; label file names carry no site (no collision here, one site per well; not tested with several). | logs under `.claude/logs/`. | Record defaults in the stored pipeline; show the enum's own name in the catalogue entry. |

## 4. Other facts established

- Registration path: GUI `pyqt_gui/main.py:1604` and MCP `function_catalog_service.py:769` both call
  `CustomFunctionManager.register_from_code` (`manager.py:127`); the tests and scripts use that call.
- One source may declare exactly one decorated function (`manager.py:520`), so fit and denoise are
  two files. Helper classes (enum, row dataclass) in the same source are fine.
- Memory decorators do not convert on a direct call; the executor does. A direct call must pass
  the declared type.
- `torch.save` embeds the file's own name in the archive: two identical models saved under
  different names differ in bytes. Compare contents, or hash under one name.
- N2V2 here is a mechanism demonstration. A 3-epoch fit made a synthetic image worse (RMSE 954
  against 400 noisy). No denoising quality is claimed.
- Cellpose writes weights to `~/.cellpose/models` unless `CELLPOSE_LOCAL_MODELS_PATH` is set.
- Disk: `/home` went from 38 GB to 24 GB free during this work; about 12 GB is mine
  (`.claude/venv` 2.4 GB, `.claude/venv-gpu` 9 GB, data 0.2 GB) and can be deleted.

## 5. Which Cellpose

| | 3.1.1.3 (2026-01-09) | 4.2.1.1 (2026-06-14, Cellpose-SAM) |
|---|---|---|
| Weights | `nuclei`, `cyto2`, `cyto3`: 26.6 MB each, from `cellpose.org/models` | `cpsam_v2` 1.23 GB (default), `cpdino` 1.21 GB, from Hugging Face `mouseland/cellpose-sam` |
| Model choice | `model_type="nuclei"` works | only `cpsam_v2`, `cpdino`, `cpdino-vitb`, `cpsam`; `model_type` ignored; unknown names silently load `cpsam_v2` |
| Dependencies | `numpy<2.1`, numba, torch≥1.6 | torch, torchvision, `segment_anything`; `cpdino` needs DINOv3 from git |
| `eval` input | NumPy; tensors copied to host | NumPy; tensors copied to host; `channels` ignored; no diameter estimation |
| GPU memory | about 0.9 GB measured here | 8.90 GB GPU RAM for a 1200 px image in Cellpose's own table (RTX 4070S) |
| CPU | 3.7 s per 520×696 field measured here | no published CPU timing; about 46 times more weights; not tested |
| Code licence | BSD-3-Clause (LICENSE file; the README badge says "GPL v3", which contradicts it) | same file |
| Weights licence | not stated on the files | Hugging Face card: `license: bsd-3-clause` |
| Training data | README: "All models in Cellpose, except yeast_BF_cp3, yeast_PhC_cp3, and deepbacs_cp3, are trained on some amount of data that is CC-BY-NC" | README: "All Cellpose models are trained on data that is licensed under CC-BY-NC" |

**Recommendation: 3.1.1.3 for the demo.** It runs on CPU, fits an 8 GB card with room to spare
(Cellpose-SAM's own figure is above 8 GB), has a nuclear model, and keeps the typed parameters
meaningful. Cost: it holds NumPy below 2.1. The manuscript should state the CC-BY-NC training-data
note; whether that restricts use of the weights is not stated by the authors and is not ours to
decide. No weights are in this repository. `cpdino` is under Meta's DINOv3 licence, not an OSI
licence; do not use it. Sources: PyPI JSON for both versions, the LICENSE and README at tags
`v3.1.1.3` and `v4.2.1.1`, `huggingface.co/mouseland/cellpose-sam`, HTTP HEAD on the weight URLs.

## 6. Manuscript proposal (no file under `paper/` is edited)

**What can honestly be claimed**

1. A published deep-learning segmenter was added as one user-written Python file (about 150
   lines, most of it docstring and declarations) with no change to OpenHCS; its controls and
   MCP description were generated from the signature and docstring. This replaces the toy.
2. In one pipeline, a CuPy step, the torch-declared Cellpose step and a scikit-image step
   exchanged images with no conversion code; CuPy to torch stayed on the GPU through DLPack with
   a shared buffer; the hand-off to NumPy copied to host. This is the first direct evidence for
   the sentence at `paper/manuscript.md:244-246` ("NumPy, CuPy, PyTorch … can share one pipeline").
3. Not claimable: "runs on any machine" (gap 2), "the output records the model" (gap 6), one model
   per plate for N2V2 (gap 3), zero-copy end to end (Cellpose's `eval` copies to host).

**Figure 1 (II), replace the gain/offset toy** (`paper/manuscript.md:67`, `:74`): left, the
`cellpose_segment` declaration (signature and three docstring lines); middle, the generated
controls (`D1-cellpose-controls.png` is the offscreen render: model drop-down, diameter, channel
pair, two thresholds, 3D check box); right, the MCP parameter entry for `model` with its enum
members. Caption addition: "the function is the laboratory's own file; Cellpose is not an
OpenHCS dependency".

**Optional panel or supplementary figure:** the three-step pipeline with the library and device
of each step and the conversion at each boundary (table in section 2), plus per-field time, CPU
against GPU.

**Text, Results, after the sentence on Caicedo et al. (`:151`)**, if the owner wants the number:
"As a check that a current deep-learning method fits the same workflow, we registered Cellpose
(v3, pretrained nuclear model, default settings) as a custom function. On the same 50 test images
and with the same scoring it reached a per-image mean F1 of 0.92 on CPU and 0.91 on a GPU. The
model was trained on images from this dataset, so this is not a held-out result."

**Is it a fair, cheap addition?** Cheap: yes. 50 fields take 24 s on the GPU or 3 min on CPU, and
scoring under 10 s, with the manuscript's own scorer and reference preparation; the 175-field
subset needs the 200-field layout the agents used and would take about 12 min on CPU. Fair: only
as a workflow demonstration, not as a comparison with the agents, for three reasons. The
pretrained model was trained on BBBC039 images (see below). The agents tuned classical functions
without a trained model, which is the manuscript's point. The Cellpose number depends on the
device (0.9225 against 0.9137), so the device must be stated.

**Training-data overlap: confirmed.** The Cellpose preprint's Methods ("Nucleus data",
bioRxiv 10.1101/2020.02.02.931238v1) say the nuclear model was trained on 1,139 images, 111 held
out by the authors' own split, and: "We used image set BBBC039v1 …, which consists of 200
fluorescent images of U2OS with the Hoechst stain. Some of these images overlap with the
BBBC038v1, so we only used the unique images, which were 157 images in total." The BBBC039 page
confirms the partial overlap with BBBC038 (the 2018 Data Science Bowl set). Not established:
how many of the 50 official test images were in Cellpose's training portion, and whether the
later torch weights (`nucleitorch_0`) used the identical set. The sentence proposed above should
therefore read "the model was trained on images from this dataset" rather than "not known to
exclude".

## 7. Sources and tests

| File | What it is |
|---|---|
| `examples/custom_functions/cellpose_segment.py` | torch-declared Cellpose inference; labels + counts as typed outputs; warm-up hook |
| `examples/custom_functions/measure_labelled_objects.py` | NumPy/scikit-image per-object table from the label artifact |
| `examples/custom_functions/n2v2_fit.py`, `n2v2_denoise.py` | fit to a declared output file; denoise from a declared input file; network reused from `openhcs/processing/backends/enhance/n2v2_processor_torch.py` |
| `examples/custom_functions/gpu_check/` | `run_gpu_check.py`, `conversion_trace.py`, `sitecustomize.py` |
| `tests/unit/test_example_custom_functions.py` | 4 tests |

`examples/` held one file before this; `examples/custom_functions/` is a new directory, one file
per function because the manager stores one function per file under its own name.

Test results observed:

- shared `.venv` (no torch, no Cellpose): `2 passed, 2 skipped` (skips: "torch is an optional
  dependency"). The two that run: the measurement function, and the Cellpose source being rejected
  at registration when its import fails.
- private CPU venv (torch 2.14.1+cpu, Cellpose 3.1.1.3), `OPENHCS_CPU_ONLY=1`: `4 passed`.
- private GPU venv (torch 2.6.0+cu124, CuPy 14.2, Cellpose 3.1.1.3): `4 passed`.
- `guardrails_local.sh`: GUARDRAILS_RESULT

Not tested: Cellpose 4; `do_3D` and two-channel input; CuPy or torch on a second GPU; several
sites per well; a plate-scoped custom function; the GUI editor dialog itself (the manager call
behind it was used); the MCP transport (the service method behind it was used).

## Progress notes

All seven questions and the GPU addition are answered above. Left for a follow-up, each a core
change and so outside this PR: gaps 1 to 9. Scratch scripts and logs are under the worktree's
`.claude/` (not committed).
