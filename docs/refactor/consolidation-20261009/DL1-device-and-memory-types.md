# DL1: where a function runs and what array type crosses its boundary

Branch `refactor/DL1-device-and-memory-types`. Answers gaps 2, 4 and 8 of
`D1-cellpose-n2v2-custom-functions.md` (PR #1230). Status at the bottom is the truth about what
is finished; read it first when resuming.

## What was wrong

1. **A declared memory type meant "needs a GPU" (gap 2).** arraybridge 0.4 gave each library an
   `is_gpu` flag (torch = True) and every device was an `int` GPU id. The resolver
   (`framework_device_resolver.py:55-58`) raised "No GPU device is available through: PyTorch"
   on a machine without CUDA, and `OPENHCS_CPU_ONLY=1` hid every non-NumPy function from the
   catalogue (269 of 333 functions left in a GPU environment; a torch-declared custom function
   registered but was absent, `UnknownFunctionIdError`).
2. **Label outputs bypassed the host copy (gap 4).** Traced on a real torch step: main-flow
   image outputs are never converted from the declared output type; they stay in their library
   and reach host memory only in `ImageFileFormat.prepare` when a file is written. Label outputs
   enter a NumPy-only family at `ImagePayload.object_label_output` when the value is saved,
   before any writer, and were passed raw. Every non-NumPy label failed, torch on CPU included.
3. **Conversions were invisible (gap 8).** Only DLPack failures were logged; the plan stored
   declared types, not conversions.

## Target

- A function declares the array library it speaks. The device is assigned by the platform from
  what the library has (asked of `arraybridge.libraries.ArrayLibrary`: `host_devices()`,
  `accelerator_devices()`); the plan states the device and the rule that assigned it.
- One owner copies a function's array to host: `openhcs/core/runtime_array_values.py:host_array`.
- The plan states the conversion that will happen at each step boundary
  (`arraybridge.conversion.ConversionRoute.planned`), and a run reports the conversions that did
  happen (`ConversionCounters` installed in each worker, merged, sent on the existing
  progress/metadata channel, printed as one table per run).

Scope change during the job (coordinator): arraybridge itself was refactored and released as
0.5.0 by another agent (AB1); this job only consumes it. Nothing was pushed to ArrayBridge from
this job.

## Done (committed and pushed)

### Label outputs (gap 4)
`host_array(value)` is the only host copy in `openhcs/core`. The file writer, the label builder
(`ImagePayload.object_label_output`), `ImagePayload.array_data` (what every file writer
receives; fixes ROI materialization of a GPU mask), `RuntimeArrayPayload.__array__`,
materialization payload equality and equivalence hashing call it. Two sites that read through
NumPy only for shape and indexing (image outputs of per-slice sources; mask slicing) no longer
convert at all. Deleted: two duplicate `__array__` methods and a separate
`convert_memory(..., NUMPY, 0)` in `equivalence/arrays.py` (`canonical_numpy_array` renamed
`contiguous_host_array`). Tests: `tests/unit/test_function_output_host_array.py`,
`tests/integration/test_label_outputs_in_any_array_library.py`, fixtures copied verbatim from
#1230 under `tests/fixtures/custom_functions/`. Before the arraybridge migration these gave, in
the GPU environment (real `cuda:0` tensor, real CuPy, Cellpose variant returning tensor labels),
`22 passed` (unit) and `24 passed` (both files); shared environment `9 passed, 13 skipped` and
`2 passed, 3 skipped`.

### Device rule (gap 2), production code
`openhcs/core/device_assignment.py`: registered family `DeviceRule`, tried in declaration order:
`OnlyHostDevices`, `AcceleratorsExcluded`, `PreferredAcceleratorPresent`,
`PreferredAcceleratorAbsent`, `NoAcceleratorPresent`. The first rule that applies assigns; if
it offers no device the compile error names the library and says it has no host device. No
library name appears in the rules. The plan holds `DeviceAssignment` with one
`AssignedDevice(placement, rule)` per declared library, NumPy included; the rule instance is the
reason. Shown by `AssignedDeviceSummary` (`openhcs/agent/dto/execution.py`) and
`PipelineArtifactPlanRenderer._step_lines`, e.g. `device: torch on host (no accelerator is
present)`. `ArrayPlacement(library, device)` in `runtime_array_values.py` replaces every
`(memory_type, device_id | None)` pair.

### `OPENHCS_CPU_ONLY`
Now means "this process is assigned no accelerator" (`accelerators_excluded()`). The catalogue
filter is derived from the rules (`DeviceRule.rules_out`), so only libraries without a host
device (CuPy, pyclesperanto) are hidden. Deleted: `gpu_imports_disabled`,
`OPENHCS_SUBPROCESS_NO_GPU`, `POLYSTORE_SUBPROCESS_NO_GPU` (no reader anywhere),
`supports_cpu_only`. Kept: `JAX_PLATFORMS=cpu` (still needed; belongs on the JAX library class
in arraybridge). Nothing ever blocked an import under the flag (`lazy_gpu_imports.py` does not
read it).

### Pins
`external/arraybridge` at `v0.5.0`; `arraybridge>=0.5.0,<0.6`.

## Deletion certificates

| Deleted | Why | Covered by |
|---|---|---|
| `openhcs/core/framework_device_resolver.py`, `FrameworkDeviceBinding`, `FrameworkDeviceAssignment`, `gpu_memory_types`, `requires_gpu`, `device_id_for` | derived from the library family | `DeviceRule`, `DeviceAssignment`; `tests/unit/test_device_assignment.py` |
| `tests/unit/test_framework_device_resolver.py` | asserted the old rule ("CPU-only rejects torch" is deliberately reversed) | `test_device_assignment.py` |
| `tests/unit/test_memory_type_authority.py` | asserted identity of re-exports arraybridge 0.5.0 removed | none needed |
| `openhcs.core.memory` forwarding re-exports, `openhcs.constants` `*_MEMORY_TYPES` / `MEMORY_TYPE_*` | forwarding only | importers import arraybridge |
| `composition_memory_domain`, `keeps_memory_type` in `artifacts/kinds.py` | both branches differed only by a hard-coded device 0 | `ArrayPlacement.of` |
| `convert_input(source_memory_type)` parameter | the payload knows its placement | — |
| `supports_cpu_only`, `_cpu_only_mode_enabled` | derived | `DeviceRule.rules_out` |
| `gpu_imports_disabled`, the two `*_NO_GPU` keys | no reader | — |
| duplicate `__array__` methods; `canonical_numpy_array` | one owner | `host_array` |

## Found, outside this job (for dispatch)

**Measurement row cells are not validated against the row type.** Reproduction: a custom
function declared with `@torch`, returning a measurement row dataclass with a field
`count: int`, sets `count=torch.tensor(1, device="cuda:0", dtype=torch.int32)`; the pipeline
succeeds; the CSV cell reads `tensor(1, device='cuda:0', dtype=torch.int32)`.
`runtime_tabular_values.py:87 validate_fields` checks names only.

Other candidates: `openhcs.constants.MemoryType` is still a re-export with about 100 importers;
`interop/cellprofiler/runtime/output_recording.py:387` is a second caller passing `value.data`
to the label request (NumPy-only callers today); the pytest-qt switch in `tests/conftest.py:76`
rides on the CPU-only flag though it is a headless switch.

## What should change on the #1230 branch

- `examples/custom_functions/cellpose_segment.py`: nothing required. The docstring sentence
  "The labels stay the NumPy array Cellpose returned: OpenHCS builds label artifacts from host
  arrays." is no longer a constraint and should go. To return labels in the declared type:
  return annotation `np.ndarray]` → `torch.Tensor]`, last line `labels` →
  `torch.from_numpy(labels).to(image.device)`.
- `n2v2_fit.py` raises `CUDA required` itself: expected to become "use the device of the input
  tensor"; exact lines not yet checked.
- `gpu_check/conversion_trace.py` and its `sitecustomize.py` become unnecessary once the
  observed-conversions report exists.

## Status: NOT finished. Remaining, in order

State of the branch: production migrated; **OpenHCS does not import without a test-only
stand-in** because PolyStore 0.6.2 uses names arraybridge 0.5.0 removed
(`polystore/constants.py:7`, `array_payload.py:22`). PolyStore 0.6.3 is being released by
another agent; then: check `external/PolyStore` out at that tag, raise the `polystore>=` pin,
drop the stand-in (`.claude/shim`, untracked, never to be committed).

1. Test migration. Last measured on 18 device/payload unit files (shared environment, with the
   stand-in): `121 failed, 268 passed, 13 skipped, 3 errors`. Causes and files are listed in the
   sub-agent hand-over: hand-built `CompiledStepPlan`s that never assign devices (about 60),
   `compose(memory_type=…)` / `ProducedImageStack(memory_type=…)`, imports of
   `FrameworkDeviceAssignment`, old flag keys, `supports_cpu_only` fakes, monkeypatches on the
   `MemoryType` class, three-argument `stack_runtime_slices`. 319 test files import touched code
   (`.claude/touched_tests.txt`, untracked).
2. Tally against `/home/ts/code/projects/openhcs/.claude/verify/AB1-callers.md` (104 OpenHCS
   sites; 11 non-test sites passed GPU id 0 to a NumPy target): not yet counted.
3. GPU-environment runs of the migrated tree in three modes (as is; `CUDA_VISIBLE_DEVICES=`;
   `OPENHCS_CPU_ONLY=1`): none run yet. Includes the three-mode test that one torch-declared
   source compiles and runs, the CuPy "no host device" compile error, JAX on host, the Cellpose
   example with `CUDA_VISIBLE_DEVICES=`, aligned image output on torch CPU.
4. CPU-only open items: catalogue size and preparation time before/after;
   `test_no_jit_after_readiness.py`; whether fork-child Numba preparation
   (`processing_preparation.py:47`) is safe once torch may be loaded in the parent; "CUDA is
   never initialised under the flag" (suspected arraybridge defect: its execution wrapper may
   call `torch.cuda.current_device()` whenever a GPU exists; forwarded for 0.5.1, stack not yet
   captured).
5. **Gap 8 in OpenHCS, not started:** planned conversion per step boundary in the compiled plan
   (from `ConversionRoute.planned(source_library, source_device, target_library,
   target_device)` over the assigned devices, including disk → first step and last step → file);
   `ConversionCounters` installed in each worker, merged per run and sent on the existing
   progress/metadata channel; one readable table per pipeline run; a test that planned equals
   observed.
6. Demo: CuPy → Cellpose (torch) → scikit-image (NumPy) pipeline from #1230 on the GTX 1080
   with planned and observed tables matching; same torch source with `CUDA_VISIBLE_DEVICES=`.
7. Reword the two commits titled WIP; gates (`verify_branch.sh` under `heavy_slot.sh`,
   `smoke_local.sh`, `guardrails_local.sh`, parity under `official30.lock`); PR.

GPU environment for resuming (deleted at the end of the job; rebuild if absent):
`uv venv --python 3.12 .claude/venv-gpu && uv pip install --python .claude/venv-gpu/bin/python
-e ".[dev]" torch==2.6.0 cupy-cuda12x cellpose==3.1.1.3 pytest-xdist scikit-image
--extra-index-url https://download.pytorch.org/whl/cu124 --index-strategy unsafe-best-match`
(6.7 GB; it lacks pytest-qt, so tests need a stand-in plugin directory on `PYTHONPATH`).
