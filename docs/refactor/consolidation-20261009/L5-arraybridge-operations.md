# L5: Per-backend processors written once against arraybridge

**Head audited:** `openhcs` `main` at `b987b7b89` (#1190); `arraybridge` `main` at `31632d8` (0.3.8). **Rules:** [00-RULES.md](00-RULES.md). **Step 2** (replaces C4 in [01-INDEX.md](01-INDEX.md)).
**Shared abstractions:** none from [02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md). *Builds:* the `ArrayOperations` family in arraybridge, keyed by memory type, with `ArrayOperations.for_memory(...)`. *Uses:* `EnumKeyedStrategyMixin` for the projection and spatial-bin families.

## What is wrong

**Six processor modules restate the same image operations once per array library, and the arraybridge family that already models "what differs per array library" is reached through a string roster.**

`openhcs/processing/backends/processors/` holds `numpy_processor.py` (1,086 lines), `cupy_processor.py` (1,235), `torch_processor.py` (868), `jax_processor.py` (768), `tensorflow_processor.py` (835) and `pyclesperanto_processor.py` (819): 5,611 lines, plus `percentile_utils.py` (187), which already writes percentile normalization once against injected `percentile_func`/`clip_func`/`ones_like_func` callables.

Census at `b987b7b89`. Thirteen names are defined in all six files (78 definitions); `_gaussian_blur` in three; `spatial_bin_2d`, `spatial_bin_3d` and `crop` in two. Each cell says how the backend's definition relates to the others: **=** identical modulo the array library (the same steps, each step one library call), **≠** a genuinely different algorithm or numeric rule that per-backend parity must keep.

| Operation | numpy | cupy | torch | jax | tensorflow | pyclesperanto |
|---|---|---|---|---|---|---|
| `_validate_3d_array` | = | = | = | = | = | = (shape only) |
| `create_weight_mask` | = | = | = | = | = | = |
| `create_linear_weight_mask` | = | = | = (ramp includes its endpoint) | = | = (ramp includes its endpoint) | ≠ min(1, distance/margin) ramps |
| `apply_mask` | = | = | = | = | = | ≠ native `multiply_images`, no float32 detour |
| `max_projection` | = | = | = | = | = | = (z-projection kernel) |
| `mean_projection` | = | = | = | = | = | ≠ keeps the float32 z-mean, no cast back |
| `create_projection` + per-file strategy family | = (+MIN) | = | = | = | = | = except MEAN (above) |
| `spatial_bin_2d`/`_3d` + per-file strategy family | = | = | – | – | – | – |
| `crop` | = | = | – | – | – | – |
| `stack_equalize_histogram` | = | = | ≠ `histc` + floor lookup | ≠ `take` lookup, own bin width | ≠ `histogram_fixed_width` | ≠ 3-D CLAHE |
| `percentile_normalize` | = | = | ≠ `quantile`, sampling above 10M, uint16 output | ≠ `isclose`, uint16 output | ≠ floor-index percentile | ≠ min/max |
| `stack_percentile_normalize` | = | = | ≠ | ≠ | ≠ | ≠ min/max |
| `create_composite` (weight validation) | = | = | ≠ skips weights ≤ 0, no normalization check | = | ≠ takes a list of stacks | = |
| `create_composite` (arithmetic) | ≠ numba kernel, NumPy pairwise order | = | ≠ | = | ≠ | ≠ native kernels |
| `sharpen` | ≠ scikit-image | ≠ vectorized ndimage | ≠ zero-padded blur | ≠ reflect-padded blur, int→uint16 | ≠ `tf.image` blur | ≠ native, no normalization |
| `tophat` | ≠ scikit-image | ≠ ndimage + own resize | ≠ unfold morphology | ≠ per-pixel loops | ≠ depthwise conv | ≠ `top_hat_sphere` |

Totals: the six files hold 145 top-level definitions (numpy 34, cupy 36, torch 17, jax 18, tensorflow 17, pyclesperanto 23). Identical modulo the array library: 55 definitions of 13 operations (counting composite weight validation separately). Genuinely different: 31 definitions (`sharpen` ×6, `tophat` ×6, histogram equalization ×4, percentile normalization ×8, composite arithmetic ×4, and pyclesperanto's linear mask, `apply_mask` and `mean_projection`). Backend-only operations (numpy 7, cupy 7, pyclesperanto 4) are not restatements.

Restated mechanisms beyond the operations:
- Five copies of a `StackProjectionStrategy` family (numpy, cupy, torch, jax, tensorflow, pyclesperanto: six roots, 13 leaves) and two copies of a `SpatialBinStrategy` family (numpy, cupy: two roots, 8 leaves), all with the same dispatch.
- Six copies of the framework-import boilerplate (`optional_import_placeholder`, the `OPENHCS_SUBPROCESS_NO_GPU` branch in three files, `_check_pyclesperanto_available`, the TensorFlow version probe).
- `PyclesperantoMaskDimensionality` is an enum whose `apply` branches on `self is MASK_2D` (rule 1a).
- In arraybridge, `MemoryType` reaches its `ArrayOperations` leaf through a string field naming a module-level singleton (`"NUMPY_OPERATIONS"` … six constants); the leaf does not know its memory type.

Defects found while measuring (kept, because parity is the acceptance check; listed for the owner):
- TensorFlow: every decorated call fails in arraybridge with `Cannot interpret 'tf.uint16' as a data type` (the TensorFlow leaf inherits the NumPy `dtype_name`; the `_tensorflow_dtype_name` helper is unused; fixed in this surface's arraybridge PR); undecorated, `sharpen` calls `tf.image.gaussian_blur` (not a TensorFlow API), percentile normalization and histogram equalization fail on dtype mismatches, and `tophat`'s "erosion" is a sum convolution.
- torch: `tophat` raises in `F.pad`; decorated `max_projection`, `mean_projection` and `sharpen` on uint16 are nondeterministic run to run on the desktop GPU (the undecorated bodies are deterministic).
- pyclesperanto 0.19: `apply_mask` (2-D mask), `create_composite` and `equalize_histogram_per_slice` fail on plane assignment (`index_x`).

## Target

arraybridge owns what differs per array library:

```python
class ArrayOperations(ABC, metaclass=AutoRegisterMeta):   # keyed by memory_type
    memory_type: ClassVar[str | None] = None
    @classmethod
    def for_memory(cls, memory_type) -> ArrayOperations   # one instance per leaf
    module                                                 # the framework, imported on first use
    accepts, astype, max, min, mean, sum, prepend_axis,    # primitives that differ per library
    linspace, ones, assign, outer, floor
class NumpyArrayOperations(MutableArrayOperations): memory_type = "numpy"
...                                                        # one leaf per memory type
```

`MemoryType` finds its leaf with `ArrayOperations.for_memory(self)`; the operations-name field and the six `*_OPERATIONS` constants are deleted.

OpenHCS writes each shared operation once, in `processors/image_stack_operations.py`, against an `ArrayOperations` leaf: stack validation, weight masks, mask application, max/mean/min projection and `create_projection` (one `StackProjection` family), spatial binning (one `SpatialBin` family), crop, histogram equalization and percentile normalization for the NumPy-compatible libraries, composite weight validation and the weighted composite. `percentile_utils.py` is folded in and deleted. Each backend module keeps only its registrations: a decorated declaration per public name (registered identity, signature and contract unchanged) that calls the shared operation with its leaf, plus the operations that genuinely differ (the ≠ cells). Framework names for annotations stay `optional_import_placeholder` handles (the decorators evaluate annotations at registration, so a lazy proxy would import or fail on every absent framework); the three `OPENHCS_SUBPROCESS_NO_GPU` branches, `_check_pyclesperanto_available`, the TensorFlow version probe and `PyclesperantoMaskDimensionality` are deleted.

Decision with a default: `NumpyStackProjectionMethod` stays as numpy's `create_projection` annotation, because saved pipelines import it (rule 2 forbids changing durable pipelines without an owner decision). `StackProjectionMethod` gains `MIN`; both enums key the one `StackProjection` family by value.

## Guards

`tests/unit/test_processor_operations_written_once.py`:
- AST: no backend module defines a class keyed by `StackProjectionMethod`/`SpatialBinMethod`, a `_validate_3d_array`, or reads `OPENHCS_SUBPROCESS_NO_GPU`; `percentile_utils.py` does not exist.
- AST: every function defined in two or more backend modules delegates to a shared operation, except the census's ≠ cells (listed once in the test).
- Each backend's `OPERATIONS` is `ArrayOperations.for_memory` of its own memory type.
- In arraybridge: `types.py` has no `_OPERATIONS` string and `array_operations.py` no module-level operations instance; every `MemoryType` resolves a leaf through `ArrayOperations.for_memory`.

## Tests

- arraybridge: one family test (every `MemoryType` has exactly one leaf; `for_memory` returns it; primitives on NumPy).
- OpenHCS: one family test over the six backends: each `create_projection` method enum is served by the `StackProjection` family; the shared operations agree with the NumPy reference on the installed backends. `test_processor_method_strategies.py` is rewritten to the family level.
- Numeric parity per backend (not committed): every public declaration on fixed inputs, before and after, decorated and undecorated; NumPy and JAX here, CuPy, torch, TensorFlow and pyclesperanto on the desktop GPU.

## New-case experiments

Today a new array library needs a sixth copy of every shared operation. After: one `ArrayOperations` leaf in arraybridge with the primitives, and one registration per operation.

## Done when

Every = cell above is a delegation to one shared operation; the per-file strategy families, validators and import boilerplate are gone; parity holds per backend; the guards pass; the arraybridge PR is open with a minor bump and green CI.

## Result

Measured on the branch (`image_stack_operations.py` 435 lines; the six backend modules 4,141 lines, from 5,611; `percentile_utils.py` deleted).

Numeric parity, every public declaration on fixed uint16/uint8/float32/constant stacks (`.claude/l5/parity_harness.py`, not committed), called decorated and undecorated, before (`b987b7b89`) and after:

| Backend | Where | Cases | Exact | Changed |
|---|---|---|---|---|
| numpy | here and desktop | 236 | 236 | none (the unregistered `min_projection` helper is deleted; `create_projection(MIN)` replaces it) |
| jax (CPU) | here and desktop | 140 | 140 | +6 new `create_projection(MIN)` cases |
| cupy | desktop RTX 2070 SUPER | 282 | 282 | +6 MIN |
| pyclesperanto 0.19 | desktop GPU (OpenCL) | 188 | 188 | +6 MIN |
| torch 2.6 (CUDA) | desktop GPU | 70 undecorated | 70 | +MIN; decorated calls are nondeterministic on main itself (two main runs differed in 2 of 70 decorated cases); after, 1 to 2 decorated cases differ per run, in operations this surface did not change |
| tensorflow 2.19 (GPU) | desktop GPU | 70 undecorated | 62 same, 8 error→value | `create_projection` (6) and `create_weight_mask` (2) used to fail through the nested decorated call; their values now equal TensorFlow's own projection and mask bodies. Decorated calls, all failing on main, now run and equal the undecorated results (33 values, 40 same errors) |

Exact means bitwise-equal arrays and equal dtypes; errors compare by exception type. No case needed a tolerance. JAX on the GPU could not be checked: the desktop's JAX CUDA plugin finds no visible GPU, so JAX ran on the CPU on both machines.
