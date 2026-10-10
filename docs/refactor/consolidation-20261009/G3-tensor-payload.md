# G3: Tensor payload with declared axes

**Head audited:** `openhcs` `main` at `1c1059867` (#1172). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.** Replaces K1.
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "The tensor payload". **Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* A1 (`ImagePayload` family methods). *Uses:* G1 `Axis`/`AxisFamily`/`AxisRole`, `RuntimeSliceProjectableValue`, `AutoRegisterMeta`.

## What is wrong

**Whether a runtime value is a bare array or a metadata carrier is re-decided at about 500 call sites, the payload knows one special axis and assumes the rest are Y/X, and two mechanisms answer "how does this value split into runtime slices" (IDEN-1, IMPL-1, IMPL-2, MEMB-2).**

Measured at this head (production = Python under `openhcs/`):

- **Re-decided type.** `image_payload_data/metadata/mask/geometry` (`core/runtime_image_values.py:1507-1536`) each `isinstance` a value against `ImagePayloadMetadataCarrier` and fall back to "bare array". Calls: `image_payload_data` 154, `image_payload_metadata` 239, `image_payload_mask` 62, `image_payload_geometry` 31 (486 in 69 files), plus 18 direct `isinstance(…, ImagePayloadMetadataCarrier)` checks. The cause is `ImagePayloadMetadata.payload_with` (`:982`), which returns the bare array when the metadata is empty, and the callable boundary (`CallableMetadata.raw_main_flow_call_argument`, `core/callable_contract.py:498`), which passes a payload only when the primary annotation admits its type, so the 66 processing functions annotated `RuntimeArrayData` (= payload | ndarray) receive either.
- **One special axis.** `ImagePayloadAxisFields` (`:324-432`) declares exactly `source_channel_axis: int | None` beside `plane_axis`; composition shifts it by hand (`_ImagePayloadMetadataComposer.composed_source_channel_axis`, `channel_axis_without_leading_plane`). 122 production lines name `source_channel_axis`.
- **Hard-coded YX.** `spatial_axes_yx` (`:381-386`) takes the last two non-channel axes; `ObjectLabelPayloadSourceSpatialDomainAdapter.spatial_axes_yx` (`aligned_image_payload.py:334-342`) the last two array axes; `ImageMaskDomain` accepts exactly two spatial axes (`:2213`).
- **Rank guessing.** `ImageShapeRole` and its five leaves plus 14 `is_*_image_*` helpers and `image_spatial_axis_indices` (`core/image_shapes.py:50-250`) guess colour/volume from rank and trailing size. **Nothing in the tree calls them** (verified: no importer in `openhcs/`, `tests/`, `benchmark/`, `scripts/`): dead code.
- **2-D only.** `SourceSpatialDomain` (`core/source_spatial_domain.py:64`) is the 2-D owner with a 3-D `VolumeSourceSpatialDomain`; there is no lower-rank instance, and its default instance is hard-wired as the default of every `ImagePayloadMetadata` (`SourceSpatialDomainFields`, `:534`), so the kernel, not the domain, decides that undeclared payloads are 2-D.
- **Copied switch.** `payload_slices_for_alignment` (`aligned_image_payload.py:1950-1992`) is a 4-type `isinstance` switch whose carrier and object-label branches are copies; `flatten_aligned_image_payload_slices` and `payload_slice_count` wrap it.
- **Two mechanisms, one question.** `RuntimeSliceProjectionStrategy` (`core/runtime_slice_projection.py:386-1033`, 16 leaves keyed by value type) runs beside the `RuntimeSliceProjectableValue` ABC (`core/runtime_plane_projection.py:19`); `RuntimeSliceProjectableValueProjectionStrategy` forwards from one to the other. The same type-keyed shape is restated by `ImageOutputSourceContextStrategy` (4 leaves) and `ObjectLabelOutputValueContextStrategy` (5 leaves) in `core/projected_image_output.py`.
- **Payload dispatch three times.** `steps/function_runtime.py` `_project_output_slices` (:1066), `_save_outputs` (:1200) and its nested `plane_axis_for_output` (:1234) each switch over `ImagePayloadMetadataCarrier` / `ImagePayloadSliceStack` / bare array.
- **Hand-written loops.** `for … in range(x.slice_count)` 32 times (11 in `artifacts.py`, 5 in `aligned_image_payload.py`).
- **Fixed spatial names.** `ObjectCoreMeasurementFeature.CENTER_X/Y/Z` with three generated strategy leaves restating axis offsets −1/−2/−3 (`core/runtime_measurements.py:990-1090`); `SparseIJVLabelRows.YX_LABEL_FIELDS` spells `y`/`x` (`core/runtime_sparse_labels.py:24-28`).

## Target

```python
# core/payload_axes.py
class AxisSpec(ABC):                       # one declared tensor dimension
    name: str; roles: tuple[type[AxisRole], ...]
class FamilyAxisSpec(AxisSpec):  axis: type[Axis]       # a G1 family axis; roles from the axis
class SpatialAxisSpec(AxisSpec): name                   # named by the SourceSpatialDomain rank
class ColourSampleAxisSpec(AxisSpec)                     # colour samples inside one source image (ColourAxis)
class RuntimePlaneAxisSpec(AxisSpec): plane_axis        # the leading runtime plane axis
class UndeclaredAxisSpec(AxisSpec)                       # dimension nothing declared
@dataclass(frozen=True) class PositionedAxis: spec; position   # rank-relative position
class PayloadAxes: declared: tuple[PositionedAxis, ...]  # replaces source_channel_axis
    with_axis / without_role / index_of(role, ndim) / shifted_for_leading_axis(±1) / resolve(ndim, spatial_rank)

# core/runtime_image_values.py
class ImagePayload(RuntimeSliceProjectableValue, ABC):   # was ImagePayloadMetadataCarrier
    data; metadata; mask; geometry; memory_type; axes (per-dimension AxisSpec tuple)
    with_metadata(m); alignment_slices(); map_slices(fn); runtime_slice_count()
    @classmethod of(value) -> ImagePayload                 # the one bare-or-payload decision
class PlainImagePayload(ImagePayload)                     # a bare array, empty metadata
class ImageMetadataPayload, MaskedImagePayload            # unchanged members
# ImagePayloadSliceStack (Aligned/Produced/ImageOutputBundle) and ObjectLabelValue are members.
```

- **Decided once.** `payload_with` always returns an `ImagePayload`. The value is wrapped once at each boundary where a bare array can enter: the primary argument of a processing function whose annotation is `ImagePayload` (the OpenHCS memory decorator, so direct and runtime calls share it), the function return in `steps/function_runtime.py`, and image loading. Functions that want arrays annotate an array type and receive `payload.data`. **Deleted:** `image_payload_data`, `image_payload_metadata`, `image_payload_mask`, `image_payload_geometry`, `normalize_image_payload_intensity`'s switch, every `isinstance(…, ImagePayloadMetadataCarrier)`, `RuntimeArrayData` as a primary-image annotation.
- **Slices on members.** `ImagePayload.alignment_slices()` replaces `payload_slices_for_alignment`, `flatten_aligned_image_payload_slices` and `payload_slice_count`; `RuntimeSliceAlignedValueSet` gains `values`/`map_slices`, replacing the hand-written loops.
- **One slice mechanism.** Every owned runtime value implements `RuntimeSliceProjectableValue` (`runtime_slice_count`, `value_for_slice`, `full_stack_value`, `aligned_value`, `identity_projected_value`). `RuntimeSliceProjection` handles only foreign values at the boundary (sequences recurse, other foreign values pass through). **Deleted:** `RuntimeSliceProjectionStrategy` and its 16 leaves, `ImageOutputSourceContextStrategy` and `ObjectLabelOutputValueContextStrategy` families (their cases become methods on the source/output members).
- **Declared axes.** `ImagePayloadMetadata.axes: PayloadAxes` replaces `source_channel_axis`; any number of declared axes with roles; kernel code asks by role (`ColourAxis`). `ImagePayload.axes` resolves one `AxisSpec` per dimension.
- **N-d spatial rank family.** `SourceSpatialDomain` members are keyed by `spatial_rank` and declare `axis_names`: rank 0 (no spatial axes), rank 1 (`x`), rank 2 (`y, x`, the planar instance) and rank 3 (`z, y, x`). Spatial `AxisSpec`s, `ImageMaskDomain` spatial axes, the object-label adapter, `CENTER_*` features and IJV columns derive their names and positions from it. Crop placement (`origin_yx`, `source_shape_yx`) stays planar: it is the viewer wire's shape (G6).
- **Domain-declared defaults.** The active `AxisFamily` declares `payload_spatial_domain` (microscopy: planar). An undeclared array of rank *r* resolves to `(undeclared × (r − k), spatial × k)` for that domain's rank *k*: the default-axes-by-rank table is derived, not written. `ImageShapeRole` and the `is_*` helpers are deleted (dead).
- **Function runtime.** The three output switches become calls on the output payload (`output_slices`, `plane_axis_for_output_context`, `copy_output_stack`).
- **artifacts.py (minimum for K2).** Loops over `RuntimeSliceAlignedValueSet` call `values`/`map_slices`; image `isinstance` checks call payload methods. The remaining `isinstance` kind checks on owned value types are recorded for K2.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Worker bundles, compiled plans, metadata caches, viewer image metadata on the wire | runtime | reset (`source_channel_axis` key becomes `axes`) |

No durable format stores payload metadata.

## Guards

`tests/unit/test_g3_tensor_payload_guards.py` (AST over `openhcs/`):
- No definition or call of `image_payload_data`, `image_payload_metadata`, `image_payload_mask`, `image_payload_geometry`, `payload_slices_for_alignment`, `flatten_aligned_image_payload_slices`, `payload_slice_count`.
- No name `ImagePayloadMetadataCarrier`, `RuntimeSliceProjectionStrategy`, `ImageOutputSourceContextStrategy`, `ObjectLabelOutputValueContextStrategy`, `ImageShapeRole`, `source_channel_axis`.
- No `for … in range(<expr>.slice_count)` in the owned modules and `artifacts.py`.
- No string literal `"center_x"`/`"center_y"`/`"center_z"` or IJV `"y"`/`"x"` field spellings in `core/runtime_measurements.py`/`core/runtime_sparse_labels.py`.

## Tests

- One family test over the `ImagePayload` members (data/metadata/mask/alignment slices/runtime slicing).
- Witness: extend `tests/unit/test_axis_family_witness.py` with a 1-D time-series family whose payloads (declared time axis, rank-0 spatial domain) are stacked, sliced, projected and composed by the payload layer with zero kernel edits.
- Tests of deleted helpers are deleted; tests that called the accessors use payload attributes.
- The 30-workflow CellProfiler parity check (baseline 29/30; `cp_tutorial_3d_monolayer` fails on a `.pkl` serializer error).

## New-case experiments

- A new payload kind: today it needs a `RuntimeSliceProjectionStrategy` leaf, a branch in `payload_slices_for_alignment`, and accessor support. After: one `ImagePayload` subclass.
- A new declared axis on a payload (a time axis on a signal): today impossible (one `source_channel_axis` slot). After: one `PositionedAxis(FamilyAxisSpec(axis), position)`.
- A non-planar domain: today every payload defaults to 2-D YX. After: the family declares `payload_spatial_domain`.

## Done when

The accessor functions, the carrier name, both strategy families, the copied switch and the loops are gone; `source_channel_axis` is replaced by declared axes; `SourceSpatialDomain` is a rank family with axis names consumed by masks, labels, `CENTER_*` and IJV; the guards and the witness pass; the touched tests and the parity check are green at baseline.

## Handoff (recorded for later surfaces)

Filled in at delivery.
