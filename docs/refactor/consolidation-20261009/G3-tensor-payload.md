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

## Target (as built)

```python
# core/payload_axes.py — the declared dimensions of a tensor payload
class SpatialAxis(AxisRole)                                  # role of a spatial dimension
class AxisSpec(ABC): name; roles; has_role(role)             # one declared dimension
class FamilyAxisSpec(AxisSpec):       axis: type[Axis]       # a G1 family axis; roles from its MRO
class ColourSampleAxisSpec(AxisSpec)                          # colour samples of one source image (ColourAxis)
class SpatialAxisSpec(AxisSpec):      axis_name              # named by the spatial domain
class RuntimePlaneAxisSpec(AxisSpec): plane_axis_name        # the leading runtime plane axis
class UndeclaredAxisSpec(AxisSpec)
class PositionedAxis: spec; position                          # rank-relative (negative counts from the end)
class PayloadAxes: declared                                   # replaces source_channel_axis
    with_axis / without_role / position_of(role) / index_of(role, ndim) / indices(ndim)
    after_leading_axis_removed() / common_after_stacking(...) / colour_samples(position)

# core/runtime_image_values.py — the tensor payload family (A1)
class ImagePayload(RuntimeArrayPayload, RuntimeSliceProjectableValue, SpatiallyPlacedValue):
    data; metadata; mask; geometry; memory_type; axes          # axes: one AxisSpec per dimension
    of(value)                                                  # wrap a bare array once
    with_metadata / with_pixels / mask_for_data / slice_payload / intensity_scale / copied
    alignment_slices / map_slices / runtime_slice_count / value_for_slice / aligned_value
    project_declared_source / contextualize_image_output / fill_output_source_context /
    object_label_output / main_output_slices / output_stack_copy / plane_axis_for_output_context
class PlainImagePayload(ImagePayload)    # bare pixels: no metadata, no mask; undeclared-output defaults
class ImageMetadataPayload, MaskedImagePayload
# ImagePayloadSliceStack (AlignedImageStack, ProducedImageStack, ImageOutputBundle) and
# ObjectLabelValue are members and override what differs.
```

- **Decided where values enter.** `payload_with` always returns an `ImagePayload`. A bare array becomes a payload exactly where it enters: a processing function's image arguments (`image_payload_boundary` in the OpenHCS memory decorator, innermost, so direct, runtime and slice-by-slice calls all pass through it: the primary argument when it declares a payload type, other arguments that declare `ImagePayload`; bare pixels in give bare pixels out; composed raw leaves in `neurite_outgrowth.py` use the same boundary), the main-flow argument (`CallableMetadata.raw_main_flow_call_argument`), the CellProfiler intensity domain (`normalize_cellprofiler_image_payload`), measurement-image sources, a function's returned image (`owned_runtime_value` in `execute_chain`, the image and label kinds' contextualization and the CellProfiler main-flow output; `ImagePayload.of` on volumetric-to-slice results), memory-store values before storage writes, loaders (`SourceFileUniverse.load_images`, `ImagePayloadSourceMetadataContext`, `NamedSourceBinding.apply_loaded_payload`, workspace projection), the image file codec, and stack/label-builder construction. The 51 processing-function parameters annotated `RuntimeArrayData` that read payload fields now annotate `ImagePayload`. **Deleted:** `image_payload_data`, `image_payload_metadata`, `image_payload_mask`, `image_payload_geometry`, `with_image_payload_data`, `image_payload_slice_context`, `image_payload_mask_for_slice`, `image_mask_for_data_domain`, `image_payload_intensity_scale`, `normalize_image_payload_intensity`, `ImagePayloadMetadataCarrier` and every `isinstance` against it (486 accessor calls and 18 checks).
- **Slices on members.** `alignment_slices`/`output_slices`/`map_slices` live on the slice family (`ImagePayload`, `ImagePayloadSliceStack`, `ObjectLabelValue`, `RuntimeSliceAlignedValueSet`). **Deleted:** `payload_slices_for_alignment`, `flatten_aligned_image_payload_slices`, `payload_slice_count`. `RuntimeSliceAlignedValueSet` gains `values`/`map_slices`; its index accessor is `value_at`. The hand-written slice loops in `artifacts.py` (10), `runtime_slice_alignment`, `interop/.../invocation.py`, `measurement_image_alignment.py`, `function_runtime.py` and the four batch copies of `execute_one(i) for i in range(slice_count)` (now `RuntimePure2DSliceBatchRequest.execute_each()`) are gone.
- **One slice mechanism.** `RuntimeSliceProjectableValue` owns `runtime_slice_count`, `value_for_slice`, `identity_projected_value`, `full_stack_value`, `aligned_value`, `declared_plane_axis`, `alignment_slices`, `output_slices`, `map_slices`; `RuntimeSliceIndexedValue`, `RuntimeSliceInvariantValue` and `RuntimeSliceIdentityProjectableValue` are its capability subclasses. Image payloads, slice stacks, object labels, aligned value sets, columnar rows, measurement tables, sparse IJV rows, relationships and spatial graphs are members. `RuntimeSliceProjection` handles only foreign values (tuples/lists recurse, arrays and primitives pass through, anything else is rejected). **Deleted:** `RuntimeSliceProjectionStrategy` and its 16 leaves; `ImageOutputSourceContextStrategy` (4 leaves) and `ObjectLabelOutputValueContextStrategy` (5 leaves), now methods on the source and output members; the `singledispatch` `project_declared_source_identity` (3 registrations), now `project_declared_source` on the members; the `SourceSpatialDomainAdapter` type-keyed registry, now `SpatiallyPlacedValue.spatial_adapter`; the `RuntimeProjectionSourceIdentityRequirement` enum and its strategy table, now `OptionalSourceIdentity` / `RequiredSourceComponentMetadata`.
- **Declared axes.** `ImagePayloadMetadata.axes: PayloadAxes` replaces `source_channel_axis` (122 lines); kernel code asks by role (`axis_index(ColourAxis, data)`), any number of axes may be declared, composition shifts all of them, and mask domains accept masks without any declared axis. `ImagePayload.axes` resolves one `AxisSpec` per dimension.
- **N-d spatial rank family.** `SourceSpatialDomain` members are keyed by `spatial_rank` and declare `axis_names`: `PointSourceSpatialDomain` (0), `LineSourceSpatialDomain` (1, `x`), the planar `SourceSpatialDomain` (2, `y x`) and `VolumeSourceSpatialDomain` (3, `z y x`). Spatial axis specs, planar placement axes, the object-label adapter, `CENTER_*` (the location features are derived from the volume domain's names, the three generated strategy leaves are deleted) and the IJV columns (from the planar domain's names) derive from it. Crop placement (`origin_yx`, `source_shape_yx`) stays planar.
- **Domain-declared defaults.** `AxisFamily.payload_spatial_rank` is required on every family (microscopy: 2). The default `SourceSpatialDomain` of payload metadata, the rank checks that used to read `ndim < 3` (`dense_shape_carries_axis`, runtime-slice counts, source-binding projection, selected-plane outputs) and `spatial_axes_yx` derive from it: an undeclared array of rank *r* is `r − k` undeclared axes followed by the `k` spatial axes of the family's domain. `ImageShapeRole`, its five leaves, the 14 `is_*` helpers and `image_spatial_axis_indices` are deleted (dead).
- **Function runtime.** The three output switches are payload methods (`declares_whole_image_output`, `main_output_slices`, `owns_output_surfaces`, `output_stack_copy`, `plane_axis_for_output_context`).
- **artifacts.py (minimum for K2).** Image and label kinds call payload methods; `materialization_image_metadata` is a kind method (`ImagePayloadArtifactKind` capability for images and labels); the slice loops are gone.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Worker bundles, compiled plans, metadata caches, viewer image metadata | runtime | reset (`source_channel_axis` becomes `axes`; spatial domains always carry `spatial_dimensions`) |

No durable format stores payload metadata.

## Guards

`tests/unit/test_g3_tensor_payload_guards.py` (AST over `openhcs/`):
- No definition, call or import of the deleted accessors and helpers.
- No name `ImagePayloadMetadataCarrier`, `RuntimeSliceProjectionStrategy`, `ImageOutputSourceContextStrategy`, `ObjectLabelOutputValueContextStrategy`, `ObjectLocationCoordinateProjectionStrategy`, `ImageShapeRole`, `ArrayShape`.
- `ImagePayloadMetadata` has no `source_channel_axis` field; no `normalized_source_channel_axis`/`without_source_channel_axis`/`is_declared_source_channel_*`/`channel_axis_without_leading_plane`/`non_channel_axes` attribute anywhere.
- No `range(<x>.slice_count)` in the G3 modules, `artifacts.py` or `function_runtime.py` (only `RuntimeSliceAlignedValueSet.values` defines it).
- Location features and IJV columns equal the spatial domains' names; no `"center_x"`/`"y"`/`"x"` literals in their modules.

## Tests

- Witness (`tests/unit/test_axis_family_witness.py`): a `Telemetry` family (station, window, sensor, time; `payload_spatial_rank = 0`) declares 1-D time-series payloads; they resolve declared axes by role, have no spatial axes, stack onto a runtime-slice axis, slice back, round-trip through the metadata codec and take masks without their declared axes, with no kernel edits. `RemoteSensing` declares its spatial rank.
- Strategy-registry structure tests are deleted (`test_aligned_image_payload_registry.py` 10, two static deletion gates enforcing the old registries); behaviour tests are rewritten onto the family (`.data`, `ImagePayload.of`, `project_declared_source`, `contextualize_image_output`, `object_label_output`).
- 30-workflow CellProfiler parity (baseline 29/30; `cp_tutorial_3d_monolayer` fails on a `.pkl` serializer error).

## New-case experiments

- A new payload kind: before, a `RuntimeSliceProjectionStrategy` leaf, a branch in `payload_slices_for_alignment`, an adapter registration, an output-context strategy and accessor support. After: one `ImagePayload` (or `RuntimeSliceProjectableValue`) subclass overriding what differs.
- A new declared axis on a payload (a time axis on a signal): before impossible (one `source_channel_axis` slot). After: one `PositionedAxis(FamilyAxisSpec(axis), position)`.
- A non-planar domain: before every payload was 2-D YX. After: the family declares `payload_spatial_rank` (the witness declares 0).

## Done when

The accessor functions, the carrier name, the strategy and adapter tables, the copied switch and the loops are gone; `source_channel_axis` is replaced by declared axes; `SourceSpatialDomain` is a rank family whose names feed masks, labels, `CENTER_*` and IJV; the guards and the witness pass; the touched tests and the parity check are green at baseline.

## Handoff (recorded for later surfaces)

- **Plane modes are still an enum (former K1 item, unassigned).** `RuntimePlaneAxis` (`RUNTIME_SLICE`/`SOURCE_BINDING`) with its `EnumKeyedStrategyMixin` strategy family, and `ImagePayloadMetadataCompositionMode` (`STACK`/`BUNDLE`), which restates it one-to-one, should become one plane-axis family. 96 member references in 35 files, including the Fiji/Napari wire decode (G6). Needs an owner.
- **K2:** kind-generic layers hold values of every artifact kind and still ask "is this an image?" in one place: `image_metadata_of` / `array_data_of` (`core/runtime_image_values.py`), used by `RuntimeProjectedPayloadItem`, materialization items and plane counts, output recording, measurement recording, source-bound provenance, `VolumetricToSliceProcessingContract` and the image kind's materialization metadata (about 20 call sites, down from 486). They go away when each artifact kind owns its metadata. `ImageArtifactType.contextualize_output` still type-switches its *output* (`SourceProjectedImageOutput`, `RuntimeSliceAlignedValueSet`, non-image values pass through); the label kind rejects non-image outputs by type.
- **G5:** `PrimaryImageCarrierRequirement.SOURCE_CHANNEL_AXIS` (`callable_contract.py`) is an enum naming the colour axis; it should be a role requirement. `Pure2DInputSlicer` and the PURE_2D auxiliary aggregators in `unified_registry.py` are type-keyed tables over payload types; `ImagePayloadPure2DAuxiliaryOutputAggregator` now also receives `PlainImagePayload` outputs and `PlainImagePayloadPure2DInputSlicer` is registered for wrapped main-flow values. `contextualize_main_image_output` and `CellProfilerFunctionContractExecutor` still accept bare main images from array-annotated callables.
- **G6:** viewer modules read `metadata.axis_position(ColourAxis)` where they read `source_channel_axis` (mechanical lines in `runtime/napari_viewer_server.py`, `runtime/napari_streaming_handlers.py` and `core/viewer_streaming_service.py`, which also reads `.data/.metadata/.mask`); the wire still carries `SOURCE_CHANNEL_AXIS` and planar `origin_yx`/`source_shape_yx` (zmqruntime), and should carry declared axes and N-d placement.
- **G4:** source loaders call `ImagePayload.of` at entry; the `NamedSourceBinding.source_channel_axis` config field and the image format's `pixel_semantics.channel_axis` are file-level declarations converted with `PayloadAxes.colour_samples`.
