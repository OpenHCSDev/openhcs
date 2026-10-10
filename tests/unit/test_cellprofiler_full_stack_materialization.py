"""Dense full-stack ABI must consume aligned source/artifact values correctly."""

from dataclasses import replace

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    AlignedImageStack,
    ImageOutputBundle,
    ImagePayloadExecutionMode,
    ImagePayloadStackComposition,
    ImagePayloadSliceStack,
    compose_aligned_image_payload,
)
from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.core.callable_contract import CallableContract, CallableMetadata
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
)
from openhcs.core.runtime_object_labels import ObjectLabelPayload, ObjectLabelVariantData
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.runtime_spatial_graph import SpatialGraph, SpatialGraphNode
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.processing.backends.cellprofiler.intensity import rescale_intensity
from openhcs.processing.backends.cellprofiler.morphology import remove_holes, remove_holes_3d
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.runtime_image_values import ImagePayload


def test_real_rescale_full_stack_materializes_composed_runtime_sources():
    data = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    ).payload_with(data, None)
    composition = compose_aligned_image_payload(
        "synthetic source inputs", (source, source)
    )
    assert isinstance(composition.payload, AlignedImageStack)
    contract = CallableContract.from_callable(rescale_intensity)
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        composition.payload,
        {},
        execution_mode=contract.runtime_image_execution_mode,
    )
    expected = np.stack((data, data), axis=1) / 23.0
    np.testing.assert_allclose(result.data, expected)


@pytest.mark.parametrize("function", (remove_holes, remove_holes_3d))
def test_literal_volume_keeps_dense_contract_semantics_without_bundle_classification(function):
    pixels = np.ones((60, 6, 8), dtype=np.float32)
    pixels[20:22, 2:4, 3:5] = 0
    mask = np.ones(pixels.shape, dtype=bool)
    mask[:, 0, 0] = False
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_voxel_spacing=SourceVoxelSpacing(
            (1.25, 2.5, 3.0), SourceVoxelSpacingUnit.MICROMETERS,
        ),
        source_spatial_domain=SourceSpatialDomain(source_shape_yx=(6, 8)),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/inputs/source_{index}.tif" for index in range(60)),
            component_metadata=tuple({"site": str(index)} for index in range(60)),
        ),
    )
    dense = metadata.payload_with(pixels, mask)
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=60,
    )
    literal = ImagePayloadSliceStack.from_output_slices(
        tuple(RuntimeSliceProjection.value_for_slice(dense, projection.selected_plane(index))
              for index in range(60)),
        memory_type="numpy", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    assert not isinstance(literal, AlignedImageStack)
    composition = compose_aligned_image_payload("literal volume", (literal,))
    assert composition.execution_mode is ImagePayloadExecutionMode.NATURAL
    assert composition.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert literal._composed_payload is None
    contract = CallableContract.from_callable(function)
    contract = replace(contract, metadata=replace(
        contract.metadata, artifact_outputs=(ArtifactSpec.output("Filled", ImageArtifactType),),
    ))
    executor = CellProfilerFunctionContractExecutor()
    outputs = tuple(
        executor.execute(
            contract, contract.resolve_canonical_raw_callable(), value, {},
            execution_mode=compose_aligned_image_payload("volume", (value,)).execution_mode,
            plane_projection=projection,
        )
        for value in (dense, literal)
    )
    np.testing.assert_array_equal(ImagePayload.of(outputs[1]).data, ImagePayload.of(outputs[0]).data)
    np.testing.assert_array_equal(ImagePayload.of(outputs[1]).mask, ImagePayload.of(outputs[0]).mask)
    assert ImagePayload.of(outputs[1]).metadata == ImagePayload.of(outputs[0]).metadata


@pytest.mark.parametrize("processing_contract", tuple(ProcessingContract))
@pytest.mark.parametrize("slice_count", (1, 2))
def test_every_full_stack_processing_family_materializes_image_and_image_kwargs(
    processing_contract, slice_count
):
    planes = tuple(
        np.full((3, 4), index, dtype=np.float32) for index in range(slice_count)
    )
    aligned = AlignedImageStack(planes)
    opaque = RuntimeSliceAlignedValues(("not an image",))
    calls = []

    def dense_callable(image, *, reference, token):
        calls.append((image, reference, token))
        assert not isinstance(image, AlignedImageStack)
        assert not isinstance(reference, AlignedImageStack)
        assert token is opaque
        np.testing.assert_array_equal(image.data, np.stack(planes))
        np.testing.assert_array_equal(reference.data, np.stack(planes))
        return image

    contract = CallableContract(
        func=dense_callable,
        function_name="dense_callable",
        module_name="DenseProbeModule",
        metadata=CallableMetadata(processing_contract=processing_contract),
    )
    kwargs = {"reference": aligned, "token": opaque}
    # Retain the PURE_3D prohibition on slice-aligned non-image kwargs.
    if processing_contract is ProcessingContract.PURE_3D:
        with pytest.raises(ValueError, match="runtime-slice-aligned kwargs.*token"):
            CellProfilerFunctionContractExecutor().execute(
                contract,
                dense_callable,
                aligned,
                kwargs,
                execution_mode=ImagePayloadExecutionMode.FULL_STACK,
            )
        assert calls == []
        kwargs["token"] = None
        opaque = None
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        dense_callable,
        aligned,
        kwargs,
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )
    assert len(calls) == 1
    np.testing.assert_array_equal(result.data, np.stack(planes))
    assert kwargs["reference"] is aligned


def test_aligned_materialization_retains_masks_calibration_and_exact_contributors():
    spacing = SourceVoxelSpacing((1.25, 2.5, 3.0), SourceVoxelSpacingUnit.MICROMETERS)
    sources = []
    expected_paths = []
    for channel, alias in ((1, "DNA"), (2, "actin")):
        paths = tuple(f"/synthetic/A01_s{site}_w{channel}.tif" for site in (1, 2))
        expected_paths.extend(paths)
        metadata = ImagePayloadMetadata(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            source_image_names=(alias,),
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                paths=paths,
                component_metadata=tuple(
                    {"well": "A01", "site": str(site), "channel": str(channel)}
                    for site in (1, 2)
                ),
            ),
            source_voxel_spacing=spacing,
            source_dtype="uint8",
            intensity_scale=255.0,
            source_spatial_domain=SourceSpatialDomain(
                source_shape_yx=(3, 4), origin_yx=(0, 0)
            ),
        )
        pixels = np.full((2, 3, 4), channel, dtype=np.float32)
        mask = np.ones_like(pixels, dtype=bool)
        mask[0, 0, 0] = False
        sources.append(metadata.payload_with(pixels, mask))
    composed = compose_aligned_image_payload(
        "matched synthetic inputs", tuple(sources)
    ).payload
    dense = RuntimeSliceProjection.full_stack_value(composed)
    assert dense.shape == (2, 2, 3, 4)
    metadata = dense.metadata
    assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert metadata.source_voxel_spacing == spacing
    assert metadata.source_spatial_shape_yx == (3, 4)
    assert set(metadata.source_provenance.represented_source_image_names) == {
        "DNA",
        "actin",
    }
    assert {
        identity.path
        for identity in metadata.source_provenance.represented_source_identities
    } == set(expected_paths)
    np.testing.assert_array_equal(
        dense.mask,
        np.stack(
            [
                np.broadcast_to(plane.mask, (2, 3, 4))
                for plane in composed.slices
            ]
        ),
    )
    for index in range(2):
        projected = RuntimeSliceProjection.value_for_slice(
            dense,
            RuntimePlaneAxisValueProjection.from_selected_plane(
                axis=RuntimePlaneAxis.RUNTIME_SLICE, plane_index=index, axis_size=2
            ),
        )
        np.testing.assert_array_equal(
            projected.data, composed.slices[index].data
        )
        expected = {f"/synthetic/A01_s{index + 1}_w{channel}.tif" for channel in (1, 2)}
        assert {
            identity.path
            for identity in projected.metadata.source_provenance.represented_source_identities
        } == expected


def test_named_output_bundle_materializes_its_own_source_binding_axis():
    planes = tuple(np.full((3, 4), index, dtype=np.float32) for index in (1, 2))
    bundle = ImageOutputBundle(
        planes,
        tuple(
            AlignedImageSliceContext.main_flow(name, artifact_kind="image")
            for name in ("red", "green")
        ),
    )
    dense = RuntimeSliceProjection.full_stack_value(bundle)
    assert dense.metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    assert dense.metadata.source_provenance.represented_source_image_names == ("red", "green")
    np.testing.assert_array_equal(dense.data, np.stack(planes))
    assert all(
        slice_payload.data is plane
        for slice_payload, plane in zip(bundle.slices, planes, strict=True)
    )


def test_named_bundle_preserves_outer_aliases_with_real_inner_plane_provenance():
    spacing = SourceVoxelSpacing((1.25, 2.5, 3.0), SourceVoxelSpacingUnit.MICROMETERS)
    payloads = []
    for channel, alias in enumerate(("red", "green"), start=1):
        metadata = ImagePayloadMetadata(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            source_image_names=(alias,),
            source_voxel_spacing=spacing,
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                paths=tuple(f"/synthetic/{alias}_s{site}.tif" for site in (1, 2)),
                component_metadata=tuple(
                    {"site": str(site), "channel": str(channel)} for site in (1, 2)
                ),
            ),
        )
        payloads.append(metadata.payload_with(np.full((2, 3, 4), channel), None))
    bundle = ImageOutputBundle(
        tuple(payloads),
        tuple(AlignedImageSliceContext.main_flow(alias) for alias in ("red", "green")),
    )
    dense = RuntimeSliceProjection.full_stack_value(bundle)
    metadata = dense.metadata
    assert metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    assert metadata.source_image_names == ("red", "green")
    assert metadata.source_provenance.source_plane_count == 2
    assert metadata.source_voxel_spacing == spacing
    for index, alias in enumerate(("red", "green")):
        selected = RuntimeSliceProjection.value_for_slice(
            dense,
            RuntimePlaneAxisValueProjection.from_selected_plane(
                axis=RuntimePlaneAxis.SOURCE_BINDING, plane_index=index, axis_size=2
            ),
        )
        np.testing.assert_array_equal(
            selected.data, payloads[index].data
        )
        selected_metadata = selected.metadata
        assert selected_metadata.source_image_names == (alias,)
        assert {
            identity.path
            for identity in selected_metadata.source_provenance.represented_source_identities
        } == {f"/synthetic/{alias}_s{site}.tif" for site in (1, 2)}


def test_new_calibrated_nominal_stack_reaches_real_callable_without_dispatch_edits():
    spacing = SourceVoxelSpacing((1.25, 2.5, 3.0), SourceVoxelSpacingUnit.MICROMETERS)

    class CalibratedAlignedImageStack(AlignedImageStack):
        """A generated acquisition grid owns one additional metadata fact."""

        def composition_payload_metadata(self, metadata):
            return super().composition_payload_metadata(metadata).replace_fields(
                source_voxel_spacing=spacing
            )

    data = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    payloads = tuple(
        ImagePayloadMetadata(source_path=f"/synthetic/site_{index}.tif").payload_with(
            plane, None
        )
        for index, plane in enumerate(data)
    )
    aligned = CalibratedAlignedImageStack(payloads)
    contract = CallableContract.from_callable(rescale_intensity)
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        aligned,
        {},
        execution_mode=contract.runtime_image_execution_mode,
    )
    np.testing.assert_allclose(result.data, data / 23.0)
    metadata = result.metadata
    assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert metadata.source_voxel_spacing == spacing
    assert {
        identity.path
        for identity in metadata.source_provenance.represented_source_identities
    } == {"/synthetic/site_0.tif", "/synthetic/site_1.tif"}


def test_ragged_aligned_images_fail_before_dense_callable():
    aligned = AlignedImageStack((np.zeros((2, 3)), np.zeros((3, 3))))
    with pytest.raises(ValueError, match="one exact shape"):
        RuntimeSliceProjection.full_stack_value(aligned)


def test_full_stack_preserves_nonimage_identity_domains_and_dense_images():
    rows = MeasurementSparseColumnarRows.from_rows(
        ({"object_label": 1, "value": 2.5},),
        fields=(FieldSpec("object_label", int), FieldSpec("value", float)),
    )
    table = MeasurementTable(
        name="Measurements",
        rows=rows,
        subject=MeasurementSubject(MeasurementScope.OBJECT, name="Objects"),
    )
    labels = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=np.zeros((2, 3), dtype=np.int32)),
    )
    graph = SpatialGraph(
        name="graph",
        nodes=(SpatialGraphNode(1, (2.0, 3.0)),),
        edges=(),
        coordinate_spacing=SourceVoxelSpacing((1.0, 1.0)),
    )
    array = np.ones((2, 3), dtype=np.float32)
    image = ImagePayloadMetadata(source_path="/synthetic/source.tif").payload_with(
        array, array > 0
    )
    aligned_tokens = RuntimeSliceAlignedValues((labels, table))
    opaque = object()
    kwargs = {
        "rows": rows,
        "table": table,
        "labels": labels,
        "graph": graph,
        "tokens": aligned_tokens,
        "array": array,
        "image": image,
        "opaque": opaque,
    }
    materialized = RuntimeSliceProjection.full_stack_kwargs(kwargs)
    assert materialized is not kwargs
    for name, value in kwargs.items():
        assert materialized[name] is value


@pytest.mark.parametrize("processing_contract", tuple(ProcessingContract))
def test_full_stack_raw_callable_keeps_opaque_nonimage_kwargs(processing_contract):
    opaque = object()
    image = np.ones((2, 3, 4), dtype=np.float32)
    calls = []

    def consume(image, *, options):
        calls.append(options)
        assert options is opaque
        return image

    contract = CallableContract(
        func=consume,
        function_name="consume",
        module_name="OpaqueFullStackProbe",
        metadata=CallableMetadata(processing_contract=processing_contract),
    )
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        consume,
        image,
        {"options": opaque},
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )
    assert calls == [opaque]
    assert ImagePayload.of(result).data is image


@pytest.mark.parametrize("reverse", (False, True))
def test_independent_composition_capabilities_cooperate_in_both_mro_orders(reverse):
    calls = []

    class PixelCapability:
        def compose_unmasked(self, payloads, **kwargs):
            calls.append("pixels")
            return super().compose_unmasked(payloads, **kwargs) + 1

    class MaskCapability:
        def compose_mask(self, composed, metadata):
            calls.append("mask")
            mask = super().compose_mask(composed, metadata)
            if mask is None:
                mask = np.ones_like(composed, dtype=bool)
            mask[:, 0, 0] = False
            return mask

    bases = (
        (MaskCapability, PixelCapability)
        if reverse
        else (PixelCapability, MaskCapability)
    )
    probe_type = type("IndependentCompositionProbe", (*bases, AlignedImageStack), {})
    probe = probe_type((np.zeros((2, 3)), np.ones((2, 3))))
    assert isinstance(probe, ImagePayloadStackComposition)
    dense = RuntimeSliceProjection.full_stack_value(probe)
    assert calls == ["pixels", "mask"]
    np.testing.assert_array_equal(
        dense.data, np.stack((np.ones((2, 3)), np.full((2, 3), 2)))
    )
    expected_mask = np.ones((2, 2, 3), dtype=bool)
    expected_mask[:, 0, 0] = False
    np.testing.assert_array_equal(dense.mask, expected_mask)
