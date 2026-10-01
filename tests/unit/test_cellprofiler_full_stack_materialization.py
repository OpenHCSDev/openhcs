"""Dense full-stack ABI must consume aligned source/artifact values correctly."""

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    AlignedImageStack,
    ImageOutputBundle,
    ImagePayloadExecutionMode,
    ImagePayloadStackComposition,
    compose_aligned_image_payload,
)
from openhcs.core.callable_contract import CallableContract, CallableMetadata
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.processing.backends.cellprofiler.intensity import rescale_intensity
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


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
    np.testing.assert_allclose(image_payload_data(result), expected)


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
        np.testing.assert_array_equal(image_payload_data(image), np.stack(planes))
        np.testing.assert_array_equal(image_payload_data(reference), np.stack(planes))
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
    np.testing.assert_array_equal(image_payload_data(result), np.stack(planes))
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
    metadata = image_payload_metadata(dense)
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
        image_payload_mask(dense),
        np.stack(
            [
                np.broadcast_to(image_payload_mask(plane), (2, 3, 4))
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
            image_payload_data(projected), image_payload_data(composed.slices[index])
        )
        expected = {f"/synthetic/A01_s{index + 1}_w{channel}.tif" for channel in (1, 2)}
        assert {
            identity.path
            for identity in image_payload_metadata(
                projected
            ).source_provenance.represented_source_identities
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
    assert image_payload_metadata(dense).plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    assert image_payload_metadata(
        dense
    ).source_provenance.represented_source_image_names == ("red", "green")
    np.testing.assert_array_equal(image_payload_data(dense), np.stack(planes))
    assert bundle.slices == planes


def test_ragged_aligned_images_fail_before_dense_callable():
    aligned = AlignedImageStack((np.zeros((2, 3)), np.zeros((3, 3))))
    with pytest.raises(ValueError, match="one exact shape"):
        RuntimeSliceProjection.full_stack_value(aligned)


@pytest.mark.parametrize("reverse", (False, True))
def test_independent_composition_capabilities_cooperate_in_both_mro_orders(reverse):
    calls = []

    class PixelCapability:
        def compose_unmasked(self, payloads):
            calls.append("pixels")
            return super().compose_unmasked(payloads) + 1

    class MaskCapability:
        def compose_mask(self, composed, metadata):
            calls.append("mask")
            return super().compose_mask(composed, metadata)

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
        image_payload_data(dense), np.stack((np.ones((2, 3)), np.full((2, 3), 2)))
    )
