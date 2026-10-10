"""Geometry declarations preserve the payload their raw implementations consume."""

from dataclasses import replace
from typing import get_type_hints

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    VolumeSourceSpatialDomain,
)
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.processing.backends.cellprofiler.image_geometry import (
    mask_image,
    resize,
    resize_volumetric,
)


def _prepared_contract(func):
    contract = CallableContract.from_callable(func).with_prepared_signature()
    return replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )


@pytest.mark.parametrize("func", (resize, resize_volumetric))
def test_prepared_resize_preserves_typed_primary_and_bare_array(func):
    pixels = np.arange(24, dtype=np.float32).reshape(4, 6)
    source = ImagePayloadMetadata(
        source_path="/images/input.tif", source_image_names=("Original",),
    ).payload_with(pixels, pixels % 2 == 0)
    contract = _prepared_contract(func)

    assert contract.raw_main_flow_call_argument(source) is source
    assert contract.raw_main_flow_call_argument(pixels) is pixels


@pytest.mark.parametrize("axis", (None, RuntimePlaneAxis.RUNTIME_SLICE))
@pytest.mark.parametrize("z_factor", (1.0, 2.0))
@pytest.mark.parametrize(
    "domain_type", (SourceSpatialDomain, VolumeSourceSpatialDomain)
)
def test_prepared_full_stack_resize_preserves_existing_metadata_and_mask(
    axis,
    z_factor,
    domain_type,
):
    planes = tuple(
        ImagePayloadMetadata(
            source_path=f"/images/z{index}.tif",
            source_image_names=("Original",),
            source_component_metadata={"z_index": index, "timepoint": 1, "well": "W001"},
            source_spatial_domain=SourceSpatialDomain(
                origin_yx=(2, 3), source_shape_yx=(8, 10),
            ),
        ).payload_with(np.full((4, 6), index, dtype=np.float32), None)
        for index in (3, 1, 2)
    )
    metadata = ImagePayloadMetadata.compose(planes).replace_fields(plane_axis=axis)
    if domain_type is VolumeSourceSpatialDomain:
        metadata = metadata.replace_fields(
            source_spatial_domain=VolumeSourceSpatialDomain(
                source_depth=3
            ).admit_source_cohort(
                metadata.source_spatial_domain,
                depth=3,
            )
        )
    pixels = np.stack(tuple(plane.data for plane in planes))
    mask = np.ones(pixels.shape, dtype=bool)
    mask[:, 0, 0] = False
    source = metadata.payload_with(pixels, mask)
    contract = _prepared_contract(resize_volumetric)
    canonical = contract.resolve_canonical_raw_callable()
    kwargs = dict(
        resizing_factor_x=0.5, resizing_factor_y=0.5, resizing_factor_z=z_factor,
    )
    expected = canonical(source, **kwargs)

    result = CellProfilerFunctionContractExecutor().execute(
        contract, canonical, source, kwargs,
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )

    np.testing.assert_array_equal(
        result.data, expected.data
    )
    np.testing.assert_array_equal(
        result.mask, expected.mask
    )
    assert result.metadata == expected.metadata
    assert result.metadata.plane_axis is axis
    assert result.metadata.source_image_paths == metadata.source_image_paths
    assert result.metadata.source_provenance == metadata.source_provenance
    assert result.metadata.source_spatial_domain.source_shape_yx == (2, 3)
    assert isinstance(result.metadata.source_spatial_domain, domain_type)
    if domain_type is VolumeSourceSpatialDomain:
        assert result.metadata.source_spatial_domain.source_depth == 3
        assert result.data.shape[0] == int(3 * z_factor)
    assert source.metadata is metadata
    np.testing.assert_array_equal(source.data, pixels)
    np.testing.assert_array_equal(source.mask, mask)


@pytest.mark.parametrize("func", (resize, resize_volumetric))
def test_prepared_resize_bare_pixels_preserve_canonical_return_contract(func):
    pixels = np.arange(24, dtype=np.float32).reshape(4, 6)
    contract = _prepared_contract(func)
    canonical = contract.resolve_canonical_raw_callable()
    kwargs = dict(resizing_factor_x=0.5, resizing_factor_y=0.5)
    if func is resize_volumetric:
        kwargs["resizing_factor_z"] = 1.0
    expected = canonical(pixels, **kwargs)

    result = CellProfilerFunctionContractExecutor().execute(
        contract, canonical, pixels, kwargs,
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )

    assert isinstance(result, RuntimeArrayData)
    assert type(result) is type(expected)
    np.testing.assert_array_equal(result.data, expected.data)
    np.testing.assert_array_equal(result.mask, expected.mask)
    assert result.metadata == expected.metadata


def test_mask_image_declares_its_actual_nominal_return_family():
    contract = _prepared_contract(mask_image)
    canonical = contract.resolve_canonical_raw_callable()
    assert get_type_hints(canonical)["return"] == RuntimeArrayData
    pixels = np.arange(12, dtype=np.float32).reshape(3, 4)
    source = ImagePayloadMetadata(source_path="/images/input.tif").payload_with(pixels)
    result = canonical(source, pixels > 3)
    assert isinstance(result, RuntimeArrayData)
    assert result.metadata.source_image_paths == ("/images/input.tif",)
