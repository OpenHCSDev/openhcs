"""Shared weighted arithmetic preserves each production consumer's recipe."""

import inspect

import numpy as np
import pytest

from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.processing.backends.cellprofiler.color import combine_color_to_gray
from openhcs.processing.backends.processors.numpy_processor import (
    NumpyWeightedProjectionKernelPreparation,
    _weighted_projection_numba,
    create_composite,
)


@pytest.mark.parametrize("dtype", [np.float32, np.float64, np.float16, np.int16])
@pytest.mark.parametrize("layout", ["C", "F", "strided", "singleton", "empty"])
def test_composite_retains_float32_products_and_original_dtype(dtype, layout):
    stack = np.arange(9 * 4 * 6, dtype=dtype).reshape(9, 4, 6)
    if layout == "F":
        stack = np.asfortranarray(stack)
    elif layout == "strided":
        stack = stack[:, ::2, ::-2]
    elif layout == "singleton":
        stack = stack[:, :1, :1]
    elif layout == "empty":
        stack = stack[:, :0]
    weights = [(-1.0) ** index * (index + 1) for index in range(9)]
    normalized = np.array([w / sum(weights) for w in weights], np.float32)
    expected = np.sum(
        stack.astype(np.float32) * normalized[:, None, None], axis=0
    ).astype(stack.dtype)
    actual = inspect.unwrap(create_composite)(stack, weights)
    np.testing.assert_array_equal(actual, expected)
    assert actual.dtype == stack.dtype


@pytest.mark.parametrize("shape", [(2, 4, 6, 9), (1, 1, 1, 9), (2, 0, 6, 9)])
@pytest.mark.parametrize("strided", [False, True])
def test_color_retains_selected_order_duplicates_and_negative_indices(shape, strided):
    pixels = np.arange(np.prod(shape), dtype=np.float32).reshape(shape) / np.float32(7)
    if strided:
        pixels = pixels[:, :, ::-1]
    channels = (8, -1, 0, 3, 3, 1, 7, 2, 6)
    contributions = (1.0, -2.0, 3.0, 4.0, 5.0, -6.0, 7.0, 8.0, 9.0)
    weights = np.asarray(contributions, float) / sum(contributions)
    if pixels.shape[:-1] == (1, 1, 1):
        expected = np.sum(pixels[..., np.array(channels)] * weights, axis=-1)
    else:
        expected = np.zeros(pixels.shape[:-1], dtype=np.float64)
        for channel, weight in zip(channels, weights, strict=True):
            expected += pixels[..., channel].astype(np.float64) * weight
    payload = ImagePayloadMetadata(
        source_channel_axis=3, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(pixels)
    actual = combine_color_to_gray(payload, channels, contributions)
    np.testing.assert_array_equal(actual, expected)


def test_nonfinite_products_are_not_reassociated():
    pixels = np.array([[[[np.inf, -np.inf, np.nan], [1.0, 2.0, 3.0]]]], np.float32)
    payload = ImagePayloadMetadata(
        source_channel_axis=3, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(pixels)
    with np.errstate(invalid="ignore"):
        actual = combine_color_to_gray(payload, (0, 1, 2), (0.0, 1.0, 1.0))
    np.testing.assert_array_equal(actual, np.array([[[np.nan, 2.5]]]))


def test_empty_spatial_domain_still_validates_channel_indices():
    payload = ImagePayloadMetadata(
        source_channel_axis=3, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(np.empty((1, 0, 2, 3), np.float32))
    with pytest.raises(IndexError):
        combine_color_to_gray(payload, (3,), (1.0,))


@pytest.mark.parametrize("channels", [(), (0, 1, 2)])
def test_zero_sum_outputs_retain_positive_zero(channels):
    payload = ImagePayloadMetadata(
        source_channel_axis=3, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(np.full((2, 2, 2, 3), -0.0, np.float32))
    actual = combine_color_to_gray(payload, channels, (1.0,) * len(channels))
    np.testing.assert_array_equal(actual, np.zeros((2, 2, 2), np.float64))
    assert not np.any(np.signbit(actual))


def test_registry_preparation_covers_accelerated_consumer_signatures():
    assert NumpyWeightedProjectionKernelPreparation in (
        NumpyWeightedProjectionKernelPreparation.__registry__.values()
    )
    NumpyWeightedProjectionKernelPreparation.prepare_registered_family()
    assert NumpyWeightedProjectionKernelPreparation in (
        AutoRegisterRegistryPreparation.cached_module_registry_families(
            combine_color_to_gray.__module__,
        )
    )
    before = tuple(_weighted_projection_numba.signatures)
    inspect.unwrap(create_composite)(np.ones((3, 4, 6), np.float64), [1, 2, 3])
    pixels = np.ones((2, 4, 6, 3), np.float32)[:, :, ::-1]
    payload = ImagePayloadMetadata(
        source_channel_axis=3, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(pixels)
    combine_color_to_gray(payload, (0, 1, 2), (1, 2, 3))
    pixels.flags.writeable = False
    readonly = combine_color_to_gray(payload, (0, 1, 2), (1, 2, 3))
    np.testing.assert_array_equal(readonly, np.ones((2, 4, 6)))
    degenerate = np.ones((1, 1, 6, 3), np.float64)
    degenerate_payload = ImagePayloadMetadata(
        source_channel_axis=3, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(degenerate)
    combine_color_to_gray(degenerate_payload, (0, 1, 2), (1, 2, 3))
    degenerate.flags.writeable = False
    combine_color_to_gray(degenerate_payload, (0, 1, 2), (1, 2, 3))
    assert before == tuple(_weighted_projection_numba.signatures)
