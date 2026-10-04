"""Exact finite-plane contracts for the declared FAST speckle operation."""

import numpy as np
import pytest
from scipy import ndimage
from skimage import morphology

from openhcs.core.callable_contract import CallableContract
from openhcs.core.config import DtypeConfig
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.processing.backends.cellprofiler.feature_enhancement import (
    SpeckleAccuracy,
    enhance_or_suppress_features,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


@pytest.mark.parametrize("shape", [(1, 9), (7, 5), (33, 41)])
@pytest.mark.parametrize("dtype", [np.float32, np.float64])
@pytest.mark.parametrize("radius", [3, 4, 4.5, 5.5, 12.5])
def test_declared_fast_speckles_matches_original_disk_opening(shape, dtype, radius):
    image = np.random.default_rng(616).uniform(-2, 3, size=shape).astype(dtype)
    image[0, 0] = 7
    image[-1, -1] = -5
    footprint = morphology.disk(max(1, round(radius)))
    expected = image - ndimage.maximum_filter(
        ndimage.minimum_filter(image, footprint=footprint), footprint=footprint,
    )
    actual = enhance_or_suppress_features(
        image, radius=radius, speckle_accuracy=SpeckleAccuracy.FAST,
        dtype_config=DtypeConfig(),
    )
    np.testing.assert_array_equal(image_payload_data(actual), expected.astype(np.float32))
    assert image_payload_data(actual).dtype == np.float32


@pytest.mark.parametrize("accuracy", [SpeckleAccuracy.FAST, SpeckleAccuracy.SLOW])
@pytest.mark.parametrize("masked", ["partial", "all", "none"])
def test_speckle_mask_background_and_metadata_remain_owned(accuracy, masked):
    image = np.random.default_rng(616).uniform(0, 2, (17, 23)).astype(np.float32)
    mask = np.ones(image.shape, dtype=bool)
    if masked == "partial":
        mask[3:8, 1:6] = False
    elif masked == "all":
        mask[:] = False
    original = ImagePayloadMetadata(intensity_scale=65535).payload_with(image, mask)
    masked_image = np.where(mask, image, 0)
    footprint = morphology.disk(5)
    expected = masked_image - ndimage.maximum_filter(
        ndimage.minimum_filter(masked_image, footprint=footprint), footprint=footprint,
    )
    expected[~mask] = image[~mask]
    actual = enhance_or_suppress_features(
        original, radius=5, speckle_accuracy=accuracy, dtype_config=DtypeConfig(),
    )
    np.testing.assert_array_equal(image_payload_data(actual), expected)
    np.testing.assert_array_equal(image_payload_mask(actual), mask)
    assert image_payload_metadata(actual).intensity_scale == 65535
    assert image_payload_metadata(actual).unit_interval_intensity is None


def test_fast_speckles_registered_callable_keeps_independent_planes():
    image = np.random.default_rng(616).uniform(0, 1, (2, 17, 23)).astype(np.float32)
    expected = np.stack([
        plane - ndimage.maximum_filter(
            ndimage.minimum_filter(plane, footprint=morphology.disk(5)),
            footprint=morphology.disk(5),
        ) for plane in image
    ])
    actual = enhance_or_suppress_features(image, radius=5, dtype_config=DtypeConfig())
    np.testing.assert_array_equal(image_payload_data(actual), expected)
    assert CallableContract.from_callable(enhance_or_suppress_features).processing_contract is ProcessingContract.PURE_2D
