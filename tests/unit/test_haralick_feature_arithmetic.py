"""Default feature fusion preserves CP formulas, directions and error behavior."""

import numpy as np
import pytest

from openhcs.processing.backends.cellprofiler.texture import (
    NativeNumpyHaralickTextureBackendStrategy,
    NumbaNumpyHaralickTextureBackendStrategy,
)


@pytest.mark.parametrize("ignore_zeros", (False, True))
@pytest.mark.parametrize("gray_levels", (2, 16, 256))
def test_fused_haralick_matches_reference_across_distributions(
    ignore_zeros, gray_levels
):
    native = NativeNumpyHaralickTextureBackendStrategy()
    fused = NumbaNumpyHaralickTextureBackendStrategy()
    rng = np.random.default_rng(7123)
    images = (
        np.full((9, 11), gray_levels - 1, dtype=np.uint8),
        (1 + np.indices((9, 11)).sum(axis=0) % 2 * (gray_levels - 2)).astype(np.uint8),
        rng.integers(0, gray_levels, size=(9, 11), dtype=np.uint8),
        rng.integers(0, gray_levels, size=(18, 22), dtype=np.uint8)[::2, ::2],
    )
    for image in images:
        for scale in (1, 2, 3):
            expected = native.haralick_features(
                image, scale=scale, ignore_zeros=ignore_zeros
            )
            actual = fused.haralick_features(
                image, scale=scale, ignore_zeros=ignore_zeros
            )
            assert actual.shape == (4, 13)
            assert actual.dtype == np.float64
            assert np.isfinite(actual).all()
            # This is the existing strict CP comparison policy, explicitly
            # authorized for fused floating-point arithmetic by the user.
            np.testing.assert_allclose(actual, expected, rtol=1e-6, atol=1e-6)


@pytest.mark.parametrize(
    "backend",
    (
        NativeNumpyHaralickTextureBackendStrategy,
        NumbaNumpyHaralickTextureBackendStrategy,
    ),
)
def test_haralick_ignored_empty_matrix_keeps_reference_failure(backend):
    with pytest.raises(ValueError, match="the input is empty"):
        backend().haralick_features(
            np.zeros((5, 6), dtype=np.uint8), scale=1, ignore_zeros=True
        )


def test_numba_haralick_small_planes_keep_zero_features():
    backend = NumbaNumpyHaralickTextureBackendStrategy()
    for shape in ((1, 5), (5, 1), (0, 5)):
        np.testing.assert_array_equal(
            backend.haralick_features(
                np.zeros(shape, dtype=np.uint8), scale=1, ignore_zeros=True
            ),
            np.zeros((4, 13)),
        )


def test_existing_backend_preparation_warms_fused_feature_kernel():
    from openhcs.processing.backends.cellprofiler.texture import (
        _haralick_features_numba,
    )

    NumbaNumpyHaralickTextureBackendStrategy().prepare_backend()
    assert _haralick_features_numba.signatures
