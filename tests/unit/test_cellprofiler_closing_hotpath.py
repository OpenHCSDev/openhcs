from __future__ import annotations

from collections.abc import Callable

import numpy as np
import pytest
from skimage.morphology import closing as skimage_closing
from skimage.morphology import dilation as skimage_dilation
from skimage.morphology import disk
from skimage.morphology import erosion as skimage_erosion
from skimage.morphology import opening as skimage_opening

from openhcs.processing.backends.cellprofiler._backend import (
    CellProfilerBackendProvider,
)
from openhcs.processing.backends.cellprofiler.morphology import (
    NumpyMorphologyBackendStrategy,
    closing,
    dilate_image,
    erode_image,
    opening,
)
from openhcs.processing.backends.cellprofiler.structuring_elements import (
    StructuringElement,
)


def _raw_function(function: Callable[..., np.ndarray]) -> Callable[..., np.ndarray]:
    while hasattr(function, "__wrapped__"):
        function = function.__wrapped__
    return function


def test_closing_collapses_runtime_slice_stack_into_one_native_operation(
    monkeypatch,
) -> None:
    rng = np.random.default_rng(20260719)
    image = rng.random((12, 48, 52), dtype=np.float32)
    footprint = disk(7)
    expected = np.stack(
        tuple(skimage_closing(plane, footprint) for plane in image),
        axis=0,
    )
    observed_shapes: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    native_closing = NumpyMorphologyBackendStrategy.grayscale_closing

    def record_native_call(
        self,
        pixels: np.ndarray,
        structuring_element: np.ndarray,
    ) -> np.ndarray:
        observed_shapes.append((pixels.shape, structuring_element.shape))
        return native_closing(self, pixels, structuring_element)

    monkeypatch.setattr(
        NumpyMorphologyBackendStrategy,
        "grayscale_closing",
        record_native_call,
    )

    observed = _raw_function(closing)(
        image,
        structuring_element=StructuringElement.DISK,
        size=7,
    )

    np.testing.assert_array_equal(observed, expected)
    assert observed.dtype == image.dtype
    assert observed_shapes == [((12, 48, 52), (1, 15, 15))]


@pytest.mark.parametrize(
    "provider",
    (CellProfilerBackendProvider.NUMBA, CellProfilerBackendProvider.OPENCV),
)
def test_closing_stack_preserves_explicit_provider_semantics(
    provider: CellProfilerBackendProvider,
) -> None:
    rng = np.random.default_rng(13)
    image = rng.random((3, 19, 21), dtype=np.float32)
    footprint = disk(3)
    expected = np.stack(
        tuple(skimage_closing(plane, footprint) for plane in image),
        axis=0,
    )

    observed = _raw_function(closing)(
        image,
        structuring_element=StructuringElement.DISK,
        size=3,
        morphology_backend_provider=provider,
    )

    np.testing.assert_array_equal(observed, expected)


@pytest.mark.parametrize(
    ("function", "reference"),
    (
        (closing, skimage_closing),
        (opening, skimage_opening),
        (dilate_image, skimage_dilation),
        (erode_image, skimage_erosion),
    ),
)
def test_image_morphology_stack_matches_planewise_reference(
    function: Callable[..., np.ndarray],
    reference: Callable[[np.ndarray, np.ndarray], np.ndarray],
) -> None:
    rng = np.random.default_rng(91)
    image = rng.random((4, 23, 25), dtype=np.float32)
    footprint = disk(3)
    expected = np.stack(
        tuple(reference(plane, footprint) for plane in image),
        axis=0,
    )

    observed = _raw_function(function)(
        image,
        structuring_element=StructuringElement.DISK,
        size=3,
    )

    np.testing.assert_array_equal(observed, expected)


@pytest.mark.parametrize("dtype", (np.float32, np.float64))
def test_native_span_morphology_preserves_asymmetric_and_even_footprints(dtype):
    image = np.random.default_rng(41).uniform(-3, 3, (2, 4, 7)).astype(dtype)
    image.setflags(write=False)
    source = image.copy()
    backend = NumpyMorphologyBackendStrategy()
    footprints = (
        disk(7)[None],
        np.array([[0, 1], [1, 1]], dtype=bool)[None],
        np.array([[1, 0, 1, 1], [0, 1, 0, 1]], dtype=bool)[None],
    )
    for footprint in footprints:
        for operation, reference in (
            (backend.grayscale_closing, skimage_closing),
            (backend.grayscale_opening, skimage_opening),
        ):
            observed = operation(image, footprint)
            expected = reference(image, footprint)
            np.testing.assert_array_equal(observed, expected)
            assert observed.dtype == dtype
            assert not np.shares_memory(observed, image)
    np.testing.assert_array_equal(image, source)


def test_native_span_morphology_keeps_native_special_value_and_volume_laws():
    backend = NumpyMorphologyBackendStrategy()
    cases = (
        (np.array([[1, np.nan], [2, 3]], dtype=np.float32), disk(1)),
        (np.array([[1, -0.0], [0.0, -2]], dtype=np.float32), disk(1)),
        (np.array([[1, 4], [2, 3]], dtype=np.int32), disk(1)),
        (np.arange(27, dtype=np.float32).reshape(3, 3, 3), np.ones((3, 3, 3), dtype=bool)),
    )
    for image, footprint in cases:
        for operation, reference in (
            (backend.grayscale_closing, skimage_closing),
            (backend.grayscale_opening, skimage_opening),
        ):
            observed = operation(image, footprint)
            expected = reference(image, footprint)
            assert observed.dtype == expected.dtype == image.dtype
            # Equality must include the native sign-bit and NaN representation.
            assert observed.tobytes() == expected.tobytes()
