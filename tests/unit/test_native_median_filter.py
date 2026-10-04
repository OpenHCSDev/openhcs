"""Exact native median admission, buffer isolation and READY preparation controls."""

import runpy
from pathlib import Path

import numpy as np
import pytest
from scipy.ndimage import median_filter

from openhcs.processing.backends.cellprofiler import _median_native
from openhcs.processing.backends.cellprofiler.median_filter import (
    NumpyMedianFilterBackendStrategy,
    ScipyBoundaryMode,
)


@pytest.mark.parametrize("shape", [(1, 1, 1), (1, 4, 9), (4, 1, 17), (5, 6, 9)])
def test_native_median_all_declared_footprints_and_partial_vectors(shape):
    backend = NumpyMedianFilterBackendStrategy()
    windows = _median_native.supported_windows()
    if not windows:
        pytest.skip("This build/CPU uses the portable existing median fallback.")
    # A read-only, noncontiguous source retains ordinary negative/duplicate values.
    storage = (np.arange(np.prod(shape) * 2).reshape(*shape, 2) % 23 - 11).astype(np.float32)
    image = storage[..., 0]
    image.setflags(write=False)
    before = image.copy()
    for window in windows:
        actual = backend.selection_network_filter(image, window, ScipyBoundaryMode.CONSTANT)
        np.testing.assert_array_equal(actual, median_filter(image, size=window, mode="constant", cval=0))
        assert actual.dtype == image.dtype
        assert not np.shares_memory(actual, image)
        np.testing.assert_array_equal(image, before)


def test_native_median_preserves_original_fallback_ordering(monkeypatch):
    backend = NumpyMedianFilterBackendStrategy()
    data = np.linspace(-1, 1, 4 * 5 * 9, dtype=np.float32).reshape(4, 5, 9)
    cases = [(data.astype(np.float64), ScipyBoundaryMode.CONSTANT),
             (data.astype(np.int32), ScipyBoundaryMode.CONSTANT),
             (data.copy(), ScipyBoundaryMode.REFLECT)]
    for value in (np.nan, np.inf, -0.0):
        image = data.copy()
        image[0, 0, 0] = value
        cases.append((image, ScipyBoundaryMode.CONSTANT))
    expected = []
    with monkeypatch.context() as portable:
        portable.setattr(_median_native, "supported_windows", lambda: ())
        expected = [backend.filter(image, window_size=4, mode=mode) for image, mode in cases]
    def reject_native(*args):
        raise AssertionError("Unsupported scalar ordering reached a native network.")
    monkeypatch.setattr(_median_native, "filter", reject_native)
    for (image, mode), oracle in zip(cases, expected):
        actual = backend.filter(image, window_size=4, mode=mode)
        # Preserve the original bit pattern, including signed zero and NaN payload.
        np.testing.assert_array_equal(np.ascontiguousarray(actual).view(np.uint8),
                                      np.ascontiguousarray(oracle).view(np.uint8))
    monkeypatch.setattr(_median_native, "supported_windows", lambda: ())
    np.testing.assert_array_equal(backend.filter(data, window_size=5, mode=ScipyBoundaryMode.CONSTANT),
                                  median_filter(data, size=5, mode="constant", cval=0))


def test_native_median_rejects_invalid_or_overlapping_buffers():
    windows = _median_native.supported_windows()
    if not windows:
        pytest.skip("This build/CPU uses the portable existing median fallback.")
    window = windows[0]
    radius = window // 2
    source = np.pad(np.ones((1, 1, 1), dtype=np.float32),
                    ((radius, radius), (radius, radius), (radius, radius + 7)))
    output = np.empty((1, 1, 8), dtype=np.float32)
    with pytest.raises(ValueError, match="float32"):
        _median_native.filter(source.astype(np.float64), output, window)
    with pytest.raises(ValueError, match="geometry"):
        _median_native.filter(source, np.empty((1, 2, 8), dtype=np.float32), window)
    borrowed = source.ravel()[:8].reshape(1, 1, 8)
    with pytest.raises(ValueError, match="independent"):
        _median_native.filter(source, borrowed, window)
    output.setflags(write=False)
    with pytest.raises((BufferError, ValueError)):
        _median_native.filter(source, output, window)


def test_native_median_prepares_every_compiled_footprint(monkeypatch):
    calls = []
    native_filter = _median_native.filter
    def observed(source, output, window):
        calls.append(window)
        return native_filter(source, output, window)
    monkeypatch.setattr(_median_native, "filter", observed)
    backend = NumpyMedianFilterBackendStrategy()
    backend.prepare_backend()
    assert tuple(calls) == _median_native.supported_windows()


def test_native_median_build_geometry_is_derived_and_source_deterministic(tmp_path):
    generator_path = Path(__file__).resolve().parents[2] / "scripts/build_median_network.py"
    generator = runpy.run_path(str(generator_path))
    declared = generator["supported_windows"]()
    cap = generator["MAX_WINDOW_VOLUME"]
    assert declared == tuple(size for size in range(3, cap + 1, 2) if size**3 <= cap)
    left, right = tmp_path / "left.h", tmp_path / "right.h"
    generator["build_median_network_header"](left)
    generator["build_median_network_header"](right)
    assert left.read_bytes() == right.read_bytes()
    if _median_native.supported_windows():
        assert _median_native.supported_windows() == declared
