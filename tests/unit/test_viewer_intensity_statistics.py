"""One statistics owner for real-valued images and Boolean masks."""

import numpy as np
import pytest

from openhcs.runtime.viewer_controls import ViewerIntensityStatistics


@pytest.mark.parametrize("values", (
    np.array([False, True, False, True]),
    np.array([0, 255, 0, 128], dtype=np.uint8).view(np.bool_),
    np.array([False, False, False]),
    np.array([True]),
    np.array([0, 3, 19, 22], dtype=np.uint16),
    np.array([-4, -1, 2, 9], dtype=np.int16),
    np.array([0.2, 0.4, 0.6, 0.9], dtype=np.float32),
    np.array([2**62, 2**62, 2**62, 2**62], dtype=np.int64),
))
def test_statistics_and_linear_percentiles_preserve_native_pixels(values):
    original = values.tobytes()
    requested = (0, 10, 25, 50, 75, 90, 100)
    reference = values.astype(np.float64)
    np.testing.assert_allclose(
        ViewerIntensityStatistics.percentiles(values, requested),
        np.percentile(reference, requested),
    )
    result = ViewerIntensityStatistics.from_pixels(values)
    assert result.count == values.size
    assert result.minimum == reference.min()
    assert result.maximum == reference.max()
    assert result.mean == reference.mean()
    assert result.median == np.median(reference)
    assert result.standard_deviation == reference.std()
    assert result.total == reference.sum()
    assert values.tobytes() == original


@pytest.mark.parametrize("requested", ((-1,), (101,), (float("nan"),)))
@pytest.mark.parametrize("dtype", (np.bool_, np.float64))
def test_percentiles_reject_invalid_requests_for_every_pixel_domain(dtype, requested):
    with pytest.raises(ValueError, match="percentiles"):
        ViewerIntensityStatistics.percentiles(np.array([0, 1], dtype=dtype), requested)


@pytest.mark.parametrize("values", (np.array([]), np.array([float("nan")]), np.array([float("inf")])))
def test_statistics_reject_unavailable_values(values):
    with pytest.raises(ValueError, match="nonempty and finite"):
        ViewerIntensityStatistics.from_pixels(values)
    with pytest.raises(ValueError, match="nonempty and finite"):
        ViewerIntensityStatistics.percentiles(values, (0, 100))


@pytest.mark.parametrize("values", (np.array(["1"]), np.array([1 + 2j])))
def test_statistics_reject_non_real_intensity_domains(values):
    with pytest.raises(TypeError, match="real numeric or Boolean"):
        ViewerIntensityStatistics.from_pixels(values)
    with pytest.raises(TypeError, match="real numeric or Boolean"):
        ViewerIntensityStatistics.percentiles(values, (0, 100))
