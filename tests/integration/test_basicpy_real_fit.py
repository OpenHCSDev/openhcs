"""Real, bounded BaSiC fit/range/field checks; compiled MCP acceptance is separate."""

import numpy as np
import pytest

pytest.importorskip("basicpy", reason="requires reviewed paired BaSiCPy source")

from openhcs.processing.backends.enhance.basic_processor_jax import (
    basic_flatfield_correction_jax,
)


def shaded_observations(*, stationary_biology=False, volume=False):
    """Synthetic acquisition only: no biological data, reference or downloaded image."""
    size = 32
    count = 24
    yy, xx = np.mgrid[-1 : 1 : complex(size), -1 : 1 : complex(size)]
    flatfield = 1.2 - 0.3 * (yy**2 + xx**2) + 0.1 * xx
    flatfield /= flatfield.mean()
    rng = np.random.default_rng(213)
    observations = []
    for index in range(count):
        background = 3000 + 50 * index
        if stationary_biology:
            # A stationary, background-scaled biological pattern is fundamentally
            # confounded with multiplicative shading, not a convergence failure.
            biology = background * np.exp(-((xx - 0.2) ** 2 + (yy + 0.1) ** 2) / 0.09)
        else:
            cx, cy = rng.uniform(-0.8, 0.8, size=2)
            biology = 5000 * np.exp(-((xx - cx) ** 2 + (yy - cy) ** 2) / 0.008)
        frame = (background + biology) * flatfield
        observations.append(np.rint(frame).astype(np.uint16))
    observations = np.stack(observations)
    if volume:
        observations = np.stack((observations, observations), axis=1)
        flatfield = np.stack((flatfield, flatfield))
    return observations, flatfield


def run_fit(observations):
    return basic_flatfield_correction_jax(
        observations,
        max_iterations=100,
        working_size=None,
        get_darkfield=False,
    )


@pytest.mark.parametrize("volume", [False, True])
def test_real_fit_keeps_measurement_range_and_returns_same_fit_fields(volume):
    observations, truth = shaded_observations(volume=volume)
    corrected, flatfield, darkfield = run_fit(observations)
    corrected = np.asarray(corrected)
    flatfield_data = np.asarray(flatfield)
    darkfield_data = np.asarray(darkfield)
    assert np.issubdtype(corrected.dtype, np.floating)
    assert corrected.shape == observations.shape
    assert flatfield.shape == darkfield.shape == observations.shape[1:]
    assert (
        flatfield.observation_count
        == darkfield.observation_count
        == observations.shape[0]
    )
    assert np.isfinite(corrected).all()
    np.testing.assert_allclose(darkfield_data, 0, atol=1e-6)
    np.testing.assert_allclose(
        corrected,
        (observations.astype(np.float32) - darkfield_data) / flatfield_data,
        rtol=1e-5,
        atol=1e-3,
    )
    assert np.sqrt(np.mean((flatfield_data - truth) ** 2)) < 0.15
    assert np.any(corrected != np.floor(corrected))


def test_stationary_biology_negative_control_exposes_flatfield_leakage():
    moving, truth = shaded_observations()
    stationary, _ = shaded_observations(stationary_biology=True)
    _, moving_field, _ = run_fit(moving)
    _, stationary_field, _ = run_fit(stationary)
    moving_error = np.sqrt(np.mean((np.asarray(moving_field) - truth) ** 2))
    stationary_error = np.sqrt(np.mean((np.asarray(stationary_field) - truth) ** 2))
    # A successful fit is not evidence that stationary signal is shading-free.
    assert stationary_error > moving_error + 0.02
