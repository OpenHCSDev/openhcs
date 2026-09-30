"""Real, bounded BaSiC fit/range/field checks; compiled MCP acceptance is separate."""

import numpy as np
import pytest

pytest.importorskip("basicpy", reason="requires the openhcs-basicpy distribution")

from openhcs.processing.backends.enhance.basic_processor_jax import (
    basic_flatfield_correction_jax,
)
from tests.diagnostics.basicpy_observation_fixture import shaded_observations


def test_real_algorithm_uses_numpy_transport_and_is_cpu_catalog_eligible(monkeypatch):
    from openhcs.constants import MemoryType
    from openhcs.core.callable_contract import CallableContract
    from openhcs.processing.backends.lib_registry.openhcs_registry import (
        _catalog_memory_types,
        _module_declares_allowed_memory_type,
    )

    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    contract = CallableContract.from_callable(basic_flatfield_correction_jax)
    assert contract.declared_memory_types == frozenset({MemoryType.NUMPY})
    assert _catalog_memory_types(basic_flatfield_correction_jax) == frozenset(
        {MemoryType.NUMPY}
    )
    assert _module_declares_allowed_memory_type(
        basic_flatfield_correction_jax.__module__, frozenset({MemoryType.NUMPY.value})
    )


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
