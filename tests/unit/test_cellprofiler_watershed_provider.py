"""Bounded explicit-provider regression for the registered watershed owner."""

import builtins

import numpy as np
import pytest

from openhcs.constants.constants import MemoryType
from openhcs.processing.backends.cellprofiler._backend import CellProfilerBackendProvider
from openhcs.processing.backends.cellprofiler.watershed import (
    LegacyWatershedBackendStrategy,
    NumbaNumpyLegacyWatershedBackendStrategy,
    cellprofiler_legacy_watershed,
)


@pytest.mark.parametrize("marker_sign", [1, -1])
def test_explicit_centrosome_watershed_executes_absorbed_reference_without_dependency(
    monkeypatch, marker_sign
):
    original_import = builtins.__import__

    def reject_centrosome(name, *args, **kwargs):
        if name == "centrosome" or name.startswith("centrosome."):
            raise AssertionError(f"production attempted to import {name}")
        return original_import(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", reject_centrosome)
    provider = CellProfilerBackendProvider.CENTROSOME
    strategy = LegacyWatershedBackendStrategy.for_memory_type(
        MemoryType.NUMPY, backend_provider=provider
    )
    assert strategy.backend_provider is provider
    assert provider in LegacyWatershedBackendStrategy.available_backend_providers(
        MemoryType.NUMPY
    )
    image = np.array([[0.0, 1.0, 0.0]])
    markers = marker_sign * np.array([[1, 0, 2]], dtype=np.int32)
    labels = cellprofiler_legacy_watershed(
        image,
        markers=markers,
        mask=np.ones(image.shape, dtype=bool),
        connectivity=np.ones((1, 3), dtype=bool),
        backend_provider=provider,
    )
    np.testing.assert_array_equal(
        labels, marker_sign * np.array([[1, 1, 2]], dtype=np.int32)
    )
    assert labels.dtype == np.int32
    np.testing.assert_array_equal(markers, marker_sign * np.array([[1, 0, 2]]))


def test_explicit_centrosome_watershed_preserves_plane_volume_and_mask_contracts():
    provider = CellProfilerBackendProvider.CENTROSOME
    image = np.zeros((2, 3, 3))
    markers = np.zeros(image.shape, dtype=np.int32)
    markers[0, 1, 1] = 7
    mask = np.ones(image.shape, dtype=bool)
    mask[:, 0, 0] = False
    plane_labels = cellprofiler_legacy_watershed(
        image,
        markers=markers,
        mask=mask,
        connectivity=np.ones((3, 3), dtype=bool),
        backend_provider=provider,
    )
    volume_labels = cellprofiler_legacy_watershed(
        image,
        markers=markers,
        mask=mask,
        connectivity=1,
        backend_provider=provider,
    )
    np.testing.assert_array_equal(plane_labels[0], mask[0].astype(np.int32) * 7)
    assert not np.any(plane_labels[1])
    np.testing.assert_array_equal(volume_labels, mask.astype(np.int32) * 7)


def test_explicit_centrosome_registration_preserves_default_and_fail_closed_selection():
    assert type(LegacyWatershedBackendStrategy.for_memory_type(MemoryType.NUMPY)) is (
        NumbaNumpyLegacyWatershedBackendStrategy
    )
    with pytest.raises(NotImplementedError, match="provider 'cucim'"):
        LegacyWatershedBackendStrategy.for_memory_type(
            MemoryType.NUMPY, backend_provider=CellProfilerBackendProvider.CUCIM
        )
    with pytest.raises(NotImplementedError, match="memory type 'cupy'"):
        LegacyWatershedBackendStrategy.for_memory_type(
            MemoryType.CUPY, backend_provider=CellProfilerBackendProvider.CENTROSOME
        )
