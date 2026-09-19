from __future__ import annotations

import builtins

import numpy as np

from openhcs.constants.constants import MemoryType
from openhcs.processing.backends.cellprofiler._backend import (
    CellProfilerBackendProvider,
)
from openhcs.processing.backends.cellprofiler.edge import (
    EdgeDirection,
    EdgeEnhancementRequest,
    EdgeEnhancementStrategy,
    EdgeMethod,
)
from openhcs.processing.backends.cellprofiler.illumination import (
    ConvexHullSmoothingBackendStrategy,
)
from openhcs.processing.backends.cellprofiler.image_quality import image_quality_backend
from openhcs.processing.backends.cellprofiler.morphology import (
    MorphologyBackendStrategy,
)
from openhcs.processing.backends.cellprofiler.outlines import (
    ObjectOutlineBackendStrategy,
)
from openhcs.processing.backends.cellprofiler.secondary import (
    secondary_propagation_backend,
)
from openhcs.processing.backends.cellprofiler.smoothing import (
    SmoothingBackendProviderPolicy,
    SmoothingBackendSelectionRequest,
    SmoothingMethod,
    SmoothingRequest,
    SmoothingStrategy,
    SmoothingStrategyKey,
    _cellprofiler_octagon,
)
from openhcs.processing.backends.cellprofiler.thresholding import threshold_primitives
from openhcs.processing.backends.cellprofiler.worm_geometry import (
    rebuild_worm_from_control_points_approx,
)
from openhcs.processing.backends.cellprofiler.zernike import shape_zernike_moments


def test_production_cellprofiler_backends_execute_without_centrosome(
    monkeypatch,
) -> None:
    original_import = builtins.__import__

    def reject_centrosome(name, *args, **kwargs):
        if name == "centrosome" or name.startswith("centrosome."):
            raise AssertionError(f"production attempted to import {name}")
        return original_import(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", reject_centrosome)
    provider = CellProfilerBackendProvider.CENTROSOME
    image = np.arange(81, dtype=np.float32).reshape(9, 9) / 80
    mask = np.ones(image.shape, dtype=bool)
    labels = np.zeros(image.shape, dtype=np.int32)
    labels[2:5, 2:5] = 1
    labels[5:8, 5:8] = 2

    morphology = MorphologyBackendStrategy.for_memory_type(
        MemoryType.NUMPY, backend_provider=provider
    )
    assert morphology.disk_footprint(2).ndim == 2
    assert threshold_primitives(backend_provider=provider).otsu_threshold(image) > 0
    assert (
        ObjectOutlineBackendStrategy.for_memory_type(
            MemoryType.NUMPY, backend_provider=provider
        )
        .outline(labels)
        .shape
        == labels.shape
    )
    assert np.isfinite(
        image_quality_backend(backend_provider=provider).haralick_h3(image, scale=1)
    )

    propagation = secondary_propagation_backend(
        backend_provider=CellProfilerBackendProvider.NATIVE
    ).propagate_result(image, labels, mask, 1.0)
    assert propagation.labels.shape == labels.shape

    convex_hull = ConvexHullSmoothingBackendStrategy.for_memory_type(
        MemoryType.NUMPY, backend_provider=provider
    ).smooth_background_plane(
        image,
        mask=mask,
        filter_size=3,
        morphology=morphology,
    )
    assert convex_hull.shape == image.shape

    edge_request = EdgeEnhancementRequest(
        image=image,
        mask=mask,
        backend_provider=CellProfilerBackendProvider.NATIVE,
        method=EdgeMethod.CANNY,
        direction=EdgeDirection.ALL,
        automatic_threshold=False,
        automatic_low_threshold=False,
        sigma=1.0,
        low_threshold=0.1,
        manual_threshold=0.2,
        threshold_adjustment_factor=1.0,
    )
    assert (
        EdgeEnhancementStrategy.for_request(edge_request).enhance(edge_request).shape
        == image.shape
    )

    selection = SmoothingBackendSelectionRequest(
        method=SmoothingMethod.CIRCULAR_AVERAGE_FILTER,
        auto_object_size=False,
        object_size=4.0,
        image_shape=image.shape,
    )
    smoothing_provider = SmoothingBackendProviderPolicy.resolve(
        selection.method,
        None,
        selection,
    )
    smoothing_request = SmoothingRequest(
        pixel_data=image,
        mask=mask,
        backend_provider=smoothing_provider,
        method=selection.method,
        object_size=selection.effective_object_size,
        sigma=selection.sigma,
        edge_intensity_difference=0.1,
        clip_polynomial=True,
    )
    assert (
        SmoothingStrategy.for_key(
            SmoothingStrategyKey(smoothing_provider, selection.method)
        )
        .smooth(smoothing_request)
        .shape
        == image.shape
    )

    indexes, moments = shape_zernike_moments(labels, np.array([1, 2]), max_order=4)
    assert moments.shape == (2, len(indexes))
    rows, columns = rebuild_worm_from_control_points_approx(
        np.array([[2.2, 2.2], [6.8, 6.8]]),
        np.array([1.0, 1.0]),
        image.shape,
    )
    assert rows.shape == columns.shape


def test_small_cellprofiler_median_radii_use_promoted_octagon() -> None:
    expected = np.ones((5, 5), dtype=bool)
    expected[0, 0] = expected[0, -1] = False
    expected[-1, 0] = expected[-1, -1] = False

    np.testing.assert_array_equal(_cellprofiler_octagon(1.0), expected)
    np.testing.assert_array_equal(_cellprofiler_octagon(1.5), expected)


def test_canny_accepts_all_automatic_and_manual_threshold_combinations() -> None:
    image = np.zeros((24, 24), dtype=np.float32)
    image[6:18, 6:18] = 1.0
    mask = np.ones(image.shape, dtype=bool)

    for automatic_threshold, automatic_low_threshold in (
        (False, False),
        (False, True),
        (True, False),
        (True, True),
    ):
        request = EdgeEnhancementRequest(
            image=image,
            mask=mask,
            backend_provider=CellProfilerBackendProvider.NATIVE,
            method=EdgeMethod.CANNY,
            direction=EdgeDirection.ALL,
            automatic_threshold=automatic_threshold,
            automatic_low_threshold=automatic_low_threshold,
            sigma=1.0,
            low_threshold=0.8,
            manual_threshold=0.0,
            threshold_adjustment_factor=1.0,
        )

        result = EdgeEnhancementStrategy.for_request(request).enhance(request)

        assert result.shape == image.shape
