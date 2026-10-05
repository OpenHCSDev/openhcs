from __future__ import annotations

import numpy as np
import pytest
import skimage.measure
import skimage.segmentation
import skimage.transform

from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.processing.backends.cellprofiler.watershed import (
    WatershedMethod,
    WatershedSegmentationSurface,
    watershed_cellprofiler4,
    watershed_resize_labels,
)


def test_constant_surface_preserves_signed_and_wide_marker_domains(monkeypatch) -> None:
    image = np.full((4, 7, 9), -2.0, dtype=np.float32)
    mask = np.ones(image.shape, dtype=bool)
    mask[:, 3, 4] = False
    native_watershed = skimage.segmentation.watershed
    native_calls = []

    def observe_native(*args, **kwargs):
        native_calls.append(args)
        return native_watershed(*args, **kwargs)

    monkeypatch.setattr(skimage.segmentation, "watershed", observe_native)
    for dtype, label, native_required in (
        (np.int8, -7, False),
        (np.int32, -7, False),
        (np.int64, -7, False),
        (np.int64, -(1 << 40), True),
        (np.uint64, np.iinfo(np.uint64).max, True),
    ):
        markers = np.zeros(image.shape, dtype=dtype)
        markers.ravel()[::7] = 3
        markers[1, 2, 3] = label
        original = markers.copy()
        expected = native_watershed(
            image, markers, mask=mask, connectivity=3
        )
        previous_native_calls = len(native_calls)
        actual = WatershedSegmentationSurface(image, None, None, markers).labels(
            mask, connectivity=3
        )
        np.testing.assert_array_equal(actual, expected)
        np.testing.assert_array_equal(markers, original)
        assert actual.dtype == markers.dtype
        assert not np.shares_memory(actual, markers)
        assert len(native_calls) - previous_native_calls == int(native_required)


def test_surface_preserves_native_variable_nonfinite_and_line_semantics() -> None:
    image = np.ones((7, 9), dtype=np.float32)
    markers = np.zeros(image.shape, dtype=np.int32)
    markers[1, 1] = 7
    markers[-2, -2] = 2
    mask = np.ones(image.shape, dtype=bool)
    mask[3, 4] = False
    for mode in ("variable", "nonfinite", "compact", "lines"):
        surface = image.copy()
        compactness = 0.25 if mode == "compact" else 0.0
        lines = mode == "lines"
        if mode == "variable":
            surface[2:5, 2:5] = 2.0
        if mode == "nonfinite":
            surface[2, 2] = np.nan
        expected = skimage.segmentation.watershed(
            surface, markers, mask=mask, compactness=compactness,
            watershed_line=lines,
        )
        actual = WatershedSegmentationSurface(surface, None, None, markers).labels(
            mask, compactness=compactness, watershed_line=lines,
        )
        np.testing.assert_array_equal(actual, expected)


def test_marker_watershed_nonempty_mask_matches_connected_component_reference() -> None:
    image = np.zeros((5, 17, 19), dtype=bool)
    image[:, 2:15, 2:17] = True
    mask = image.copy()
    mask[:, 7:10, 8:11] = False
    markers = np.zeros(image.shape, dtype=np.int32)
    markers[1, 5, 5] = 7
    markers[3, 12, 14] = 2

    initial_labels = skimage.segmentation.watershed(
        image=image,
        markers=markers,
        mask=mask,
        connectivity=1,
        compactness=0.0,
        watershed_line=False,
    )
    expected_labels = skimage.measure.label(initial_labels).astype(
        np.int32,
        copy=False,
    )

    _, stats, label_value = watershed_cellprofiler4(
        image,
        topology_inputs=(markers, mask),
        watershed_method=WatershedMethod.MARKERS,
        use_advanced_settings=False,
    )

    labels = object_label_dense_array(label_value)
    assert np.count_nonzero(markers) == 2
    assert np.count_nonzero(mask) > 0
    np.testing.assert_array_equal(labels, expected_labels)
    (stats_row,) = stats.row_mappings()
    object_count = int(expected_labels.max(initial=0))
    assert stats_row["object_count"] == object_count
    assert stats_row["mean_area"] == pytest.approx(
        np.count_nonzero(expected_labels) / object_count,
    )


def test_integer_label_resize_reuses_exact_resize_result(monkeypatch) -> None:
    resized = np.arange(24, dtype=np.uint16).reshape(2, 3, 4)

    def fake_resize(
        labels,
        output_shape,
        *,
        mode,
        order,
        preserve_range,
    ):
        assert labels.shape == (1, 2, 2)
        assert output_shape == resized.shape
        assert mode == "edge"
        assert order == 0
        assert preserve_range is True
        return resized

    monkeypatch.setattr(skimage.transform, "resize", fake_resize)

    result = watershed_resize_labels(
        np.ones((1, 2, 2), dtype=np.uint16),
        resized.shape,
    )

    assert result is resized


def test_float_label_resize_rounds_in_place_before_uint16_cast(monkeypatch) -> None:
    resized = np.array([[[0.49, 0.5], [1.5, 2.51]]], dtype=np.float32)
    expected = np.rint(resized).astype(np.uint16)

    monkeypatch.setattr(
        skimage.transform,
        "resize",
        lambda *args, **kwargs: resized,
    )

    result = watershed_resize_labels(
        np.ones((1, 1, 1), dtype=np.float32),
        resized.shape,
    )

    np.testing.assert_array_equal(result, expected)
    np.testing.assert_array_equal(resized, np.rint(resized))
