import importlib
from dataclasses import fields, replace
from inspect import signature, unwrap

import numpy as np
import pytest
from scipy import ndimage as ndi
from skimage.draw import disk, ellipse
from skimage.measure import regionprops

from openhcs.core.artifacts import (
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_output_matching import RuntimeReturnedOutputMatcher
from openhcs.processing.backends.analysis.count_cells_simple import (
    Foreground,
    MetaXpressW2Settings,
    MetaXpressWavelengthSettings,
    SimpleCellSegmentationConfig,
    StainedArea,
    ThresholdMethod,
    count_cells_simple,
    count_cells_simple_dual_channel,
    inspect_metaxpress_round_objects,
    round_object_segmentation_stages,
    segment_metaxpress_round_objects,
)

count_cells_simple_module = importlib.import_module(
    "openhcs.processing.backends.analysis.count_cells_simple"
)


def _count_cells_simple_impl():
    return unwrap(count_cells_simple)


def _count_cells_simple_dual_channel_impl():
    return unwrap(count_cells_simple_dual_channel)


def _settings(**overrides):
    return replace(SimpleCellSegmentationConfig(), **overrides)


def _rows(rows):
    return rows.row_mappings()


def test_dual_channel_signature_exposes_only_metaxpress_scoring_controls():
    parameters = signature(_count_cells_simple_dual_channel_impl()).parameters
    contract = CallableContract.from_callable(count_cells_simple_dual_channel)
    runtime_artifact_parameter_names = contract.artifact_inputs.names()
    exposed_names = [
        name for name in parameters if name not in runtime_artifact_parameter_names
    ]

    assert exposed_names == [
        "image",
        "w1",
        "w2",
        "minimum_stained_area",
    ]
    assert runtime_artifact_parameter_names == ("pixel_size",)
    assert parameters["pixel_size"].annotation._ui_hidden is True
    assert [field.name for field in fields(MetaXpressWavelengthSettings)] == [
        "channel_index",
        "approx_min_width",
        "approx_max_width",
        "intensity_above_local_background",
    ]
    assert [field.name for field in fields(MetaXpressW2Settings)] == [
        "channel_index",
        "approx_min_width",
        "approx_max_width",
        "intensity_above_local_background",
        "stained_area",
    ]
    assert [choice.value for choice in StainedArea] == [
        "nucleus",
        "nucleus and cytoplasm",
    ]
    assert contract.artifact_outputs.names() == (
        "dual_channel_counts",
        "dual_channel_cells",
        "w1_nuclei",
        "w2_stain",
    )
    summary_spec, cell_spec, w1_spec, w2_spec = contract.artifact_outputs
    assert summary_spec.artifact_type is MeasurementsArtifactType
    assert cell_spec.artifact_type is MeasurementsArtifactType
    assert cell_spec.relations[0].measurement_subject().name == w1_spec.name
    assert w1_spec.artifact_type is ObjectLabelsArtifactType
    assert w2_spec.artifact_type is ObjectLabelsArtifactType


def test_count_cells_simple_area_filter_fast_path_does_not_use_regionprops(monkeypatch):
    image = np.zeros((1, 32, 32), dtype=float)
    rr, cc = disk((10, 10), 4, shape=image.shape[1:])
    image[0, rr, cc] = 1.0
    rr, cc = disk((22, 22), 4, shape=image.shape[1:])
    image[0, rr, cc] = 1.0
    image[0, 0, 0] = 1.0

    def fail_regionprops(_labels):
        raise AssertionError("regionprops should not be needed without shape filtering")

    monkeypatch.setattr(count_cells_simple_module, "regionprops", fail_regionprops)

    _, results, masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=20,
            max_size=200,
            max_eccentricity=1.0,
        ),
    )

    assert _rows(results) == ({"slice_index": 0, "cell_count": 2},)
    assert set(np.unique(masks[0])) == {0, 1, 2}


def test_count_cells_simple_filters_eccentricity_after_size_filter():
    image = np.zeros((1, 64, 64), dtype=float)
    rr, cc = disk((24, 24), 5, shape=image.shape[1:])
    image[0, rr, cc] = 1.0
    image[0, 42:45, 10:40] = 1.0

    _, unfiltered_results, unfiltered_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=20,
            max_size=200,
            max_eccentricity=1.0,
        ),
    )
    _, filtered_results, filtered_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=20,
            max_size=200,
            max_eccentricity=0.9,
        ),
    )

    assert _rows(unfiltered_results) == ({"slice_index": 0, "cell_count": 2},)
    assert set(np.unique(unfiltered_masks[0])) == {0, 1, 2}
    assert _rows(filtered_results) == ({"slice_index": 0, "cell_count": 1},)
    assert set(np.unique(filtered_masks[0])) == {0, 1}


def test_count_cells_simple_watersheds_large_objects_before_size_filter():
    image = np.zeros((1, 64, 64), dtype=float)
    rr, cc = disk((32, 26), 8, shape=image.shape[1:])
    image[0, rr, cc] = 1.0
    rr, cc = disk((32, 38), 8, shape=image.shape[1:])
    image[0, rr, cc] = 1.0

    _, unsplit_results, unsplit_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=50,
            max_size=220,
            watershed_large_objects=False,
        ),
    )
    _, split_results, split_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=50,
            max_size=220,
            watershed_large_objects=True,
            watershed_min_distance=5,
        ),
    )
    _, capped_results, capped_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=50,
            max_size=220,
            watershed_large_objects=True,
            watershed_max_size=300,
            watershed_min_distance=5,
        ),
    )

    assert _rows(unsplit_results) == ({"slice_index": 0, "cell_count": 0},)
    assert set(np.unique(unsplit_masks[0])) == {0}
    assert _rows(split_results) == ({"slice_index": 0, "cell_count": 2},)
    assert set(np.unique(split_masks[0])) == {0, 1, 2}
    assert _rows(capped_results) == ({"slice_index": 0, "cell_count": 0},)
    assert set(np.unique(capped_masks[0])) == {0}


def test_count_cells_simple_watershed_min_size_separates_split_trigger_from_filter():
    image = np.zeros((1, 80, 80), dtype=float)
    rr, cc = disk((32, 32), 12, shape=image.shape[1:])
    image[0, rr, cc] = 1.0
    rr, cc = disk((48, 44), 12, shape=image.shape[1:])
    image[0, rr, cc] = 1.0

    _, unsplit_results, unsplit_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=20,
            max_size=900,
            watershed_large_objects=True,
            watershed_min_distance=1,
            watershed_footprint_size=5,
        ),
    )
    _, split_results, split_masks = _count_cells_simple_impl()(
        image,
        segmentation_settings=_settings(
            threshold_method=ThresholdMethod.MANUAL,
            threshold=0.5,
            min_size=20,
            max_size=900,
            watershed_large_objects=True,
            watershed_min_size=100,
            watershed_min_distance=1,
            watershed_footprint_size=5,
        ),
    )

    assert _rows(unsplit_results) == ({"slice_index": 0, "cell_count": 1},)
    assert set(np.unique(unsplit_masks[0])) == {0, 1}
    assert _rows(split_results) == ({"slice_index": 0, "cell_count": 2},)
    assert set(np.unique(split_masks[0])) == {0, 1, 2}


def _metaxpress_settings(**overrides):
    return replace(MetaXpressWavelengthSettings(), **overrides)


def _metaxpress_w2_settings(**overrides):
    return replace(MetaXpressW2Settings(), **overrides)


def test_dual_channel_scores_w2_positive_cells_by_minimum_stained_area():
    image = np.full((2, 64, 64), 100.0)
    for center in ((20, 20), (45, 45)):
        rr, cc = disk(center, 5, shape=image.shape[1:])
        image[0, rr, cc] = 1000.0

    rr, cc = disk((20, 20), 4, shape=image.shape[1:])
    image[1, rr, cc] = 700.0

    (
        output,
        results,
        cell_results,
        w1_labels,
        w2_labels,
    ) = _count_cells_simple_dual_channel_impl()(
        image,
        w1=_metaxpress_settings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=14.0,
            intensity_above_local_background=300.0,
        ),
        w2=_metaxpress_w2_settings(
            channel_index=1,
            approx_min_width=4.0,
            approx_max_width=14.0,
            intensity_above_local_background=200.0,
            stained_area=StainedArea.NUCLEUS,
        ),
        minimum_stained_area=20.0,
        pixel_size=1.0,
    )

    assert output is image
    assert _rows(results) == (
        {
            "w1_channel_index": 0,
            "w2_channel_index": 1,
            "total_cell_count": 2,
            "w2_positive_cell_count": 1,
            "w2_negative_cell_count": 1,
            "w2_positive_percent": 50.0,
            "w2_stained_area": "nucleus",
            "minimum_stained_area": 20.0,
            "all_w2_mean_stained_area": 22.5,
            "positive_w2_mean_stained_area": 45.0,
        },
    )
    assert _rows(cell_results) == (
        {
            "object_label": 1,
            "w2_positive": True,
            "w2_stained_area_um2": 45.0,
        },
        {
            "object_label": 2,
            "w2_positive": False,
            "w2_stained_area_um2": 0.0,
        },
    )
    assert [set(np.unique(labels)) for labels in (w1_labels, w2_labels)] == [
        {0, 1, 2},
        {0, 1},
    ]
    assert np.count_nonzero(w1_labels[1]) == 0
    assert np.count_nonzero(w2_labels[0]) == 0

    _, stricter_results, _, _, _ = _count_cells_simple_dual_channel_impl()(
        image,
        w1=_metaxpress_settings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=14.0,
            intensity_above_local_background=300.0,
        ),
        w2=_metaxpress_w2_settings(
            channel_index=1,
            approx_min_width=4.0,
            approx_max_width=14.0,
            intensity_above_local_background=200.0,
            stained_area=StainedArea.NUCLEUS,
        ),
        minimum_stained_area=46.0,
        pixel_size=1.0,
    )
    assert _rows(stricter_results)[0]["w2_positive_cell_count"] == 0


def test_w2_nucleus_and_cytoplasm_scores_stain_outside_the_nucleus():
    image = np.full((2, 64, 64), 100.0)
    rr, cc = disk((32, 32), 4, shape=image.shape[1:])
    image[0, rr, cc] = 1000.0

    outer_rr, outer_cc = disk((32, 32), 8, shape=image.shape[1:])
    image[1, outer_rr, outer_cc] = 700.0
    image[1, rr, cc] = 100.0

    w1 = _metaxpress_settings(
        channel_index=0,
        approx_min_width=5.0,
        approx_max_width=10.0,
        intensity_above_local_background=300.0,
    )
    w2 = _metaxpress_w2_settings(
        channel_index=1,
        approx_min_width=6.0,
        approx_max_width=24.0,
        intensity_above_local_background=200.0,
        stained_area=StainedArea.NUCLEUS,
    )

    _, nucleus_results, _, _, _ = _count_cells_simple_dual_channel_impl()(
        image,
        w1=w1,
        w2=w2,
        minimum_stained_area=20.0,
        pixel_size=1.0,
    )
    _, whole_cell_results, _, _, w2_labels = _count_cells_simple_dual_channel_impl()(
        image,
        w1=w1,
        w2=replace(w2, stained_area=StainedArea.NUCLEUS_AND_CYTOPLASM),
        minimum_stained_area=20.0,
        pixel_size=1.0,
    )

    assert _rows(nucleus_results)[0]["w2_positive_cell_count"] == 0
    assert _rows(whole_cell_results)[0]["w2_positive_cell_count"] == 1
    assert _rows(whole_cell_results)[0]["w2_stained_area"] == ("nucleus and cytoplasm")
    assert set(np.unique(w2_labels[1])) == {0, 1}


@pytest.mark.parametrize("rotation_degrees", range(0, 180, 15))
def test_width_based_watershed_preserves_one_elongated_nucleus(rotation_degrees):
    image = np.zeros((96, 96), dtype=np.float64)
    rr, cc = ellipse(
        48, 48, 15, 19, rotation=np.deg2rad(rotation_degrees), shape=image.shape
    )
    image[rr, cc] = 1000.0
    settings = MetaXpressWavelengthSettings(
        approx_min_width=5.0,
        approx_max_width=32.0,
        intensity_above_local_background=300.0,
    )

    labels = segment_metaxpress_round_objects(image, settings, 1.0)

    # Its area exceeds the circular split trigger, but its short-axis width
    # fits the declared range and its medial ridge belongs to one nucleus.
    assert len(rr) > np.pi * (settings.approx_max_width / 2.0) ** 2
    assert labels.max() == 1
    assert labels[48, 48] == 1


def test_width_based_watershed_splits_touching_nuclei_below_max_width_area():
    image = np.zeros((96, 96), dtype=np.float64)
    centers = ((48, 43), (48, 53))
    for center in centers:
        rows, columns = disk(center, 6, shape=image.shape)
        image[rows, columns] = 1000.0
        rows, columns = disk(center, 2, shape=image.shape)
        image[rows, columns] = 1800.0
    settings = MetaXpressWavelengthSettings(
        approx_min_width=5.0,
        approx_max_width=30.0,
        intensity_above_local_background=300.0,
    )

    labels = segment_metaxpress_round_objects(image, settings, 1.0)

    foreground_area = np.count_nonzero(image)
    maximum_object_area = np.pi * (settings.approx_max_width / 2.0) ** 2
    assert foreground_area < maximum_object_area
    assert labels.max() == 2
    assert labels[centers[0]] != labels[centers[1]]


def test_width_based_watershed_preserves_unequal_touching_nucleus_peaks():
    image = np.zeros((96, 96), dtype=np.float64)
    centers_and_radii = (((48, 44), 6), ((48, 52), 5))
    for center, radius in centers_and_radii:
        rows, columns = disk(center, radius, shape=image.shape)
        image[rows, columns] = 1000.0
        rows, columns = disk(center, 2, shape=image.shape)
        image[rows, columns] = 1800.0
    settings = MetaXpressWavelengthSettings(
        approx_min_width=5.0,
        approx_max_width=30.0,
        intensity_above_local_background=300.0,
    )

    labels = segment_metaxpress_round_objects(image, settings, 1.3556)

    centers = tuple(center for center, _ in centers_and_radii)
    assert labels.max() == 2
    assert labels[centers[0]] != labels[centers[1]]


def test_round_object_declumping_uses_distinct_intensity_centers_in_one_silhouette():
    rows, columns = np.mgrid[:128, :128]
    image = np.full((128, 128), 100.0)
    foreground = np.zeros(image.shape, dtype=bool)
    foreground_rows, foreground_columns = ellipse(64, 64, 10, 18, shape=image.shape)
    foreground[foreground_rows, foreground_columns] = True
    image[foreground] = 350.0
    centers = ((64, 58), (64, 70))
    for center, amplitude in zip(centers, (1000.0, 800.0), strict=True):
        image += amplitude * np.exp(
            -((rows - center[0]) ** 2 + (columns - center[1]) ** 2) / 8.0
        )
    settings = MetaXpressWavelengthSettings(
        approx_min_width=5.0,
        approx_max_width=50.0,
        intensity_above_local_background=200.0,
    )

    labels = segment_metaxpress_round_objects(image, settings, 1.3556)

    assert ndi.label(foreground)[1] == 1
    assert labels.max() == 2
    assert labels[centers[0]] != labels[centers[1]]


def test_intensity_marker_refuses_shape_only_split_without_two_centers():
    component = np.zeros((96, 96), dtype=bool)
    for center in ((48, 43), (48, 53)):
        rows, columns = disk(center, 8, shape=component.shape)
        component[rows, columns] = True
    labeled, _ = ndi.label(component)
    rows, columns = np.mgrid[:96, :96]
    one_center_surface = 1000.0 * np.exp(
        -((rows - 48) ** 2 + (columns - 43) ** 2) / 32.0
    )

    shape_only = count_cells_simple_module._watershed_large_objects(
        labeled,
        split_size=100,
        watershed_max_size=None,
        min_distance=3,
        footprint_size=3,
        peak_prominence=1.0,
    )
    intensity_supported = count_cells_simple_module._watershed_large_objects(
        labeled,
        split_size=100,
        watershed_max_size=None,
        min_distance=3,
        footprint_size=3,
        peak_prominence=1.0,
        marker_image=one_center_surface,
        marker_smoothing_sigma=1.0,
        marker_peak_prominence=50.0,
    )

    assert shape_only.max() > 1
    assert intensity_supported.max() == 1


def test_label_indexed_shape_statistics_match_regionprops():
    labels = np.zeros((128, 144), dtype=np.int32)
    for label, center, radii, rotation in (
        (1, (0, 0), (9, 7), 0.0),
        (2, (45, 50), (15, 6), np.deg2rad(30)),
        (3, (95, 110), (8, 18), np.deg2rad(75)),
    ):
        rows, columns = ellipse(
            *center,
            *radii,
            rotation=rotation,
            shape=labels.shape,
        )
        labels[rows, columns] = label

    statistics = count_cells_simple_module._shape_statistics_by_label(labels)

    for region in regionprops(labels):
        assert statistics.counts[region.label] == region.area
        assert statistics.centroid_rows_px[region.label] == pytest.approx(
            region.centroid[0]
        )
        assert statistics.centroid_columns_px[region.label] == pytest.approx(
            region.centroid[1]
        )
        assert statistics.major_axis_lengths_px[region.label] == pytest.approx(
            region.axis_major_length
        )
        assert statistics.minor_axis_lengths_px[region.label] == pytest.approx(
            region.axis_minor_length
        )


def test_round_object_width_filter_does_not_iterate_region_objects(monkeypatch):
    image = np.zeros((96, 96), dtype=np.float64)
    rows, columns = disk((48, 48), 9, shape=image.shape)
    image[rows, columns] = 1000.0

    def reject_region_iteration(*args, **kwargs):
        raise AssertionError("round-object filtering must use indexed moments")

    monkeypatch.setattr(
        count_cells_simple_module, "regionprops", reject_region_iteration
    )

    labels = segment_metaxpress_round_objects(
        image,
        MetaXpressWavelengthSettings(
            approx_min_width=5.0,
            approx_max_width=24.0,
            intensity_above_local_background=300.0,
        ),
        1.0,
    )

    assert labels.max() == 1
    assert labels[48, 48] == 1


def test_round_object_diagnostics_preserve_kernel_output_and_rejection_identity():
    image = np.zeros((2, 96, 96), dtype=np.float32)
    for center, radius in (((25, 25), 7), ((70, 70), 1)):
        rr, cc = disk(center, radius, shape=image.shape[1:])
        image[0, rr, cc] = 1000.0
    image[1] = 123.0
    original = image.copy()
    settings = MetaXpressWavelengthSettings(
        channel_index=0,
        approx_min_width=5.0,
        approx_max_width=30.0,
        intensity_above_local_background=200.0,
    )
    stages = round_object_segmentation_stages(image[0], settings, 1.0)
    returned = unwrap(inspect_metaxpress_round_objects)(
        image,
        settings=settings,
        pixel_size=1.0,
    )
    raw, measurements, prefilter, accepted, weak_core, adjacent_satellites = returned
    contract = CallableContract.from_callable(inspect_metaxpress_round_objects)
    matched = RuntimeReturnedOutputMatcher(contract, returned).resolve()
    assert (
        matched[count_cells_simple_module.ROUND_OBJECT_WIDTHS_OUTPUT.ref()]
        is measurements
    )
    assert (
        matched[count_cells_simple_module.ROUND_OBJECT_PREFILTER_OUTPUT.ref()]
        is prefilter
    )
    assert (
        matched[count_cells_simple_module.ROUND_OBJECT_ACCEPTED_OUTPUT.ref()]
        is accepted
    )
    assert (
        matched[count_cells_simple_module.ROUND_OBJECT_WEAK_CORE_OUTPUT.ref()]
        is weak_core
    )
    assert (
        matched[
            count_cells_simple_module.ROUND_OBJECT_ADJACENT_SATELLITE_OUTPUT.ref()
        ]
        is adjacent_satellites
    )
    assert raw is image
    np.testing.assert_array_equal(image, original)
    np.testing.assert_array_equal(prefilter[0], stages.prefilter_labels)
    np.testing.assert_array_equal(
        accepted[0],
        segment_metaxpress_round_objects(
            image[0],
            settings,
            1.0,
        ),
    )
    assert not np.any(prefilter[1])
    assert not np.any(accepted[1])
    assert not np.any(weak_core[1])
    assert not np.any(adjacent_satellites[1])
    rows = _rows(measurements)
    assert len(rows) == 2
    for row in rows:
        support = prefilter[0] == row["object_label"]
        assert row["area_pixels"] == np.count_nonzero(support)
        assert np.all(accepted[0][support] == row["accepted_label"])
        assert row["source_component_output_count"] == 1
        assert row["split_from_source_component"] is False
        expected_centroid = regionprops(support.astype(np.uint8))[0].centroid
        assert row["centroid_row_px"] == pytest.approx(expected_centroid[0])
        assert row["centroid_column_px"] == pytest.approx(expected_centroid[1])
        assert row["peak_intensity_above_local_background"] >= row[
            "mean_intensity_above_local_background"
        ]
        assert row["core_support_threshold"] == 400.0
        assert row["weak_core_candidate"] == (
            bool(stages.width_keep_mask[row["object_label"]])
            and row["peak_intensity_above_local_background"] < 400.0
        )
        assert row["rejected_as_adjacent_satellite"] is False
        width_accepted = 5.0 <= row["minor_axis_um"] <= 30.0
        assert (row["accepted_label"] > 0) == width_accepted
    assert {row["accepted_label"] for row in rows} == {0, 1}


def test_round_object_diagnostics_report_watershed_source_component_lineage():
    image = np.zeros((1, 96, 96), dtype=np.float32)
    centers = ((48, 43), (48, 53))
    for center in centers:
        rr, cc = disk(center, 6, shape=image.shape[1:])
        image[0, rr, cc] = 1000.0
        rr, cc = disk(center, 2, shape=image.shape[1:])
        image[0, rr, cc] = 1800.0
    settings = MetaXpressWavelengthSettings(
        channel_index=0,
        approx_min_width=5.0,
        approx_max_width=30.0,
        intensity_above_local_background=300.0,
    )

    _, measurements, prefilter, accepted, _, _ = unwrap(
        inspect_metaxpress_round_objects
    )(
        image,
        settings=settings,
        pixel_size=1.0,
    )

    rows = _rows(measurements)
    assert len(rows) == 2
    assert np.count_nonzero(np.unique(prefilter)) == 2
    assert accepted.max() == 2
    assert {row["source_component_label"] for row in rows} == {1}
    assert {row["source_component_output_count"] for row in rows} == {2}
    assert {row["split_from_source_component"] for row in rows} == {True}


def test_adjacent_satellite_filter_is_conjunctive_and_keeps_isolated_faint_objects():
    labels = np.zeros((48, 64), dtype=np.int32)
    labels[20:23, 20:25] = 1
    labels[18:30, 26:38] = 2
    labels[35:38, 4:9] = 3
    labels[8:11, 50:55] = 4
    counts = np.bincount(labels.ravel())
    peaks = np.array([0.0, 280.0, 900.0, 280.0, 900.0])
    width_keep = np.array([False, True, True, True, True])

    rejected = count_cells_simple_module._adjacent_satellite_mask(
        labels,
        counts,
        peaks,
        width_keep,
        maximum_candidate_area=22,
        minimum_core_response=400.0,
        maximum_gap_px=2,
    )

    assert rejected.tolist() == [False, True, False, False, False]


def test_width_settings_derive_watershed_for_touching_w1_nuclei():
    image = np.full((2, 64, 64), 100.0)
    for center in ((32, 27), (32, 37)):
        rr, cc = disk(center, 6, shape=image.shape[1:])
        image[0, rr, cc] = 1000.0
        rr, cc = disk(center, 2, shape=image.shape[1:])
        image[0, rr, cc] = 1800.0

    _, results, _, w1_labels, _ = _count_cells_simple_dual_channel_impl()(
        image,
        w1=_metaxpress_settings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=12.0,
            intensity_above_local_background=300.0,
        ),
        w2=_metaxpress_w2_settings(
            channel_index=1,
            approx_min_width=4.0,
            approx_max_width=12.0,
            intensity_above_local_background=2000.0,
        ),
        minimum_stained_area=10.0,
        pixel_size=1.0,
    )

    assert _rows(results)[0]["total_cell_count"] == 2
    assert _rows(results)[0]["w2_positive_cell_count"] == 0
    assert set(np.unique(w1_labels[0])) == {0, 1, 2}
