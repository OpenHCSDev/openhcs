from dataclasses import replace

import numpy as np
import pytest

import openhcs.processing.backends.cellprofiler.intensity_distribution as mid
from openhcs.core.config import DtypeConfig
from openhcs.core.measurement_feature_queries import (
    MeasurementFeatureQuery,
    MeasurementFeatureValueIndex,
)
from openhcs.core.pipeline.function_contracts import object_label_input_execution_mode_from_callable
from openhcs.core.measurement_row_materialization import columnar_row_values
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
)
from openhcs.core.runtime_object_label_domains import (
    ObjectLabelDomain,
    ObjectLabelDomainScope,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_object_labels import (
    ObjectLabelVariantData,
    ObjectLabelPayload,
)
from openhcs.core.runtime_tabular_values import MeasurementObjectRowIdentity
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_DIALECT,
)
from openhcs.processing.backends.cellprofiler._backend import (
    CellProfilerBackendProvider,
)
from openhcs.processing.backends.cellprofiler.intensity_distribution import (
    MeasureObjectIntensityDistributionModule,
    NativeNumpyRadialDistributionBackendStrategy,
    NumbaNumpyRadialDistributionBackendStrategy,
    ObjectIntensityDistributionMeasurementColumnarRows,
    RadialDistributionArrays,
    RadialDistributionMeasureRequest,
    intensity_distribution_object_domain,
    measure_object_intensity_distribution,
    radial_distribution_backend,
)
from openhcs.processing.backends.cellprofiler.secondary import (
    secondary_propagation_backend,
)
from openhcs.processing.backends.cellprofiler.zernike import (
    IntensityZernikeMeasurementFeature,
    IntensityZernikeMeasurementRowsRequest,
    ObjectIntensityZernikeMeasurementColumnarRows,
    ObjectZernikeDescriptorFeature,
    indexed_object_intensity_zernike_feature_name,
)
from openhcs.core.pipeline.function_contracts import (
    SliceAlignedLabels,
)

SOURCE_IMAGE_NAME = "BF_image"


def source_image(image: np.ndarray):
    return ImagePayloadMetadata(source_image_names=(SOURCE_IMAGE_NAME,)).attach_to(
        image
    )


def test_native_radial_distribution_excludes_pixels_without_valid_center():
    image = np.ones((2, 2), dtype=np.float32)
    labels = np.ones((2, 2), dtype=np.int32)

    radial_arrays = NativeNumpyRadialDistributionBackendStrategy().measure_from_centers(
        image,
        labels,
        np.zeros(labels.shape, dtype=np.float64),
        np.array([-1.0], dtype=np.float64),
        np.array([-1.0], dtype=np.float64),
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )

    assert not radial_arrays.object_has_pixels[0]
    assert np.all(np.isnan(radial_arrays.fraction_at_distance[0]))
    assert np.all(np.isnan(radial_arrays.mean_pixel_fraction[0]))
    assert np.all(radial_arrays.radial_cv_by_bin[:, 0] == 0.0)


def test_radial_center_fast_path_matches_propagation_with_obstacles_and_touching_labels():
    labels = np.zeros((36, 52), dtype=np.int32)
    labels[2:30, 2:28] = 1
    labels[8:25, 8:23] = 0
    labels[13:19, 8:18] = 1
    labels[5:29, 28:48] = 2
    backend = NativeNumpyRadialDistributionBackendStrategy()
    geometry = backend.label_geometry(labels)
    center_fields = geometry.center_fields
    unobstructed = mid._radial_unobstructed_center_fields(
        labels, center_fields.centers_i, center_fields.centers_j
    )
    assert np.array_equal(np.flatnonzero(unobstructed[2]), np.array([1]))

    seeds = np.zeros(labels.shape, dtype=np.int32)
    for label in (1, 2):
        row = int(center_fields.centers_i[label - 1])
        column = int(center_fields.centers_j[label - 1])
        seeds[row, column] = label
    colors = backend.shape_geometry_backend().color_labels(labels)
    reference_distances = np.zeros(labels.shape, dtype=np.float64)
    reference_labels = np.zeros(labels.shape, dtype=np.int32)
    for color in range(1, int(colors.max()) + 1):
        mask = colors == color
        result = backend.center_propagation_backend().propagate_zero_image_result(
            seeds, mask, 1
        )
        reference_distances[mask] = result.distances[mask]
        reference_labels[mask] = result.labels[mask]

    np.testing.assert_array_equal(center_fields.center_labels, reference_labels)
    np.testing.assert_allclose(
        center_fields.d_from_center, reference_distances, rtol=0, atol=1e-12
    )
    image = np.arange(labels.size, dtype=np.float32).reshape(labels.shape) + 1
    reference_geometry = mid.RadialLabelGeometry(
        d_to_edge=geometry.d_to_edge,
        center_fields=mid.RadialCenterDistanceFields(
            d_from_center=reference_distances,
            center_labels=reference_labels,
            centers_i=center_fields.centers_i,
            centers_j=center_fields.centers_j,
        ),
    )
    expected = backend.measure_self_centered_with_geometry(
        image,
        labels,
        reference_geometry,
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )
    actual = backend.measure_self_centered_with_geometry(
        image,
        labels,
        geometry,
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )
    for field_name in (
        "fraction_at_distance",
        "mean_pixel_fraction",
        "radial_cv_by_bin",
        "object_has_pixels",
    ):
        np.testing.assert_array_equal(
            getattr(actual, field_name), getattr(expected, field_name)
        )


def test_radial_distribution_uses_dense_extent_domain_for_missing_object_rows():
    image = np.ones((3, 3), dtype=np.float32)
    labels = np.array(
        [
            [1, 0, 3],
            [1, 0, 3],
            [0, 0, 0],
        ],
        dtype=np.int32,
    )

    label_payload = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=ObjectLabelDomain(declared_object_count=4),
    )

    _result, measurements = mid.measure_object_intensity_distribution(
        source_image(image),
        label_payload,
        bin_count=4,
        dtype_config=DtypeConfig(),
    )

    assert MeasurementRowAxisField.OBJECT_ROW_IDENTITY.value not in measurements.columns

    rows_by_object = {
        int(row["object_label"]): row for row in measurements.iter_row_mappings()
    }
    assert tuple(rows_by_object) == (1, 2, 3, 4)
    assert measurements.row_count() == 4
    assert len(measurements.fields) == 15
    fraction_feature = MeasureObjectIntensityDistributionModule.MeasurementFeature.FRACTION_AT_DISTANCE.source_qualified_name(
        source_image_name=SOURCE_IMAGE_NAME
    )
    mean_fraction_feature = MeasureObjectIntensityDistributionModule.MeasurementFeature.MEAN_FRACTION.source_qualified_name(
        source_image_name=SOURCE_IMAGE_NAME
    )
    radial_cv_feature = MeasureObjectIntensityDistributionModule.MeasurementFeature.RADIAL_CV.source_qualified_name(
        source_image_name=SOURCE_IMAGE_NAME
    )
    for bin_index in range(1, 5):
        fraction = f"{fraction_feature}_{bin_index}of4"
        mean = f"{mean_fraction_feature}_{bin_index}of4"
        cv = f"{radial_cv_feature}_{bin_index}of4"
        assert np.isfinite(rows_by_object[3][fraction])
        assert np.isnan(rows_by_object[2][fraction])
        assert np.isnan(rows_by_object[2][mean])
        assert rows_by_object[2][cv] == 0.0
        assert np.isnan(rows_by_object[4][cv])
        assert np.isfinite(rows_by_object[3][mean])
        assert np.isfinite(rows_by_object[3][cv])


def test_radial_cv_export_values_zero_undefined_coefficients():
    rows = ObjectIntensityDistributionMeasurementColumnarRows(
        radial_arrays=RadialDistributionArrays(
            fraction_at_distance=np.array([[1.0]], dtype=np.float64),
            mean_pixel_fraction=np.array([[1.0]], dtype=np.float64),
            radial_cv_by_bin=np.array([[np.nan]], dtype=np.float64),
            object_has_pixels=np.array([True]),
            n_bins=1,
        ),
        object_ids=(1,),
        source_image_name=SOURCE_IMAGE_NAME,
        bin_count=1,
    )

    np.testing.assert_array_equal(
        rows.column_values("RadialDistribution_RadialCV_BF_image_1of1"), [0.0]
    )


def test_radial_distribution_rows_own_native_feature_identity_and_axes():
    rows = ObjectIntensityDistributionMeasurementColumnarRows(
        radial_arrays=RadialDistributionArrays(
            fraction_at_distance=np.array([[0.25]], dtype=np.float64),
            mean_pixel_fraction=np.array([[1.0]], dtype=np.float64),
            radial_cv_by_bin=np.array([[0.0]], dtype=np.float64),
            object_has_pixels=np.array([True]),
            n_bins=1,
        ),
        object_ids=(1,),
        source_image_name=SOURCE_IMAGE_NAME,
        bin_count=4,
    )

    assert rows.object_row_identity is MeasurementObjectRowIdentity.LABEL_ID
    assert tuple(rows.columns) == (
        "object_label",
        "source_image_name",
        "RadialDistribution_FracAtD_BF_image_1of4",
        "RadialDistribution_MeanFrac_BF_image_1of4",
        "RadialDistribution_RadialCV_BF_image_1of4",
    )
    assert rows.row_count() == 1
    np.testing.assert_array_equal(
        rows.column_values("RadialDistribution_FracAtD_BF_image_1of4"), [0.25]
    )
    assert set(columnar_row_values(rows, "source_image_name")) == {SOURCE_IMAGE_NAME}


def test_intensity_distribution_module_owns_canonical_source_projection():
    assert (
        MeasureObjectIntensityDistributionModule.source_qualified_measurement_category()
        == "RadialDistribution"
    )
    radial_name = MeasureObjectIntensityDistributionModule.MeasurementFeature.FRACTION_AT_DISTANCE.source_qualified_name(
        source_image_name=SOURCE_IMAGE_NAME
    )
    zernike_name = MeasureObjectIntensityDistributionModule.source_qualified_feature_name(
        IntensityZernikeMeasurementFeature.ZERNIKE_MAGNITUDE.measurement_row_field_name,
        SOURCE_IMAGE_NAME,
    )

    assert radial_name == "RadialDistribution_FracAtD_BF_image"
    assert zernike_name == "RadialDistribution_ZernikeMagnitude_BF_image"
    assert (
        MeasureObjectIntensityDistributionModule.source_qualified_feature_name(
            radial_name,
            SOURCE_IMAGE_NAME,
        )
        == radial_name
    )
    assert (
        MeasureObjectIntensityDistributionModule.source_qualified_feature_name(
            zernike_name,
            SOURCE_IMAGE_NAME,
        )
        == zernike_name
    )


@pytest.mark.parametrize(
    "feature_name",
    (
        "RadialDistribution_FracAtD_BF_image_1of2",
        "RadialDistribution_FracAtD_BF_image_2of2",
        "RadialDistribution_MeanFrac_BF_image_2of2",
        "RadialDistribution_ZernikeMagnitude_BF_image_2_0",
        "RadialDistribution_ZernikePhase_BF_image_2_0",
    ),
)
@pytest.mark.parametrize("source_name", ("BF_image", "BF_image_2_0", "BF_image_1of2"))
def test_wide_intensity_distribution_features_remain_queryable(
    feature_name, source_name
):
    feature_name = feature_name.replace(SOURCE_IMAGE_NAME, source_name)
    image = np.arange(36, dtype=np.float32).reshape((6, 6)) + 1
    labels = np.zeros(image.shape, dtype=np.int32)
    labels[1:5, 1:5] = 1
    _, rows = measure_object_intensity_distribution(
        ImagePayloadMetadata(source_image_names=(source_name,)).attach_to(image),
        ObjectLabelPayload(
            variant_data=ObjectLabelVariantData(labels=labels),
            domain=ObjectLabelDomain(declared_object_count=1),
        ),
        bin_count=2,
        wants_zernikes=mid.ZernikeMode.MAGNITUDES_AND_PHASE,
        zernike_degree=2,
    )
    table = MeasurementTable(
        name="IntensityDistribution",
        rows=rows,
        source_image_name=source_name,
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
        measurement_feature_owner=MeasureObjectIntensityDistributionModule,
    )
    indexes = MeasurementFeatureValueIndex.from_columnar_table_by_object(
        table,
        MeasurementFeatureQuery(
            feature_name,
            object_name="Cells",
            dialect=CELLPROFILER_MEASUREMENT_DIALECT,
        ),
        {"Cells": "Cells"},
    )
    assert indexes is not None
    assert indexes["Cells"].values_by_label == {
        1: float(rows.column_values(feature_name)[0])
    }


@pytest.mark.parametrize(
    "source_name, aliases",
    (
        ("BF_image_1of2", ("bf_image_1_of_2", "bfimage1of2")),
        ("BF_image_2_0", ("bf_image_2_0", "bfimage20")),
    ),
)
def test_unindexed_intensity_lookup_preserves_bin_like_source_names(
    source_name, aliases
):
    lookup = CELLPROFILER_MEASUREMENT_DIALECT.feature_lookup(
        f"Intensity_MeanIntensity_{source_name}"
    )
    assert lookup.source_aliases == aliases


def test_intensity_zernike_rows_own_native_feature_identity_and_axes():
    rows = ObjectIntensityZernikeMeasurementColumnarRows(
        object_ids=(1,),
        zernike_indexes=((2, 0),),
        magnitudes=np.array([[0.5]], dtype=np.float64),
        phases=np.array([[0.0]], dtype=np.float64),
        include_phase=False,
        source_image_name=SOURCE_IMAGE_NAME,
    )

    assert tuple(rows.columns) == (
        "object_label",
        "source_image_name",
        "RadialDistribution_ZernikeMagnitude_BF_image_2_0",
    )
    assert rows.row_count() == 1
    np.testing.assert_array_equal(
        rows.column_values("RadialDistribution_ZernikeMagnitude_BF_image_2_0"), [0.5]
    )
    assert tuple(columnar_row_values(rows, "source_image_name")) == (SOURCE_IMAGE_NAME,)
    native_feature_name = indexed_object_intensity_zernike_feature_name(
        ObjectZernikeDescriptorFeature.INTENSITY_MAGNITUDE,
        source_image_name=SOURCE_IMAGE_NAME,
        degree=2,
        repetition=0,
    )
    assert native_feature_name == "RadialDistribution_ZernikeMagnitude_BF_image_2_0"
    assert (
        CELLPROFILER_MEASUREMENT_DIALECT.projected_feature_name(
            native_feature_name,
            (("n", 2), ("m", 0)),
        )
        == native_feature_name
    )


def test_radial_and_zernike_rows_preserve_exact_zero_row_schemas():
    radial_rows = ObjectIntensityDistributionMeasurementColumnarRows.empty(
        source_image_name=SOURCE_IMAGE_NAME,
        slice_index=0,
    )
    zernike_rows = ObjectIntensityZernikeMeasurementColumnarRows.empty(
        source_image_name=SOURCE_IMAGE_NAME,
        slice_index=0,
    )

    assert tuple(field.name for field in radial_rows.fields) == tuple(
        radial_rows.columns
    )
    assert tuple(field.dtype for field in radial_rows.fields) == (
        int,
        str,
        int,
    )
    assert tuple(field.name for field in zernike_rows.fields) == tuple(
        zernike_rows.columns
    )
    assert tuple(field.dtype for field in zernike_rows.fields) == (
        int,
        str,
        int,
    )
    assert radial_rows.row_count() == 0
    assert zernike_rows.row_count() == 0


def test_intensity_distribution_object_domain_uses_declared_payload_domain():
    labels = np.array(
        [
            [1, 0, 3],
            [1, 0, 3],
            [0, 0, 0],
        ],
        dtype=np.int32,
    )

    with pytest.raises(ValueError, match="explicit object-ID domain"):
        intensity_distribution_object_domain(labels)
    assert intensity_distribution_object_domain(
        ObjectLabelPayload(
            variant_data=ObjectLabelVariantData(labels=labels),
            domain=ObjectLabelDomain(declared_object_count=4),
        )
    ) == (1, 2, 3, 4)


def test_radial_cv_ignores_empty_angular_wedges():
    image = np.ones((3, 3), dtype=np.float32)
    labels = np.ones((3, 3), dtype=np.int32)

    radial_arrays = NativeNumpyRadialDistributionBackendStrategy().measure(
        RadialDistributionMeasureRequest(
            image=image,
            labels=labels,
            d_to_edge=np.zeros(labels.shape, dtype=np.float64),
            d_from_center=np.zeros(labels.shape, dtype=np.float64),
            center_labels=np.ones(labels.shape, dtype=np.int32),
            centers_i=np.array([1.0], dtype=np.float64),
            centers_j=np.array([1.0], dtype=np.float64),
            bin_count=4,
            wants_scaled=True,
            maximum_radius=100,
        )
    )

    assert radial_arrays.radial_cv_by_bin[0, 0] == 0.0


def test_explicit_numba_radial_provider_remains_available():
    selected = radial_distribution_backend(
        backend_provider=CellProfilerBackendProvider.NUMBA,
    )

    assert selected.backend_provider is CellProfilerBackendProvider.NUMBA.provider


def test_measure_object_intensity_distribution_declares_slice_aligned_labels():
    assert (
        object_label_input_execution_mode_from_callable(
            measure_object_intensity_distribution
        )
        is SliceAlignedLabels
    )


def test_measure_object_intensity_distribution_preserves_runtime_slice_axis():
    image = np.full((4, 4), 2.0, dtype=np.float32)
    labels = np.zeros(image.shape, dtype=np.int32)
    labels[1:3, 1:3] = 1

    _result, measurements = measure_object_intensity_distribution(
        source_image(image),
        ObjectLabelPayload(
            variant_data=ObjectLabelVariantData(labels=labels),
            domain=ObjectLabelDomain(declared_object_count=1),
        ),
        bin_count=2,
        wants_zernikes="None",
        slice_index=1,
    )

    assert set(columnar_row_values(measurements, "slice_index")) == {1}


def test_default_intensity_zernike_rows_match_explicit_native_with_missing_objects():
    image = np.arange(32 * 32, dtype=np.float32).reshape(32, 32) / 1024
    labels = np.zeros(image.shape, dtype=np.int32)
    labels[2:13, 3:15] = 1
    labels[17:30, 19:31] = 3
    object_labels = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=ObjectLabelDomain(declared_object_count=3),
    )

    def measure(backend_provider=None):
        kwargs = (
            {}
            if backend_provider is None
            else {"zernike_backend_provider": backend_provider}
        )
        return measure_object_intensity_distribution(
            source_image(image),
            object_labels,
            wants_zernikes=mid.ZernikeMode.MAGNITUDES_AND_PHASE,
            zernike_degree=5,
            **kwargs,
        )[1]

    default_rows = measure()
    native_rows = measure(CellProfilerBackendProvider.NATIVE)
    assert tuple(default_rows.columns) == tuple(native_rows.columns)
    for field in ("object_label", "source_image_name", "slice_index"):
        np.testing.assert_array_equal(
            columnar_row_values(default_rows, field),
            columnar_row_values(native_rows, field),
        )
    for field in default_rows.columns:
        if field in ("object_label", "source_image_name", "slice_index"):
            continue
        np.testing.assert_allclose(
            default_rows.column_values(field),
            native_rows.column_values(field),
            rtol=1e-10,
            atol=1e-12,
            equal_nan=True,
        )


def test_measure_object_intensity_distribution_rejects_unprojected_label_stack():
    image = np.ones((2, 4, 4), dtype=np.float32)
    labels = np.zeros(image.shape, dtype=np.int32)
    labels[0, 1:3, 1:3] = 1
    labels[0, 0, 0] = 3
    labels[1, 1:3, 1:3] = 1

    with pytest.raises(ValueError, match="already projected to one 2-D plane"):
        measure_object_intensity_distribution(
            source_image(image),
            ObjectLabelPayload(variant_data=ObjectLabelVariantData(labels=labels)),
            bin_count=2,
            wants_zernikes="None",
        )


def test_measure_object_intensity_distribution_rejects_repeated_plane_domains():
    image = np.ones((4, 4), dtype=np.float32)
    labels = np.zeros((2, 4, 4), dtype=np.int32)
    labels[:, 1:3, 1:3] = 1
    payload = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=ObjectLabelDomain(
            declared_object_id_domains=((1, 2), (1, 2)),
            scope=ObjectLabelDomainScope.PLANE,
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )

    with pytest.raises(ValueError, match="already projected to one 2-D plane"):
        measure_object_intensity_distribution(
            source_image(image),
            payload,
            bin_count=2,
            wants_zernikes="None",
        )


def test_intensity_zernike_uses_compact_rows_for_noncontiguous_domains():
    image = np.ones((5, 5), dtype=np.float32)
    labels = np.zeros(image.shape, dtype=np.int32)
    labels[1:4, 1:4] = 5

    phase_feature = indexed_object_intensity_zernike_feature_name(
        ObjectZernikeDescriptorFeature.INTENSITY_PHASE,
        source_image_name=SOURCE_IMAGE_NAME,
        degree=0,
        repetition=0,
    )

    rows = IntensityZernikeMeasurementRowsRequest(
        image=image,
        labels=labels,
        max_order=0,
        include_phase=True,
        source_image_name=SOURCE_IMAGE_NAME,
        object_ids=(5,),
        backend_provider=CellProfilerBackendProvider.LEGACY_FAST,
    ).rows()
    assert rows.row_count() == 1
    np.testing.assert_allclose(rows.column_values(phase_feature), [np.pi / 2.0])


def test_intensity_zernike_phase_export_preserves_undefined_phase():
    phase_feature = indexed_object_intensity_zernike_feature_name(
        ObjectZernikeDescriptorFeature.INTENSITY_PHASE,
        source_image_name=SOURCE_IMAGE_NAME,
        degree=0,
        repetition=0,
    )
    rows = ObjectIntensityZernikeMeasurementColumnarRows(
        object_ids=(1,),
        zernike_indexes=((0, 0),),
        magnitudes=np.array([[np.nan]], dtype=np.float64),
        phases=np.array([[np.nan]], dtype=np.float64),
        include_phase=True,
        source_image_name=SOURCE_IMAGE_NAME,
    )

    assert np.isnan(rows.column_values(phase_feature)[0])


def test_intensity_zernike_phase_export_zeroes_undefined_phase_within_extent():
    phase_feature = indexed_object_intensity_zernike_feature_name(
        ObjectZernikeDescriptorFeature.INTENSITY_PHASE,
        source_image_name=SOURCE_IMAGE_NAME,
        degree=0,
        repetition=0,
    )
    rows = ObjectIntensityZernikeMeasurementColumnarRows(
        object_ids=(1, 2),
        zernike_indexes=((0, 0),),
        magnitudes=np.array([[np.nan], [np.nan]], dtype=np.float64),
        phases=np.array([[np.nan], [0.0]], dtype=np.float64),
        include_phase=True,
        source_image_name=SOURCE_IMAGE_NAME,
        phase_zero_extent=1,
    )

    values_by_object = {
        object_label: value
        for object_label, value in zip(
            columnar_row_values(rows, "object_label"),
            rows.column_values(phase_feature),
            strict=True,
        )
    }

    assert values_by_object[1] == 0.0
    assert np.isnan(values_by_object[2])


def test_numba_propagation_result_matches_native_reference_values():
    image = np.arange(64, dtype=np.float64).reshape((8, 8)) / 64.0
    labels = np.zeros((8, 8), dtype=np.int32)
    labels[2, 2] = 1
    labels[2, 5] = 2
    labels[6, 4] = 3
    mask = np.ones((8, 8), dtype=bool)
    mask[4, 1:6] = False

    accelerated = secondary_propagation_backend(
        backend_provider=CellProfilerBackendProvider.NUMBA,
    ).propagate_result(image, labels, mask, 1)
    expected_labels = np.array(
        [
            [1, 1, 1, 1, 2, 2, 2, 2],
            [1, 1, 1, 1, 2, 2, 2, 2],
            [1, 1, 1, 1, 2, 2, 2, 2],
            [1, 1, 1, 1, 2, 2, 2, 2],
            [1, 0, 0, 0, 0, 0, 2, 2],
            [3, 3, 3, 3, 3, 3, 3, 3],
            [3, 3, 3, 3, 3, 3, 3, 3],
            [3, 3, 3, 3, 3, 3, 3, 3],
        ],
        dtype=np.int32,
    )
    expected_distances = np.array(
        [
            [
                3.5446316437742986,
                3.1478426279923740,
                2.7551993223490370,
                2.9730769398448230,
                3.1478426279923740,
                2.7551993223490370,
                2.9730769398448230,
                3.3094569581569550,
            ],
            [
                2.8767489184090140,
                1.8978426279923740,
                1.5051993223490370,
                1.7230769398448231,
                1.8978426279923740,
                1.5051993223490370,
                1.7230769398448231,
                2.7274618573440854,
            ],
            [
                2.0142242070027950,
                1.0098392895035329,
                0.0,
                1.0098392895035329,
                1.0098392895035329,
                0.0,
                1.0098392895035329,
                2.0142242070027950,
            ],
            [
                2.7274618573440854,
                1.7230769398448231,
                1.5051993223490370,
                1.8978426279923740,
                1.7230769398448231,
                1.5051993223490370,
                1.8978426279923740,
                2.8767489184090140,
            ],
            [
                3.4733559354623790,
                -1.0,
                -1.0,
                -1.0,
                -1.0,
                -1.0,
                3.4030419503414110,
                3.7647522568978546,
            ],
            [
                4.8964274974160790,
                3.9175212069994396,
                2.9076819174959070,
                1.8978426279923740,
                1.5051993223490370,
                1.7230769398448231,
                2.7329162293483558,
                3.7373011468476180,
            ],
            [
                4.0339027860098610,
                3.0295178685105990,
                2.0196785790070657,
                1.0098392895035329,
                0.0,
                1.0098392895035329,
                2.0196785790070657,
                3.0240634965063280,
            ],
            [
                4.6034256353538440,
                3.5990407178545816,
                2.5892014283510490,
                1.5793621388475159,
                1.2500000000000000,
                1.6712907857775678,
                2.6811300752811010,
                3.6664675947889904,
            ],
        ],
        dtype=np.float64,
    )

    np.testing.assert_array_equal(accelerated.labels, expected_labels)
    np.testing.assert_allclose(accelerated.distances, expected_distances)


def test_numba_zero_image_propagation_matches_uniform_image_path():
    labels = np.zeros((9, 9), dtype=np.int32)
    labels[1, 1] = 2
    labels[1, 7] = 1
    labels[7, 4] = 3
    mask = np.ones(labels.shape, dtype=bool)
    mask[4, 1:7] = False
    backend = secondary_propagation_backend(
        backend_provider=CellProfilerBackendProvider.NUMBA,
    )

    reference = backend.propagate_result(
        np.zeros(labels.shape, dtype=np.float64),
        labels,
        mask,
        1,
    )
    accelerated = backend.propagate_zero_image_result(labels, mask, 1)

    np.testing.assert_array_equal(accelerated.labels, reference.labels)
    np.testing.assert_allclose(accelerated.distances, reference.distances)


def test_numba_self_centered_radial_distribution_matches_native_reference():
    image = np.arange(25, dtype=np.float32).reshape((5, 5))
    labels = np.array(
        [
            [0, 1, 1, 0, 0],
            [0, 1, 1, 0, 0],
            [0, 0, 0, 2, 2],
            [0, 0, 0, 2, 2],
            [0, 0, 0, 0, 0],
        ],
        dtype=np.int32,
    )

    native = NativeNumpyRadialDistributionBackendStrategy().measure_self_centered(
        image,
        labels,
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )
    accelerated = NumbaNumpyRadialDistributionBackendStrategy().measure_self_centered(
        image,
        labels,
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )

    np.testing.assert_allclose(
        accelerated.fraction_at_distance,
        native.fraction_at_distance,
        equal_nan=True,
    )
    np.testing.assert_allclose(
        accelerated.mean_pixel_fraction,
        native.mean_pixel_fraction,
        equal_nan=True,
    )
    np.testing.assert_allclose(
        accelerated.radial_cv_by_bin,
        native.radial_cv_by_bin,
        equal_nan=True,
    )
    np.testing.assert_array_equal(
        accelerated.object_has_pixels,
        native.object_has_pixels,
    )


def test_numba_self_centered_radial_distribution_preserves_native_zero_intensity_edges():
    image = np.zeros((5, 5), dtype=np.float32)
    labels = np.array(
        [
            [0, 1, 1, 0, 0],
            [0, 1, 1, 0, 0],
            [0, 0, 0, 2, 2],
            [0, 0, 0, 2, 2],
            [0, 0, 0, 0, 0],
        ],
        dtype=np.int32,
    )
    native_backend = NativeNumpyRadialDistributionBackendStrategy()
    accelerated_backend = NumbaNumpyRadialDistributionBackendStrategy()
    geometry = native_backend.label_geometry(labels)

    native = native_backend.measure_self_centered_with_geometry(
        image,
        labels,
        geometry,
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )
    accelerated = accelerated_backend.measure_batch_self_centered_with_geometry(
        (image,),
        labels,
        geometry,
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )[0]

    np.testing.assert_allclose(
        accelerated.fraction_at_distance,
        native.fraction_at_distance,
        equal_nan=True,
    )
    np.testing.assert_allclose(
        accelerated.mean_pixel_fraction,
        native.mean_pixel_fraction,
        equal_nan=True,
    )
    np.testing.assert_allclose(
        accelerated.radial_cv_by_bin,
        native.radial_cv_by_bin,
        equal_nan=True,
    )
    np.testing.assert_array_equal(
        accelerated.object_has_pixels,
        native.object_has_pixels,
    )


@pytest.mark.parametrize(
    "dtype", [np.uint8, np.uint16, np.int16, np.float32, np.float64]
)
@pytest.mark.parametrize("wants_scaled", [True, False])
@pytest.mark.parametrize("image_kind", ["varying", "constant", "zero"])
def test_default_radial_scalar_and_batch_preserve_native_dtype_measurements(
    dtype, wants_scaled, image_kind
):
    labels = np.zeros((12, 14), dtype=np.int32)
    labels[1:10, 1:6] = 1
    labels[3:11, 8:13] = 3  # Keep the missing object row in the dense extent.
    image = np.arange(labels.size, dtype=dtype).reshape(labels.shape)
    if image_kind == "constant":
        image.fill(3)
    elif image_kind == "zero":
        image.fill(0)
    if dtype == np.int16 and image_kind == "varying":
        image -= 80
    native_backend = NativeNumpyRadialDistributionBackendStrategy()
    backend = radial_distribution_backend()
    geometry = native_backend.label_geometry(labels)
    parameters = dict(bin_count=4, wants_scaled=wants_scaled, maximum_radius=3)
    with np.errstate(all="ignore"):
        expected = native_backend.measure_self_centered_with_geometry(
            image, labels, geometry, **parameters
        )
        scalar = backend.measure_self_centered_with_geometry(
            image, labels, geometry, **parameters
        )
        batched = backend.measure_batch_self_centered_with_geometry(
            (image, image[:, ::-1]), labels, geometry, **parameters
        )
        reversed_expected = native_backend.measure_self_centered_with_geometry(
            image[:, ::-1], labels, geometry, **parameters
        )
    for actual, reference in (
        (scalar, expected),
        (batched[0], expected),
        (batched[1], reversed_expected),
    ):
        assert actual.n_bins == reference.n_bins
        assert np.issubdtype(actual.fraction_at_distance.dtype, np.floating)
        np.testing.assert_array_equal(
            actual.object_has_pixels, reference.object_has_pixels
        )
        for field in (
            "fraction_at_distance",
            "mean_pixel_fraction",
            "radial_cv_by_bin",
        ):
            np.testing.assert_allclose(
                getattr(actual, field),
                getattr(reference, field),
                rtol=1e-6,
                atol=1e-6,
                equal_nan=True,
            )


@pytest.mark.parametrize("dtype", [np.float32, np.float64])
@pytest.mark.parametrize(
    "image_kind", ["near_constant", "nan", "infinity", "zero_mean"]
)
def test_default_radial_cv_preserves_native_centered_variance_and_undefined_values(
    dtype, image_kind
):
    labels = np.ones((8, 8), dtype=np.int32)
    image = np.ones(labels.shape, dtype=dtype)
    if image_kind == "near_constant":
        image[::2] += 1e-5 if dtype == np.float32 else 1e-12
    elif image_kind == "nan":
        image[2, 2] = np.nan
    elif image_kind == "infinity":
        image[2, 2] = np.inf
    else:
        image[::2] = -1
    native_backend = NativeNumpyRadialDistributionBackendStrategy()
    backend = radial_distribution_backend()
    geometry = native_backend.label_geometry(labels)
    parameters = dict(bin_count=4, wants_scaled=True, maximum_radius=100)
    with np.errstate(all="ignore"):
        expected = native_backend.measure_self_centered_with_geometry(
            image, labels, geometry, **parameters
        )
        scalar = backend.measure_self_centered_with_geometry(
            image, labels, geometry, **parameters
        )
        batched = backend.measure_batch_self_centered_with_geometry(
            (image,), labels, geometry, **parameters
        )[0]
    for actual in (scalar, batched):
        for field in (
            "fraction_at_distance",
            "mean_pixel_fraction",
            "radial_cv_by_bin",
        ):
            np.testing.assert_allclose(
                getattr(actual, field),
                getattr(expected, field),
                rtol=1e-6,
                atol=1e-6,
                equal_nan=True,
            )


def _radial_request_for_boundary_tests():
    image = np.ones((4, 4), dtype=np.float32)
    labels = np.ones(image.shape, dtype=np.int32)
    return RadialDistributionMeasureRequest(
        image=image,
        labels=labels,
        d_to_edge=np.ones(image.shape, dtype=np.float64),
        d_from_center=np.ones(image.shape, dtype=np.float64),
        center_labels=labels.copy(),
        centers_i=np.array([1.5]),
        centers_j=np.array([1.5]),
        bin_count=4,
        wants_scaled=True,
        maximum_radius=100,
    )


@pytest.mark.parametrize(
    "backend_type",
    (
        NativeNumpyRadialDistributionBackendStrategy,
        NumbaNumpyRadialDistributionBackendStrategy,
    ),
)
@pytest.mark.parametrize("field", ("d_to_edge", "d_from_center", "center_labels"))
def test_radial_backend_rejects_misaligned_geometry(backend_type, field):
    request = _radial_request_for_boundary_tests()
    request = replace(request, **{field: getattr(request, field)[:1]})
    with pytest.raises(ValueError, match="geometry must match"):
        backend_type().measure(request)


@pytest.mark.parametrize(
    "backend_type",
    (
        NativeNumpyRadialDistributionBackendStrategy,
        NumbaNumpyRadialDistributionBackendStrategy,
    ),
)
@pytest.mark.parametrize("centers_j", (np.zeros(2), np.zeros((1, 1))))
def test_radial_backend_rejects_incompatible_center_vectors(backend_type, centers_j):
    request = replace(_radial_request_for_boundary_tests(), centers_j=centers_j)
    with pytest.raises(ValueError, match="equal-length vectors"):
        backend_type().measure(request)


@pytest.mark.parametrize(
    "backend_type",
    (
        NativeNumpyRadialDistributionBackendStrategy,
        NumbaNumpyRadialDistributionBackendStrategy,
    ),
)
def test_radial_backend_rejects_undeclared_center_ids(backend_type):
    request = _radial_request_for_boundary_tests()
    request = replace(
        request, center_labels=np.full(request.image.shape, 2, dtype=np.int32)
    )
    with pytest.raises(ValueError, match="exceed the declared center"):
        backend_type().measure(request)


@pytest.mark.parametrize(
    "backend_type",
    (
        NativeNumpyRadialDistributionBackendStrategy,
        NumbaNumpyRadialDistributionBackendStrategy,
    ),
)
def test_radial_batch_validates_every_image_against_shared_geometry(backend_type):
    request = _radial_request_for_boundary_tests()
    geometry = mid.RadialLabelGeometry(
        request.d_to_edge,
        mid.RadialCenterDistanceFields(
            request.d_from_center,
            request.center_labels,
            request.centers_i,
            request.centers_j,
        ),
    )
    with pytest.raises(ValueError, match="labels must match"):
        backend_type().measure_batch_self_centered_with_geometry(
            (request.image, request.image[:1]),
            request.labels,
            geometry,
            bin_count=request.bin_count,
            wants_scaled=request.wants_scaled,
            maximum_radius=request.maximum_radius,
        )
