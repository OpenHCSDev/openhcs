import numpy as np
import pytest

from openhcs.processing.backends.cellprofiler._granularity_native import (
    sample_order_one_grid,
)

from openhcs.core.measurement_row_materialization import (
    MeasurementProjectedColumnarRows,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.processing.backends.cellprofiler.granularity import (
    GranularityImageSeriesCache,
    GRANULARITY_SPECTRUM_LENGTH,
    GranularityImageSeriesRequest,
    GranularitySamplingGrid,
    GranularitySpectrumDescriptor,
    GranularitySpectrumDescriptorDeclaration,
    MeasureGranularityModule,
    CppGranularityReconstructionBackendStrategy,
    NativeGranularityReconstructionBackendStrategy,
    NumbaGranularityReconstructionBackendStrategy,
    ObjectGranularityMeasurementRows,
    OpenCVGranularityReconstructionBackendStrategy,
    background_corrected_pixels,
    granularity_grey_erosion,
    granularity_reconstruction_backend,
    granularity_reconstruction_series,
    measure_granularity_objects,
)
from openhcs.core.config import DtypeConfig


@pytest.mark.parametrize(
    "dtype",
    [
        np.bool_,
        np.int8,
        np.uint8,
        np.int16,
        np.uint16,
        np.int32,
        np.uint32,
        np.int64,
        np.uint64,
        np.float32,
        np.float64,
    ],
)
@pytest.mark.parametrize("shape", [(1, 1), (1, 7), (7, 1), (6, 8)])
@pytest.mark.parametrize("scales", [(0.5, 0.25), (1.0, 1.0), (1.3, -0.25)])
def test_owned_granularity_grid_matches_scipy_dtypes_and_constant_borders(
    dtype, shape, scales
):
    from scipy.ndimage import map_coordinates

    image = (np.arange(np.prod(shape)).reshape(shape) % 17).astype(dtype)
    grid = GranularitySamplingGrid((5.25, 8.5))
    rows, columns = np.mgrid[0:5.25, 0:8.5].astype(float)
    rows *= scales[0]
    columns *= scales[1]
    expected = map_coordinates(image, (rows, columns), order=1)
    actual = grid.sample_pixels(image, coordinate_scales=scales)
    np.testing.assert_array_equal(actual, expected)
    assert actual.dtype == expected.dtype


@pytest.mark.parametrize("dtype", [np.int64, np.uint64])
@pytest.mark.parametrize("scales", [(1.0, 1.0), (0.5, 0.5), (0.1, 0.2)])
def test_owned_granularity_grid_preserves_native_64bit_cast_extrema(dtype, scales):
    from scipy.ndimage import map_coordinates

    limits = np.iinfo(dtype)
    image = np.array([[limits.min, limits.max], [limits.max, limits.min]], dtype=dtype)
    rows, columns = np.mgrid[:4, :4].astype(float)
    expected = map_coordinates(image, (rows * scales[0], columns * scales[1]), order=1)
    actual = GranularitySamplingGrid((4, 4)).sample_pixels(
        image, coordinate_scales=scales
    )
    np.testing.assert_array_equal(actual, expected)


@pytest.mark.parametrize("dtype", [np.float32, np.float64, np.complex64, np.complex128])
@pytest.mark.parametrize("layout", ["strided", "readonly", "non_native_endian"])
def test_owned_granularity_grid_preserves_nonfinite_values_and_array_layouts(
    dtype, layout
):
    from scipy.ndimage import map_coordinates

    image = np.arange(48, dtype=np.float64).reshape(6, 8).astype(dtype)
    image[2, 2] = np.nan
    image[3, 3] = np.inf
    if np.issubdtype(dtype, np.complexfloating):
        image.imag[:] = np.arange(48, dtype=np.float64).reshape(image.shape)
        image.imag[1, 1] = np.nan
        image.imag[4, 4] = np.inf
    if layout == "strided":
        image = image[:, ::2]
    elif layout == "readonly":
        image.setflags(write=False)
    else:
        image = image.astype(image.dtype.newbyteorder(">"))
    before = image.tobytes()
    rows, columns = np.mgrid[:7, :9].astype(float)
    expected = map_coordinates(image, (rows * 0.75, columns * 0.5), order=1)
    actual = GranularitySamplingGrid((7, 9)).sample_pixels(
        image, coordinate_scales=(0.75, 0.5)
    )
    if np.iscomplexobj(image):
        np.testing.assert_array_equal(actual.real, expected.real)
        np.testing.assert_array_equal(actual.imag, expected.imag)
    else:
        np.testing.assert_array_equal(actual, expected)
    assert actual.dtype == expected.dtype
    assert image.tobytes() == before


def test_owned_granularity_grid_uses_logical_extents_for_endpoint_scales():
    from scipy.ndimage import map_coordinates

    original = GranularitySamplingGrid((9, 11))
    source = original.subsampled(0.5)
    assert source.logical_shape == (4.5, 5.5)
    assert source.array_shape == (5, 6)
    image = np.arange(30, dtype=np.float64).reshape(source.array_shape)
    rows, columns = np.mgrid[:9, :11].astype(float)
    expected = map_coordinates(image, (rows * (3.5 / 8), columns * (4.5 / 10)), order=1)
    np.testing.assert_array_equal(original.sample_grid(image, source), expected)


@pytest.mark.parametrize("dtype", [np.float32, np.float64])
@pytest.mark.parametrize("axis", [0, 1])
@pytest.mark.parametrize("value", [np.nan, np.inf])
def test_owned_granularity_grid_preserves_zero_weight_mirrored_edge_values(
    dtype, axis, value
):
    from scipy.ndimage import map_coordinates

    image = np.ones((4, 5), dtype=dtype)
    if axis == 0:
        image[-2, :] = value
    else:
        image[:, -2] = value
    coordinates = np.mgrid[:4, :5].astype(float)
    expected = map_coordinates(image, coordinates, order=1)
    actual = GranularitySamplingGrid(tuple(image.shape)).sample_pixels(
        image, coordinate_scales=(1.0, 1.0)
    )
    np.testing.assert_array_equal(actual, expected)


@pytest.mark.parametrize(
    "invalid,expected_error",
    [
        ("image_rank", ValueError),
        ("output_rank", ValueError),
        ("format", ValueError),
        ("readonly", ValueError),
        ("strided", ValueError),
        ("unsupported_dtype", RuntimeError),
    ],
)
def test_native_granularity_sampling_releases_buffers_on_failure(
    invalid, expected_error
):
    import sys

    image = np.ones((4, 4), dtype=np.float32)
    output = np.zeros_like(image)
    if invalid == "image_rank":
        image = image.ravel()
    elif invalid == "output_rank":
        output = output.ravel()
    elif invalid == "format":
        output = output.astype(np.float64)
    elif invalid == "readonly":
        output.setflags(write=False)
    elif invalid == "strided":
        image = image[:, ::2]
    else:
        image = image.astype(np.float16)
        output = output.astype(np.float16)
    references = (sys.getrefcount(image), sys.getrefcount(output))
    for _ in range(3):
        with pytest.raises(expected_error):
            sample_order_one_grid(image, output, 0.5, 0.5)
        assert references == (sys.getrefcount(image), sys.getrefcount(output))


def test_measure_granularity_declares_one_indexed_spectrum_feature_authority():
    feature = MeasureGranularityModule.MeasurementFeature.SPECTRUM
    descriptor = GranularitySpectrumDescriptor(GRANULARITY_SPECTRUM_LENGTH)

    assert tuple(MeasureGranularityModule.MeasurementFeature) == (feature,)
    assert MeasureGranularityModule.numbered_measurement_feature_prefix_aliases == {}
    assert MeasureGranularityModule.source_qualified_measurement_feature_types() == (
        MeasureGranularityModule.MeasurementFeature,
    )
    assert feature.indexed_descriptor_declarations() == (
        GranularitySpectrumDescriptorDeclaration,
    )
    assert (
        GranularitySpectrumDescriptorDeclaration.from_measurement_row_field_name("gs16")
        == descriptor
    )
    assert (
        GranularitySpectrumDescriptorDeclaration.from_feature_name("Granularity_16")
        == descriptor
    )
    assert (
        GranularitySpectrumDescriptorDeclaration.source_qualified_feature_name(
            descriptor,
            source_image_name="BF_image",
        )
        == "Granularity_16_BF_image"
    )


def test_measure_granularity_projects_exact_image_feature_identities_at_producer():
    projected = MeasureGranularityModule.prepare_measurement_record_rows(
        MeasurementProjectedColumnarRows(
            {
                "slice_index": (0,),
                "gs1": (1.25,),
                "gs16": (16.25,),
            },
            fields=(
                FieldSpec("slice_index", int),
                FieldSpec("gs1", float),
                FieldSpec("gs16", float),
            ),
        ),
        source_image_name="BF_image",
    )

    assert tuple(projected.columns) == (
        "slice_index",
        "Granularity_1_BF_image",
        "Granularity_16_BF_image",
    )
    assert projected.column_values("Granularity_1_BF_image") == (1.25,)
    assert projected.column_values("Granularity_16_BF_image") == (16.25,)


def test_measure_granularity_projects_exact_object_feature_identities_at_producer():
    rows = ObjectGranularityMeasurementRows(
        np.asarray((3,), dtype=np.int32),
        np.arange(1.0, 17.0, dtype=np.float64).reshape(1, 16),
    )

    projected = MeasureGranularityModule.prepare_measurement_record_rows(
        rows,
        source_image_name="BF_image",
    )

    assert "gs1" not in projected.columns
    assert "gs16" not in projected.columns
    np.testing.assert_array_equal(
        projected.column_values("Granularity_1_BF_image"),
        np.asarray((1.0,)),
    )
    np.testing.assert_array_equal(
        projected.column_values("Granularity_16_BF_image"),
        np.asarray((16.0,)),
    )


def test_object_granularity_rows_preserve_exact_zero_row_schema():
    rows = ObjectGranularityMeasurementRows(
        np.empty(0, dtype=np.int32),
        np.empty((0, GRANULARITY_SPECTRUM_LENGTH), dtype=np.float64),
    )

    assert tuple(field.name for field in rows.fields) == tuple(rows.columns)
    assert tuple(field.dtype for field in rows.fields[:2]) == (int, int)
    assert all(field.dtype is float for field in rows.fields[2:])
    assert rows.row_count() == 0


def test_measure_granularity_objects_preserves_sparse_label_ids():
    image = np.ones((5, 5), dtype=np.float32)
    labels = np.array(
        [
            [1, 1, 0, 3, 3],
            [1, 1, 0, 3, 3],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ],
        dtype=np.int32,
    )

    _result, measurements = measure_granularity_objects(
        image,
        labels,
        subsample_size=1.0,
        background_subsample_size=1.0,
        element_radius=1,
        spectrum_length=1,
        dtype_config=DtypeConfig(),
    )

    assert [measurement.object_id for measurement in measurements] == [1, 3]


def test_granularity_series_cache_reuses_equal_image_values():
    image = np.arange(36, dtype=np.float64).reshape(6, 6)
    image_copy = image.copy()
    cache = GranularityImageSeriesCache.process_cache()
    cache.clear()

    first = GranularityImageSeriesRequest(
        image=image,
        subsample_size=1.0,
        background_subsample_size=1.0,
        element_radius=1,
        spectrum_length=2,
        profile_function="test",
    ).series()
    second = GranularityImageSeriesRequest(
        image=image_copy,
        subsample_size=1.0,
        background_subsample_size=1.0,
        element_radius=1,
        spectrum_length=2,
        profile_function="test",
    ).series()

    assert second is first
    assert len(cache.entries) == 1


def test_measure_granularity_objects_uses_order_one_coordinate_sampling_after_subsampling():
    import scipy.ndimage

    image = np.arange(25, dtype=np.float64).reshape(5, 5) / 25.0
    labels = np.array(
        [
            [1, 1, 0, 0, 3],
            [1, 0, 0, 3, 3],
            [0, 0, 3, 3, 0],
            [0, 0, 0, 0, 0],
            [1, 1, 0, 0, 0],
        ],
        dtype=np.int32,
    )
    _result, measurements = measure_granularity_objects(
        image,
        labels,
        subsample_size=0.8,
        background_subsample_size=1.0,
        element_radius=1,
        spectrum_length=1,
        dtype_config=DtypeConfig(),
    )

    series = GranularityImageSeriesRequest(
        image=image,
        subsample_size=0.8,
        background_subsample_size=1.0,
        element_radius=1,
        spectrum_length=1,
        profile_function="test",
    ).series()
    object_ids = np.array([measurement.object_id for measurement in measurements])
    current_means = scipy.ndimage.mean(image, labels, object_ids)
    start_means = np.maximum(current_means, np.finfo(float).eps)
    rec = series.reconstructions[0]
    row_scale = float(series.grid.logical_shape[0] - 1) / float(labels.shape[0] - 1)
    col_scale = float(series.grid.logical_shape[1] - 1) / float(labels.shape[1] - 1)
    ri, rj = np.mgrid[0 : labels.shape[0], 0 : labels.shape[1]].astype(np.float64)
    ri *= row_scale
    rj *= col_scale
    rec_full = scipy.ndimage.map_coordinates(rec, (ri, rj), order=1)
    new_means = scipy.ndimage.mean(rec_full, labels, object_ids)
    expected = (current_means - new_means) * 100 / start_means
    actual = np.array([measurement.gs1 for measurement in measurements])

    np.testing.assert_allclose(actual, expected)


def test_background_corrected_pixels_match_reference_operations():
    import scipy.ndimage
    import skimage.morphology

    image = np.arange(99, dtype=np.float64).reshape(9, 11) / 99.0
    pixels, _shape = background_corrected_pixels(
        image,
        subsample_size=1.0,
        background_subsample_size=0.5,
        element_radius=1,
    )

    back_shape = np.asarray(image.shape) * 0.5
    bi, bj = np.mgrid[0 : back_shape[0], 0 : back_shape[1]].astype(float) / 0.5
    back_pixels = scipy.ndimage.map_coordinates(image, (bi, bj), order=1)
    footprint = skimage.morphology.disk(1, dtype=bool)
    back_pixels = skimage.morphology.erosion(back_pixels, footprint=footprint)
    back_pixels = skimage.morphology.dilation(back_pixels, footprint=footprint)
    ui, uj = np.mgrid[0 : image.shape[0], 0 : image.shape[1]].astype(float)
    ui *= float(back_shape[0] - 1) / float(image.shape[0] - 1)
    uj *= float(back_shape[1] - 1) / float(image.shape[1] - 1)
    expected = image - scipy.ndimage.map_coordinates(back_pixels, (ui, uj), order=1)
    expected[expected < 0] = 0

    np.testing.assert_allclose(pixels, expected)


def test_granularity_reconstruction_default_backend_is_cpp():
    assert isinstance(
        granularity_reconstruction_backend(),
        CppGranularityReconstructionBackendStrategy,
    )


def test_cpp_granularity_reconstruction_matches_numba_and_native():
    import skimage.morphology

    rng = np.random.default_rng(25)
    pixels = rng.random((40, 41), dtype=np.float32)
    seed = granularity_grey_erosion(pixels, skimage.morphology.disk(1, dtype=np.uint8))
    native = NativeGranularityReconstructionBackendStrategy().reconstruct_radius_one(
        seed, pixels
    )
    cpp = CppGranularityReconstructionBackendStrategy().reconstruct_radius_one(
        seed, pixels
    )
    np.testing.assert_array_equal(cpp, native)
    np.testing.assert_array_equal(
        cpp,
        NumbaGranularityReconstructionBackendStrategy().reconstruct_radius_one(
            seed, pixels
        ),
    )


def test_numba_granularity_reconstruction_matches_native_radius_one():
    import skimage.morphology

    rng = np.random.default_rng(22)
    pixels = rng.random((40, 41), dtype=np.float32)
    footprint = skimage.morphology.disk(1, dtype=np.uint8)
    seed = granularity_grey_erosion(pixels, footprint)

    native = NativeGranularityReconstructionBackendStrategy().reconstruct_radius_one(
        seed,
        pixels,
    )
    accelerated = (
        NumbaGranularityReconstructionBackendStrategy().reconstruct_radius_one(
            seed,
            pixels,
        )
    )

    np.testing.assert_array_equal(accelerated, native)


def test_opencv_granularity_reconstruction_matches_native_radius_one():
    import skimage.morphology

    rng = np.random.default_rng(24)
    pixels = rng.random((40, 41), dtype=np.float32)
    footprint = skimage.morphology.disk(1, dtype=np.uint8)
    seed = granularity_grey_erosion(pixels, footprint)

    native = NativeGranularityReconstructionBackendStrategy().reconstruct_radius_one(
        seed,
        pixels,
    )
    accelerated = (
        OpenCVGranularityReconstructionBackendStrategy().reconstruct_radius_one(
            seed,
            pixels,
        )
    )

    np.testing.assert_array_equal(accelerated, native)


def test_numba_granularity_reconstruction_series_matches_reference():
    import skimage.morphology

    rng = np.random.default_rng(23)
    pixels = rng.random((35, 37), dtype=np.float32)
    footprint = skimage.morphology.disk(1, dtype=bool)
    erosion_footprint = skimage.morphology.disk(1, dtype=np.uint8)
    expected = []
    ero = pixels.copy()
    for _index in range(3):
        ero = granularity_grey_erosion(ero, erosion_footprint)
        expected.append(
            skimage.morphology.reconstruction(
                ero,
                pixels,
                footprint=footprint,
            )
        )

    actual = granularity_reconstruction_series(pixels, 3)

    for actual_image, expected_image in zip(actual, expected, strict=True):
        np.testing.assert_array_equal(actual_image, expected_image)


def test_measure_granularity_objects_matches_reference_operations():
    import scipy.ndimage
    import skimage.morphology

    image = np.array(
        [
            [0.0, 0.1, 0.4, 0.2, 0.0],
            [0.2, 0.7, 0.9, 0.5, 0.1],
            [0.1, 0.6, 0.8, 0.4, 0.2],
            [0.0, 0.2, 0.5, 0.3, 0.1],
        ],
        dtype=np.float64,
    )
    labels = np.array(
        [
            [1, 1, 1, 0, 0],
            [1, 1, 1, 2, 2],
            [0, 0, 2, 2, 2],
            [0, 0, 2, 2, 2],
        ],
        dtype=np.int32,
    )

    _result, actual_measurements = measure_granularity_objects(
        image,
        labels,
        subsample_size=1.0,
        background_subsample_size=1.0,
        element_radius=1,
        spectrum_length=2,
        dtype_config=DtypeConfig(),
    )

    footprint = skimage.morphology.disk(1, dtype=bool)
    pixels = skimage.morphology.erosion(image, footprint=footprint)
    pixels = skimage.morphology.dilation(pixels, footprint=footprint)
    pixels = image - pixels
    pixels[pixels < 0] = 0
    object_ids = np.array([1, 2], dtype=np.int32)
    current_means = scipy.ndimage.mean(image, labels, object_ids)
    start_means = np.maximum(current_means, np.finfo(float).eps)
    ero = pixels.copy()
    expected = []
    for _index in range(2):
        previous_means = current_means.copy()
        ero = skimage.morphology.erosion(ero, footprint=footprint)
        rec = skimage.morphology.reconstruction(ero, pixels, footprint=footprint)
        current_means = scipy.ndimage.mean(rec, labels, object_ids)
        expected.append((previous_means - current_means) * 100 / start_means)

    actual = np.array(
        [[measurement.gs1, measurement.gs2] for measurement in actual_measurements]
    )
    np.testing.assert_allclose(actual, np.asarray(expected).T)


def test_measure_granularity_objects_preserves_negative_first_scale():
    rng = np.random.default_rng(51)
    image = rng.random((40, 40))
    labels = np.zeros((40, 40), dtype=np.int32)
    labels[5:15, 5:15] = 1
    labels[20:35, 20:35] = 2

    _result, measurements = measure_granularity_objects(
        image,
        labels,
        subsample_size=0.25,
        background_subsample_size=0.25,
        element_radius=10,
        spectrum_length=2,
        dtype_config=DtypeConfig(),
    )

    assert measurements[0].gs1 < 0.0
    assert measurements[0].gs2 >= 0.0
