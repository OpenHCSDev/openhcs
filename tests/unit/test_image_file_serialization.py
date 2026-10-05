import os
from contextlib import nullcontext
from dataclasses import replace

import numpy as np
import pytest
import tifffile

from openhcs.core.image_file_serialization import (
    ImageFileFormat,
    ImageFileSourceMetadata,
    NumpyImageFileFormat,
    PngImageFileFormat,
    SourceImagePixelSemantics,
    TiffImageFileFormat,
    image_file_source_metadata,
    image_payload_as_uint8,
    prepare_disk_image_payloads,
    require_image_file_source_metadata,
)
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload,
    ImagePayloadMetadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis


def test_jpeg_disk_serialization_scales_unit_float_image_to_uint8() -> None:
    image = np.array([[0.0, 0.5, 1.0]], dtype=np.float32)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.JPG",))

    assert prepared.dtype == np.uint8
    np.testing.assert_array_equal(prepared, np.array([[0, 128, 255]], dtype=np.uint8))


def test_png_disk_serialization_preserves_float32_quantization() -> None:
    image = np.array([[np.float32(2.5 / 255.0)]], dtype=np.float32)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.png",))

    assert prepared.dtype == np.uint8
    np.testing.assert_array_equal(prepared, np.array([[2]], dtype=np.uint8))


@pytest.mark.parametrize("dtype", (np.float16, np.float32, np.float64))
@pytest.mark.parametrize(
    ("values", "expected"),
    (
        ((np.nan, -np.inf, np.inf, 0.0, 0.5, 1.0), (0, 0, 255, 0, 128, 255)),
        ((np.nan, -np.inf, np.inf, -1.0, 2.5, 3.5, 300.0), (0, 0, 255, 0, 2, 4, 255)),
    ),
)
def test_uint8_conversion_preserves_readonly_pixels_and_rounding(
    dtype, values, expected
) -> None:
    storage = np.zeros((len(values), 2), dtype=dtype)
    storage[:, 0] = values
    image = storage[:, 0]
    original = storage.copy()
    image.setflags(write=False)

    converted = image_payload_as_uint8(image)

    np.testing.assert_array_equal(converted, np.asarray(expected, dtype=np.uint8))
    np.testing.assert_array_equal(storage, original)
    assert not np.shares_memory(image, converted)


@pytest.mark.parametrize(
    "image",
    (
        np.asarray((0, 2, 4, 300), dtype=np.int32),
        np.asarray((0 + 10j, 2.5 + 30j, 3.5 - 3j, 300 + 100j)),
    ),
)
def test_uint8_conversion_owns_cast_pixels(image) -> None:
    original = image.copy()
    image.setflags(write=False)
    warning = (
        pytest.warns(np.exceptions.ComplexWarning)
        if np.issubdtype(image.dtype, np.complexfloating)
        else nullcontext()
    )

    with warning:
        converted = image_payload_as_uint8(image)

    np.testing.assert_array_equal(converted, np.asarray((0, 2, 4, 255), dtype=np.uint8))
    np.testing.assert_array_equal(image, original)
    assert not np.shares_memory(image, converted)


def test_jpeg_disk_serialization_clips_non_unit_float_image_to_uint8() -> None:
    image = np.array([[-5.0, 12.2, 300.0]], dtype=np.float32)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.jpg",))

    assert prepared.dtype == np.uint8
    np.testing.assert_array_equal(prepared, np.array([[0, 12, 255]], dtype=np.uint8))


def test_png_disk_serialization_preserves_uint16_image() -> None:
    image = np.array([[0, 1024]], dtype=np.uint16)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.png",))

    assert prepared is image


def test_png_disk_serialization_does_not_infer_singleton_color_stack() -> None:
    image = np.zeros((1, 3, 4, 3), dtype=np.uint8)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.png",))

    assert prepared.shape == image.shape
    assert prepared.dtype == np.uint8


def test_jpeg_disk_serialization_does_not_infer_singleton_grayscale_stack() -> None:
    image = np.ones((1, 3, 5), dtype=np.float32)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.jpg",))

    assert prepared.shape == image.shape
    assert prepared.dtype == np.uint8


def test_png_disk_serialization_preserves_one_row_color_slice() -> None:
    image = np.zeros((1, 4, 3), dtype=np.uint8)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.png",))

    assert prepared.shape == (1, 4, 3)
    assert prepared.dtype == np.uint8


def test_tiff_disk_serialization_preserves_float_payload() -> None:
    image = np.array([[0.25]], dtype=np.float32)

    (prepared,) = prepare_disk_image_payloads((image,), ("out.tif",))

    assert prepared is image


def test_registered_tiff_format_round_trips_grayscale_pixels(tmp_path) -> None:
    path = tmp_path / "image.tif"
    image = np.arange(20, dtype=np.uint8).reshape(4, 5)

    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, image)

    np.testing.assert_array_equal(image_format.read(path), image)


def test_tiff_source_metadata_reads_dtype_and_declared_scale_without_imageio(
    tmp_path,
    monkeypatch,
) -> None:
    import imageio.v3 as iio
    import tifffile

    path = tmp_path / "source.tif"
    tifffile.imwrite(
        path,
        np.array([[0, 4095]], dtype=np.uint16),
        extratags=((281, "H", 1, 4095, False),),
    )
    monkeypatch.setattr(
        iio,
        "improps",
        lambda *_args, **_kwargs: pytest.fail("TIFF metadata reopened through ImageIO"),
    )

    metadata = TiffImageFileFormat().source_metadata(path)

    assert metadata.source_dtype == np.dtype(np.uint16)
    assert metadata.intensity_scale == 4095.0
    assert metadata.image_shape_yx == (1, 2)
    assert metadata.pixel_semantics.channel_axis is None
    assert metadata.pixel_semantics.channel_count is None


def test_tiff_source_metadata_reads_rgb_semantics_without_generic_reopen(
    tmp_path,
    monkeypatch,
) -> None:
    import tifffile

    path = tmp_path / "rgb.tiff"
    tifffile.imwrite(path, np.zeros((4, 5, 3), dtype=np.uint8), photometric="rgb")
    monkeypatch.setattr(
        TiffImageFileFormat,
        "pixel_semantics",
        lambda *_args, **_kwargs: pytest.fail(
            "TIFF source metadata reopened inherited pixel semantics"
        ),
    )

    metadata = TiffImageFileFormat().source_metadata(path)

    assert metadata.source_dtype == np.dtype(np.uint8)
    assert metadata.intensity_scale == 255.0
    assert metadata.pixel_semantics.channel_axis == -1
    assert metadata.pixel_semantics.channel_count == 3
    assert metadata.image_shape_yx == (4, 5)
    assert metadata.pixel_semantics.validated_channel_axis(tifffile.imread(path)) == -1


def test_tiff_required_source_metadata_fails_closed_for_unreadable_header(
    tmp_path,
) -> None:
    path = tmp_path / "broken.tif"
    path.write_bytes(b"not a tiff")

    with pytest.raises(tifffile.TiffFileError):
        TiffImageFileFormat().require_source_metadata(path)

    assert TiffImageFileFormat().source_metadata(path).source_dtype is None


def test_required_source_metadata_does_not_reuse_replaced_header(
    tmp_path,
) -> None:
    path = tmp_path / "replaceable.tif"
    tifffile.imwrite(path, np.zeros((4, 5, 3), dtype=np.uint8), photometric="rgb")
    assert require_image_file_source_metadata(path).pixel_semantics.channel_axis == -1
    assert image_file_source_metadata(path).pixel_semantics.channel_axis == -1

    tifffile.imwrite(path, np.zeros((4, 5), dtype=np.uint8))

    assert require_image_file_source_metadata(path).pixel_semantics.channel_axis is None
    assert image_file_source_metadata(path).pixel_semantics.channel_axis is None
    assert require_image_file_source_metadata(path).image_shape_yx == (4, 5)


def test_numpy_source_header_owns_shape_dtype_and_revision_without_pixel_decode(
    tmp_path, monkeypatch
) -> None:
    path = tmp_path / "illum.npy"
    np.save(path, np.zeros((5, 7), dtype=np.float32))
    original_load = np.load
    calls = []

    def load_header(file, *, mmap_mode, allow_pickle):
        assert mmap_mode == "r"
        assert allow_pickle is False
        calls.append(file)
        return original_load(file, mmap_mode=mmap_mode, allow_pickle=allow_pickle)

    monkeypatch.setattr(np, "load", load_header)
    metadata = require_image_file_source_metadata(path)
    assert metadata.image_shape_yx == (5, 7)
    assert metadata.source_dtype == np.dtype(np.float32)
    assert require_image_file_source_metadata(path) is metadata
    assert len(calls) == 1
    np.save(path, np.zeros((3, 4), dtype=np.uint16))
    replaced = require_image_file_source_metadata(path)
    assert replaced.image_shape_yx == (3, 4)
    assert replaced.source_dtype == np.dtype(np.uint16)
    assert len(calls) == 2


@pytest.mark.parametrize(
    "shape", ((1,), (1, 2, 3), (0, 2), (-1, 2), (True, 2), (1.0, 2))
)
def test_source_header_refuses_invalid_declared_yx_dimensions(shape) -> None:
    with pytest.raises(ValueError, match="two positive integer dimensions"):
        ImageFileSourceMetadata(image_shape_yx=shape)


@pytest.mark.parametrize(
    "axis,shape,expected",
    (
        (-1, (5, 7, 3), (5, 7)),
        (0, (3, 5, 7), (5, 7)),
        (None, (5, 7), (5, 7)),
        (None, (5, 7, 3), None),
    ),
)
def test_format_declared_image_shape_shares_loaded_channel_validation(
    axis, shape, expected
) -> None:
    semantics = SourceImagePixelSemantics(axis, 3 if axis is not None else None)
    assert semantics.image_shape_yx_for_shape(shape) == expected
    assert semantics.validated_channel_axis(np.zeros(shape, dtype=np.uint8)) == axis


@pytest.mark.parametrize("shape", ((5, 7, 4), (5, 7), ()))
def test_source_header_and_loaded_pixels_refuse_same_invalid_channel_layout(
    shape,
) -> None:
    semantics = SourceImagePixelSemantics(2, 3)
    with pytest.raises(ValueError):
        semantics.image_shape_yx_for_shape(shape)
    with pytest.raises(ValueError):
        semantics.validated_channel_axis(np.zeros(shape, dtype=np.uint8))


def test_no_channel_declaration_does_not_inspect_payload(monkeypatch) -> None:
    from openhcs.core import image_file_serialization

    monkeypatch.setattr(
        image_file_serialization,
        "image_payload_data",
        lambda _payload: pytest.fail("No-axis guard must precede payload inspection"),
    )
    assert SourceImagePixelSemantics().validated_channel_axis(object()) is None


def test_declared_negative_channel_axis_is_not_wrapped_into_valid_range() -> None:
    semantics = SourceImagePixelSemantics(-4, 3)
    with pytest.raises(ValueError, match="axis -4 is invalid"):
        semantics.image_shape_yx_for_shape((5, 7, 3))
    with pytest.raises(ValueError, match="axis -4 is invalid"):
        semantics.validated_channel_axis(np.zeros((5, 7, 3)))


def test_numpy_non_image_header_does_not_infer_spatial_axes(tmp_path) -> None:
    for name, shape in (("scalar", ()), ("volume", (2, 5, 7)), ("color", (5, 7, 3))):
        path = tmp_path / f"{name}.npy"
        np.save(path, np.zeros(shape, dtype=np.float32))
        metadata = require_image_file_source_metadata(path)
        assert metadata.image_shape_yx is None
        assert metadata.source_frame_shape is None
        with pytest.raises(ValueError, match="container-frame mapping"):
            metadata.frame_for_source_indices((0,))


def test_tiff_header_owns_selected_frame_grid_and_bounds(tmp_path) -> None:
    path = tmp_path / "frames.tif"
    tifffile.imwrite(
        path,
        np.zeros((2, 3, 5, 7), dtype=np.uint16),
        photometric="minisblack",
        metadata={"axes": "TZYX"},
    )
    metadata = require_image_file_source_metadata(path)
    assert metadata.image_shape_yx == (5, 7)
    assert metadata.source_frame_shape == (2, 3)
    assert metadata.frame_for_source_indices((1, 2)) == 5
    with pytest.raises(ValueError, match="complete container-frame mapping"):
        metadata.frame_for_source_indices((1,))
    with pytest.raises(ValueError, match="outside dimension"):
        metadata.frame_for_source_indices((2, 0))


def test_tiff_source_metadata_uses_declared_planar_sample_axis(tmp_path) -> None:
    import tifffile

    path = tmp_path / "planar-rgb.tiff"
    tifffile.imwrite(
        path,
        np.zeros((3, 4, 5), dtype=np.uint8),
        photometric="rgb",
        planarconfig="separate",
    )

    metadata = TiffImageFileFormat().source_metadata(path)

    assert metadata.pixel_semantics.channel_axis == 0
    assert metadata.pixel_semantics.channel_count == 3
    assert metadata.pixel_semantics.validated_channel_axis(tifffile.imread(path)) == 0


def test_tiff_header_reuse_is_shared_by_strict_optional_and_format_instances(
    tmp_path, monkeypatch
) -> None:
    path = tmp_path / "shared.tif"
    tifffile.imwrite(path, np.zeros((3, 4, 3), dtype=np.uint8), photometric="rgb")
    original = tifffile.TiffFile
    opened = []

    def record_open(*args, **kwargs):
        opened.append(args[0])
        return original(*args, **kwargs)

    monkeypatch.setattr(tifffile, "TiffFile", record_open)
    metadata = image_file_source_metadata(path)
    for _ in range(60):
        assert require_image_file_source_metadata(path) is metadata
        assert TiffImageFileFormat().source_metadata(path) is metadata
    assert metadata.pixel_semantics.channel_axis == -1
    assert metadata.pixel_semantics.channel_count == 3
    assert opened == [path]


def test_header_reuse_detects_same_size_rewrite_with_restored_mtime(tmp_path) -> None:
    path = tmp_path / "rewrite.tif"
    tifffile.imwrite(
        path,
        np.zeros((4, 5), dtype=np.uint16),
        extratags=((281, "H", 1, 4095, False),),
    )
    before_stat = path.stat()
    before = require_image_file_source_metadata(path)
    tifffile.imwrite(
        path,
        np.zeros((4, 5), dtype=np.uint16),
        extratags=((281, "H", 1, 8191, False),),
    )
    os.utime(path, ns=(before_stat.st_atime_ns, before_stat.st_mtime_ns))
    after_stat = path.stat()
    assert after_stat.st_size == before_stat.st_size
    assert after_stat.st_mtime_ns == before_stat.st_mtime_ns
    assert after_stat.st_ctime_ns != before_stat.st_ctime_ns

    after = require_image_file_source_metadata(path)
    assert before.source_dtype == np.dtype(np.uint16)
    assert before.intensity_scale == 4095.0
    assert after.source_dtype == np.dtype(np.uint16)
    assert after.intensity_scale == 8191.0
    assert image_file_source_metadata(path) is after


def test_header_reuse_does_not_hide_deletion_or_recreation(tmp_path) -> None:
    path = tmp_path / "replace.tif"
    tifffile.imwrite(path, np.zeros((4, 5), dtype=np.uint16))
    assert require_image_file_source_metadata(path).source_dtype == np.dtype(np.uint16)
    path.unlink()
    assert image_file_source_metadata(path).source_dtype is None
    assert TiffImageFileFormat().source_metadata(path).source_dtype is None
    with pytest.raises(ValueError, match="Image source does not exist"):
        require_image_file_source_metadata(path)
    with pytest.raises(FileNotFoundError):
        TiffImageFileFormat().require_source_metadata(path)

    tifffile.imwrite(path, np.zeros((4, 5, 3), dtype=np.uint8), photometric="rgb")
    recreated = require_image_file_source_metadata(path)
    assert recreated.source_dtype == np.dtype(np.uint8)
    assert recreated.pixel_semantics.channel_count == 3


def test_header_reuse_retries_transient_failure_without_file_change(
    tmp_path, monkeypatch
) -> None:
    path = tmp_path / "retry.tif"
    tifffile.imwrite(path, np.zeros((4, 5), dtype=np.uint16))
    original = TiffImageFileFormat._read_source_metadata.__func__
    attempts = []

    def transient_reader(cls, source_path):
        attempts.append(source_path)
        if len(attempts) == 1:
            raise OSError("Transient header read failure")
        return original(cls, source_path)

    monkeypatch.setattr(
        TiffImageFileFormat, "_read_source_metadata", classmethod(transient_reader)
    )
    assert image_file_source_metadata(path).source_dtype is None
    recovered = require_image_file_source_metadata(path)
    assert recovered.source_dtype == np.dtype(np.uint16)
    assert image_file_source_metadata(path) is recovered
    assert attempts == [path, path]


def test_header_reuse_observes_changed_nominal_reader(tmp_path, monkeypatch) -> None:
    path = tmp_path / "reader.tif"
    tifffile.imwrite(path, np.zeros((4, 5), dtype=np.uint16))
    before = require_image_file_source_metadata(path)
    original = TiffImageFileFormat._read_source_metadata.__func__

    def changed_reader(cls, source_path):
        return replace(original(cls, source_path), intensity_scale=4095.0)

    monkeypatch.setattr(
        TiffImageFileFormat, "_read_source_metadata", classmethod(changed_reader)
    )
    after = require_image_file_source_metadata(path)
    assert before.intensity_scale == 65535.0
    assert after.intensity_scale == 4095.0
    assert image_file_source_metadata(path) is after


@pytest.mark.parametrize("suffix", (".npy", ".tif", ".png"))
def test_native_header_readers_use_shared_strict_revision_algorithm(tmp_path, suffix):
    path = tmp_path / f"native{suffix}"
    image = np.zeros((4, 5), dtype=np.uint8)
    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, image)
    assert (
        image_format.require_source_metadata.__func__
        is ImageFileFormat.require_source_metadata
    )
    metadata = require_image_file_source_metadata(path)
    assert metadata.source_dtype == np.dtype(np.uint8)
    assert metadata.intensity_scale == 255.0
    assert metadata.pixel_semantics.channel_axis is None
    assert image_file_source_metadata(path) is metadata


def test_numpy_optional_header_read_preserves_strict_failure_policy(tmp_path) -> None:
    path = tmp_path / "invalid.npy"
    path.write_bytes(b"not a numpy array")
    with pytest.raises(ValueError):
        image_file_source_metadata(path)
    with pytest.raises(ValueError):
        require_image_file_source_metadata(path)


def test_native_disk_serialization_unwraps_image_metadata_payload() -> None:
    image = np.array([[0.25]], dtype=np.float32)
    payload = ImageMetadataPayload(
        image,
        ImagePayloadMetadata(source_dtype="float32"),
    )

    (prepared,) = prepare_disk_image_payloads((payload,), ("out.tif",))

    assert prepared is image


def test_png_disk_serialization_unwraps_image_metadata_payload() -> None:
    image = np.array([[[0, 1024]]], dtype=np.uint16)
    payload = ImageMetadataPayload(
        image,
        ImagePayloadMetadata(source_dtype="uint16"),
    )

    (prepared,) = prepare_disk_image_payloads((payload,), ("out.png",))

    assert prepared.shape == (1, 1, 2)
    assert prepared.dtype == np.uint16


def test_png_disk_serialization_rejects_declared_unprojected_plane_axis() -> None:
    payload = ImageMetadataPayload(
        np.zeros((1, 3, 5), dtype=np.uint8),
        ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE),
    )

    with pytest.raises(ValueError, match="projected off.*runtime_slice"):
        prepare_disk_image_payloads((payload,), ("out.png",))


def test_numpy_image_format_has_explicit_registered_suffix() -> None:
    assert isinstance(
        ImageFileFormat.require_path("out.npy"),
        NumpyImageFileFormat,
    )


@pytest.mark.parametrize("path", ("out.tif", "out.tiff"))
def test_tiff_image_format_has_explicit_registered_suffixes(path) -> None:
    assert isinstance(ImageFileFormat.require_path(path), TiffImageFileFormat)


def test_png_image_format_uses_registered_png_leaf() -> None:
    assert isinstance(
        ImageFileFormat.require_path("out.png"),
        PngImageFileFormat,
    )


@pytest.mark.parametrize("path", ("out.h5", "out.hdf5", "out.unknown"))
def test_unknown_image_serialization_suffix_fails_loudly(path) -> None:
    with pytest.raises(ValueError, match="image|suffix|format"):
        ImageFileFormat.require_path(path)


@pytest.mark.parametrize("channel_axis", (None, -1, 1))
def test_intrinsic_tiff_write_uses_declared_axes_not_rgb_shaped_dimensions(
    tmp_path, channel_axis
):
    from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain

    shape = (
        (3, 4, 4)
        if channel_axis is None
        else ((3, 4, 4, 3) if channel_axis == -1 else (3, 3, 4, 4))
    )
    pixels = np.arange(np.prod(shape), dtype=np.uint16).reshape(shape)
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_channel_axis=channel_axis,
        source_spatial_domain=VolumeSourceSpatialDomain(source_depth=3),
    )
    path = tmp_path / "volume.tif"
    image_format = TiffImageFileFormat()
    image_format.write(path, metadata.payload_with(pixels))
    np.testing.assert_array_equal(image_format.read(path), pixels)
    header = image_format.require_source_metadata(path)
    assert header.source_frame_shape == ((3,) if channel_axis != 1 else None)
    assert header.pixel_semantics.channel_axis == channel_axis
    assert header.pixel_semantics.channel_count == (None if channel_axis is None else 3)
    assert header.image_shape_yx == (4, 4)


@pytest.mark.parametrize("plane_count", (1, 3, 4, 5))
@pytest.mark.parametrize("dtype", (np.uint16, np.int32))
@pytest.mark.parametrize("channel_axis", (None, -1, 1))
def test_runtime_plane_tiff_write_retains_scalar_frames_and_declared_channels(
    tmp_path, plane_count, dtype, channel_axis
):
    from polystore.config import TiffCompression, TiffConfig, TiffPhotometric
    from openhcs.processing.materialization.core import Output, RawBackendKwargs

    shape = (
        (plane_count, 5, 7) if channel_axis is None
        else ((plane_count, 5, 7, 3) if channel_axis == -1 else (plane_count, 3, 5, 7))
    )
    pixels = np.arange(np.prod(shape), dtype=dtype).reshape(shape)
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_channel_axis=channel_axis,
    )
    path = tmp_path / "artifact.labels.tif"
    configured = TiffConfig(compression=TiffCompression.DEFLATE, compression_level=1)
    (batch, kwargs), = RawBackendKwargs(tiff_config=configured).filemanager_batches(
        (Output(str(path), pixels, metadata),)
    )
    assert len(batch) == 1 and batch[0].content is pixels
    config = kwargs['tiff_config']
    assert config.compression is TiffCompression.DEFLATE
    assert config.compression_level == 1
    assert config.photometric is (TiffPhotometric.MINISBLACK if channel_axis is None else TiffPhotometric.RGB)
    assert config.axes == ('QYX' if channel_axis is None else ('QYXS' if channel_axis == -1 else 'QSYX'))
    tifffile.imwrite(path, pixels, **config.tifffile_write_kwargs())
    np.testing.assert_array_equal(tifffile.imread(path), pixels)
    with tifffile.TiffFile(path) as tif:
        assert tif.series[0].axes == config.axes
        assert len(tif.pages) == plane_count
        assert tif.pages[0].samplesperpixel == (1 if channel_axis is None else 3)
    header = TiffImageFileFormat().require_source_metadata(path)
    assert header.pixel_semantics.channel_axis == channel_axis
    assert header.pixel_semantics.channel_count == (None if channel_axis is None else 3)
    assert header.image_shape_yx == (5, 7)


def test_runtime_plane_tiff_rejects_undeclared_extra_payload_axis(tmp_path):
    metadata = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE)
    with pytest.raises(ValueError, match='declared plane'):
        TiffImageFileFormat().write(
            tmp_path / 'invalid.tif', metadata.payload_with(np.zeros((4, 5, 7, 2)))
        )
