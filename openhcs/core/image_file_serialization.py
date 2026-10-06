"""Nominal image-file formats for source metadata and disk serialization."""

from __future__ import annotations

import logging
from abc import abstractmethod
from dataclasses import dataclass, replace
from functools import lru_cache
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable, ClassVar, Sequence

import numpy as np
from arraybridge import MemoryType, detect_memory_type
from metaclass_registry import AutoRegisterMeta
from polystore.config import TiffConfig, TiffPhotometric, TiffPlanarConfig

from openhcs.constants.constants import FileFormat
from openhcs.core.callable_contract import CompilerPreparedAutoRegisterFamily
from openhcs.core.image_quantization_numba import quantize_image_uint8
from openhcs.core.registry_strategies import NominalTypeStrategyFamilyMixin
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_intensity_scale_for_dtype,
    image_payload_data,
    image_payload_metadata,
)

if TYPE_CHECKING:
    from openhcs.core.processing_preparation import PreparationOperation

logger = logging.getLogger(__name__)


@dataclass(frozen=True, slots=True)
class SourceImagePixelSemantics:
    """Channel layout declared by an image-file format."""

    channel_axis: int | None = None
    channel_count: int | None = None

    def __post_init__(self) -> None:
        if (self.channel_axis is None) != (self.channel_count is None):
            raise ValueError(
                "Source image pixel channel axis and count must be declared together."
            )
        if self.channel_count is not None and self.channel_count <= 1:
            raise ValueError(
                "Source image pixel channel count must exceed one when declared."
            )

    def validated_channel_axis(self, payload: Any) -> int | None:
        """Validate loaded pixels against this format-owned declaration."""
        axis = self.channel_axis
        if axis is None:
            return None
        shape = tuple(int(value) for value in np.shape(image_payload_data(payload)))
        return self._validated_channel_axis_for_shape(axis, shape)

    def image_shape_yx_for_shape(
        self,
        shape: tuple[int, ...],
    ) -> tuple[int, int] | None:
        """Project format-declared channel bands without inferring image axes."""

        axis = self.channel_axis
        if axis is not None:
            self._validated_channel_axis_for_shape(axis, shape)
            normalized = axis if axis >= 0 else len(shape) + axis
            shape = shape[:normalized] + shape[normalized + 1 :]
        return shape if len(shape) == 2 else None

    def _validated_channel_axis_for_shape(
        self,
        axis: int,
        shape: tuple[int, ...],
    ) -> int:
        normalized = axis if axis >= 0 else len(shape) + axis
        if normalized < 0 or normalized >= len(shape):
            raise ValueError(
                f"Declared source pixel channel axis {axis} is invalid for loaded "
                f"payload shape {shape!r}."
            )
        if shape[normalized] != self.channel_count:
            raise ValueError(
                "Loaded payload conflicts with declared source pixel semantics: "
                f"axis {axis} carries {shape[normalized]} channel values, expected "
                f"{self.channel_count}."
            )
        return axis


@dataclass(frozen=True, slots=True)
class ImageFileSourceMetadata:
    """Source metadata read through one registered image-file format."""

    source_dtype: Any | None = None
    intensity_scale: float | None = None
    pixel_semantics: SourceImagePixelSemantics = SourceImagePixelSemantics()
    image_shape_yx: tuple[int, int] | None = None
    source_frame_shape: tuple[int, ...] | None = ()

    def __post_init__(self) -> None:
        if self.image_shape_yx is not None:
            if len(self.image_shape_yx) != 2 or any(
                not isinstance(value, int) or isinstance(value, bool) or value <= 0
                for value in self.image_shape_yx
            ):
                raise ValueError(
                    "Image-file YX shape requires two positive integer dimensions."
                )
            object.__setattr__(self, "image_shape_yx", tuple(self.image_shape_yx))
        if self.source_frame_shape is not None:
            if any(
                not isinstance(value, int) or isinstance(value, bool) or value <= 0
                for value in self.source_frame_shape
            ):
                raise ValueError(
                    "Image-file frame shape requires positive integer dimensions."
                )
            object.__setattr__(
                self, "source_frame_shape", tuple(self.source_frame_shape)
            )

    def frame_for_source_indices(self, indices: tuple[int, ...]) -> int:
        """Map explicitly selected leading source axes to a container frame."""

        if not indices:
            return 0
        if self.source_frame_shape is None or len(indices) != len(
            self.source_frame_shape
        ):
            raise ValueError(
                "Source selection has no declared complete container-frame mapping."
            )
        frame = 0
        for index, size in zip(indices, self.source_frame_shape, strict=True):
            if (
                not isinstance(index, int)
                or isinstance(index, bool)
                or not 0 <= index < size
            ):
                raise ValueError(
                    f"Source frame index {index!r} is outside dimension {size}."
                )
            frame = frame * size + index
        return frame

    def require_image_geometry(self) -> tuple[Any, int, int]:
        """Require complete format-declared dtype and physical image dimensions."""

        if self.image_shape_yx is None or self.source_dtype is None:
            raise ValueError("Image-file header does not declare image dtype and YX geometry.")
        height, width = self.image_shape_yx
        return self.source_dtype, height, width

    def project_image_metadata(
        self, metadata: ImagePayloadMetadata, *, values_preserved: bool
    ) -> ImagePayloadMetadata:
        """Combine current native pixels with retained typed acquisition facts."""
        if self.source_dtype is None:
            raise ValueError("Saved image metadata requires an actual native dtype.")
        native_scale_governs = self.intensity_scale is not None or not values_preserved
        if not values_preserved:
            metadata = metadata.replace_fields(
                unit_interval_intensity=None,
                physical_border_edges_yx=None,
                mask_defines_border=None,
            )
        return metadata.replace_fields(
            source_dtype=str(self.source_dtype),
            intensity_scale=(
                self.intensity_scale
                if native_scale_governs
                else metadata.intensity_scale
            ),
            source_plane_dtypes=tuple(
                str(self.source_dtype) for _ in metadata.source_plane_dtypes
            ),
            source_plane_intensity_scales=(
                tuple(
                    self.intensity_scale for _ in metadata.source_plane_intensity_scales
                )
                if native_scale_governs
                else metadata.source_plane_intensity_scales
            ),
            source_channel_axis=(
                metadata.source_channel_axis
                if values_preserved and self.pixel_semantics.channel_axis is None
                else self.pixel_semantics.channel_axis
            ),
        )


@dataclass(frozen=True, slots=True)
class ImageFileRevision:
    """Physical file identity and timestamps determining header reuse."""

    path: Path
    device: int
    inode: int
    size: int
    modified_ns: int
    changed_ns: int

    @classmethod
    def from_path(cls, path: Path) -> "ImageFileRevision":
        stat = path.stat()
        return cls(
            path=path,
            device=stat.st_dev,
            inode=stat.st_ino,
            size=stat.st_size,
            modified_ns=stat.st_mtime_ns,
            changed_ns=stat.st_ctime_ns,
        )


class ImageFileFormat(CompilerPreparedAutoRegisterFamily, metaclass=AutoRegisterMeta):
    """Nominal owner of image-file source and serialization semantics."""

    __registry_key__ = "format_key"
    __skip_if_no_key__ = True
    format_key: ClassVar[str | None] = None
    suffixes: ClassVar[tuple[str, ...]] = ()
    browser_file_format: ClassVar[FileFormat] = FileFormat.TIFF

    @classmethod
    def cache_preparation_operations(cls) -> tuple[PreparationOperation, ...]:
        """Derive serialization substrates from the pixel-conversion owner."""
        return ImagePayloadUint8Strategy.cache_preparation_operations()

    @classmethod
    def prepare_registered_family(cls) -> None:
        for operation in cls.cache_preparation_operations():
            operation.prepare()

    @classmethod
    def matches_path(cls, path: str | Path) -> bool:
        """Return whether this exact nominal format owns ``path``."""
        return Path(path).suffix.lower() in cls.suffixes

    @classmethod
    def is_image_path(cls, path: str | Path) -> bool:
        """Return whether one registered image format exactly owns ``path``."""
        return any(
            format_type.matches_path(path) for format_type in cls.__registry__.values()
        )

    @classmethod
    def require_path(cls, path: str | Path) -> "ImageFileFormat":
        matches = tuple(
            format_type
            for format_type in cls.__registry__.values()
            if format_type.matches_path(path)
        )
        if len(matches) == 1:
            return matches[0]()
        suffix = Path(path).suffix.lower()
        if len(matches) > 1:
            raise ValueError(
                "Multiple image serialization formats are registered for suffix "
                f"{suffix!r}: {tuple(item.__name__ for item in matches)!r}."
            )
        raise ValueError(
            f"No image serialization format is registered for suffix {suffix!r}."
        )

    def prepare(self, payload: Any) -> Any:
        """Project runtime pixels onto the host before format-specific encoding."""
        pixels = image_payload_data(payload)
        host_pixels = MemoryType(detect_memory_type(pixels)).to_numpy(pixels)
        host_payload = image_payload_metadata(payload).payload_with(host_pixels)
        return self.prepare_host_payload(host_payload)

    @abstractmethod
    def prepare_host_payload(self, payload: Any) -> Any:
        """Encode host pixels while respecting this format's image semantics."""

    def storage_config(
        self, payload: Any, configured: TiffConfig | None
    ) -> TiffConfig | None:
        """Non-TIFF formats retain their existing backend writer configuration."""
        return None

    @classmethod
    def storage_write_batches(
        cls,
        payloads: Sequence[Any],
        paths: Sequence[str | Path],
        configured: TiffConfig | None,
    ) -> tuple[tuple[tuple[int, ...], TiffConfig | None], ...]:
        """Batch compatible declared image codecs without changing output order."""
        if len(payloads) != len(paths):
            raise ValueError("Image storage payload/path cardinality mismatch.")
        batches = []
        for index, (payload, path) in enumerate(zip(payloads, paths, strict=True)):
            config = (
                cls.require_path(path).storage_config(
                    payload,
                    (
                        configured
                        if configured is not None and configured.applies_to_path(path)
                        else None
                    ),
                )
                if cls.is_image_path(path)
                else None
            )
            if batches and batches[-1][1] == config:
                batches[-1][0].append(index)
            else:
                batches.append(([index], config))
        return tuple((tuple(indices), config) for indices, config in batches)

    def read(self, path: str | Path) -> np.ndarray:
        """Read pixels through this exact registered image-file format."""
        import imageio.v3 as iio

        return np.asarray(iio.imread(path))

    def write(self, path: str | Path, payload: Any) -> None:
        """Write pixels through this exact registered image-file format."""
        import imageio.v3 as iio

        iio.imwrite(path, self.prepare(payload))

    def source_metadata(self, path: Path) -> ImageFileSourceMetadata:
        """Read format-owned source metadata without loading pixel data."""
        try:
            return self.require_source_metadata(path)
        except Exception:
            logger.debug("Could not read image metadata for %s.", path, exc_info=True)
            return ImageFileSourceMetadata()

    def require_source_metadata(self, path: Path) -> ImageFileSourceMetadata:
        """Read or reuse complete header facts for the current file revision."""

        return self._source_metadata_for_revision(
            ImageFileRevision.from_path(path),
            self._read_source_metadata,
        )

    @staticmethod
    @lru_cache(maxsize=4096)
    def _source_metadata_for_revision(
        revision: ImageFileRevision,
        reader: Callable[[Path], ImageFileSourceMetadata],
    ) -> ImageFileSourceMetadata:
        """Cache successful immutable headers; exceptions retain read semantics."""

        return reader(revision.path)

    @classmethod
    def _read_source_metadata(cls, path: Path) -> ImageFileSourceMetadata:
        """Read complete format-owned header metadata or fail closed."""

        import imageio.v3 as iio

        properties = iio.improps(path)
        dtype = properties.dtype
        pixel_semantics = cls.require_pixel_semantics(path)
        shape = tuple(properties.shape)
        return ImageFileSourceMetadata(
            source_dtype=dtype,
            intensity_scale=(
                cls.declared_intensity_scale(path)
                or image_intensity_scale_for_dtype(dtype)
            ),
            pixel_semantics=pixel_semantics,
            image_shape_yx=pixel_semantics.image_shape_yx_for_shape(
                tuple(int(value) for value in shape)
            ),
        )

    def preserves_pixel_values(self, source_dtype: Any) -> bool:
        """Whether serialization retains authored pixel-value proofs."""
        del source_dtype
        return False

    def persisted_metadata(self, path: Path, payload: Any) -> ImagePayloadMetadata:
        """Describe saved native pixels while retaining their semantic lineage."""
        header = self.source_metadata(path)
        if header.source_dtype is None:
            raise ValueError(f"Cannot establish saved image metadata for {path}.")
        return header.project_image_metadata(
            image_payload_metadata(payload),
            values_preserved=self.preserves_pixel_values(
                image_payload_data(payload).dtype
            ),
        )

    def requires_plane_store_decoder(self, path: Path) -> bool:
        """Return whether embedded metadata requires a richer plane decoder."""
        del path
        return False

    @classmethod
    def declared_intensity_scale(cls, path: Path) -> float | None:
        """Return a container-declared intensity scale when the format has one."""
        del path
        return None

    def pixel_semantics(self, path: Path) -> SourceImagePixelSemantics:
        """Return explicit channel-band semantics exposed by the file container."""
        try:
            return self.require_pixel_semantics(path)
        except Exception:
            logger.debug(
                "Could not read source pixel-band metadata for %s.",
                path,
                exc_info=True,
            )
            return SourceImagePixelSemantics()

    @classmethod
    def require_pixel_semantics(cls, path: Path) -> SourceImagePixelSemantics:
        """Read complete pixel-band header semantics or fail closed."""

        from PIL import Image

        with Image.open(path) as image:
            band_count = len(image.getbands())
        if band_count <= 1:
            return SourceImagePixelSemantics()
        return SourceImagePixelSemantics(channel_axis=-1, channel_count=band_count)


class NumpyImageFileFormat(ImageFileFormat):
    """NumPy array files preserve the payload dtype directly."""

    format_key = "numpy"
    suffixes = (".npy",)
    browser_file_format = FileFormat.NUMPY

    def preserves_pixel_values(self, source_dtype: Any) -> bool:
        del source_dtype
        return True

    def prepare_host_payload(self, payload: Any) -> Any:
        return image_payload_data(payload)

    def read(self, path: str | Path) -> np.ndarray:
        return np.asarray(np.load(path, allow_pickle=False))

    def write(self, path: str | Path, payload: Any) -> None:
        np.save(path, self.prepare(payload), allow_pickle=False)

    def source_metadata(self, path: Path) -> ImageFileSourceMetadata:
        """NumPy source reads retain their strict failure policy."""

        return self.require_source_metadata(path)

    @classmethod
    def _read_source_metadata(cls, path: Path) -> ImageFileSourceMetadata:
        array = np.load(path, mmap_mode="r", allow_pickle=False)
        return ImageFileSourceMetadata(
            source_dtype=array.dtype,
            intensity_scale=image_intensity_scale_for_dtype(array.dtype),
            image_shape_yx=tuple(array.shape) if array.ndim == 2 else None,
            source_frame_shape=() if array.ndim == 2 else None,
        )


class TiffImageFileFormat(ImageFileFormat):
    """TIFF preserves dtype and may declare a physical maximum sample value."""

    format_key = "tiff"
    suffixes = (".tif", ".tiff")

    def preserves_pixel_values(self, source_dtype: Any) -> bool:
        del source_dtype
        return True

    def prepare_host_payload(self, payload: Any) -> Any:
        return image_payload_data(payload)

    def storage_config(
        self, payload: Any, configured: TiffConfig | None
    ) -> TiffConfig | None:
        metadata = image_payload_metadata(payload)
        if metadata.persists_whole_image():
            axes = list("ZYX")
        elif metadata.plane_axis is not None:
            # Q is a container frame, not a guessed physical Z/channel axis.
            # Its exact OpenHCS component domain remains in source projection.
            axes = list("QYX")
        else:
            return configured
        data = image_payload_data(payload)
        channel_axis = metadata.normalized_source_channel_axis(data)
        planarconfig = None
        photometric = TiffPhotometric.MINISBLACK
        if channel_axis is not None:
            if channel_axis < 0:
                channel_axis += data.ndim
            if channel_axis not in (data.ndim - 1, data.ndim - 3):
                raise ValueError(
                    "Intrinsic TIFF channels must be contiguous or planar before Y/X."
                )
            axes.insert(channel_axis, "S")
            planarconfig = (
                TiffPlanarConfig.CONTIG
                if channel_axis == data.ndim - 1
                else TiffPlanarConfig.SEPARATE
            )
            photometric = TiffPhotometric.RGB
        if len(axes) != data.ndim:
            raise ValueError(
                "TIFF pixels must retain exactly their declared plane, Y/X and channel axes."
            )
        return replace(
            configured if configured is not None else TiffConfig(),
            photometric=photometric,
            axes="".join(axes),
            planarconfig=planarconfig,
        )

    def write(self, path: str | Path, payload: Any) -> None:
        config = self.storage_config(payload, None)
        if config is None:
            return super().write(path, payload)
        import tifffile

        tifffile.imwrite(path, self.prepare(payload), **config.tifffile_write_kwargs())

    def requires_plane_store_decoder(self, path: Path) -> bool:
        import tifffile

        with tifffile.TiffFile(path) as tif:
            return bool(tif.is_ome)

    @classmethod
    def _read_source_metadata(cls, path: Path) -> ImageFileSourceMetadata:
        """Read complete TIFF header semantics through one container context."""

        import tifffile

        tif = tifffile.TiffFile(path)
        with tif:
            series = tif.series[0]
            dtype = series.dtype
            declared_scale = cls._declared_intensity_scale_from_page(tif.pages[0])
            image_shape_yx = (
                int(tif.pages[0].imagelength),
                int(tif.pages[0].imagewidth),
            )
            spatial_axis = series.axes.find("Y")
            frame_shape = tuple(int(value) for value in series.shape[:spatial_axis])
            if (
                spatial_axis < 0
                or "S" in series.axes[:spatial_axis]
                or len(series.pages) != np.prod(frame_shape)
            ):
                frame_shape = None
            sample_axis = series.axes.find("S")
            sample_count = int(series.shape[sample_axis]) if sample_axis >= 0 else None
            pixel_semantics = SourceImagePixelSemantics()
            if sample_count is not None and sample_count > 1:
                pixel_semantics = SourceImagePixelSemantics(
                    channel_axis=(
                        -1 if sample_axis == len(series.shape) - 1 else sample_axis
                    ),
                    channel_count=sample_count,
                )
        return ImageFileSourceMetadata(
            source_dtype=dtype,
            intensity_scale=(declared_scale or image_intensity_scale_for_dtype(dtype)),
            pixel_semantics=pixel_semantics,
            image_shape_yx=image_shape_yx,
            source_frame_shape=frame_shape,
        )

    @classmethod
    def declared_intensity_scale(cls, path: Path) -> float | None:
        import tifffile

        with tifffile.TiffFile(path) as tif:
            return cls._declared_intensity_scale_from_page(tif.pages[0])

    @staticmethod
    def _declared_intensity_scale_from_page(page: Any) -> float | None:
        tag = page.tags.get("SMaxSampleValue") or page.tags.get("MaxSampleValue")
        if tag is None:
            return None
        value = tag.value
        scale_value = value[0] if isinstance(value, (tuple, list)) else value
        if not isinstance(scale_value, (int, float, np.integer, np.floating)):
            return None
        scale = float(scale_value)
        return scale if scale > 0 else None


class EightBitRasterImageFileFormat(ImageFileFormat):
    """Raster formats that require 8-bit file-compatible image arrays."""

    format_key = None
    suffixes = ()

    def prepare_host_payload(self, payload: Any) -> Any:
        return image_payload_as_uint8(require_single_image_payload(payload))

    def preserves_pixel_values(self, source_dtype: Any) -> bool:
        del source_dtype
        return False


class BmpImageFileFormat(EightBitRasterImageFileFormat):
    format_key = "bmp"
    suffixes = (".bmp",)

    def preserves_pixel_values(self, source_dtype: Any) -> bool:
        return np.dtype(source_dtype) == np.dtype(np.uint8)


class GifImageFileFormat(EightBitRasterImageFileFormat):
    """Palette conversion has no general exact-pixel preservation proof."""

    format_key = "gif"
    suffixes = (".gif",)


class JpegImageFileFormat(EightBitRasterImageFileFormat):
    """Lossy compression invalidates authored exact-value and border proofs."""

    format_key = "jpeg"
    suffixes = (".jpeg", ".jpg")


class PngImageFileFormat(ImageFileFormat):
    """PNG preserves uint8/uint16 images but cannot encode float image modes."""

    format_key = "png"
    suffixes = (".png",)

    def prepare_host_payload(self, payload: Any) -> Any:
        array = require_single_image_payload(payload)
        if array.dtype == np.uint8 or array.dtype == np.uint16:
            return array
        return image_payload_as_uint8(array)

    def preserves_pixel_values(self, source_dtype: Any) -> bool:
        return np.dtype(source_dtype) in (np.dtype(np.uint8), np.dtype(np.uint16))


class ImagePayloadUint8Strategy(
    NominalTypeStrategyFamilyMixin,
    CompilerPreparedAutoRegisterFamily,
    metaclass=AutoRegisterMeta,
):
    """Nominal family for dtype-specific uint8 image conversion."""

    @classmethod
    def prepare_registered_family(cls) -> None:
        for strategy in cls.registered_strategy_types():
            strategy.prepare_substrate()

    @classmethod
    def prepare_substrate(cls) -> None:
        """Native NumPy conversions require no compiled numerical substrate."""

    @classmethod
    def for_dtype(cls, dtype: Any) -> "ImagePayloadUint8Strategy":
        normalized = np.dtype(dtype)
        strategy_types = cls.strategy_types_for_nominal_type(normalized.type)
        if strategy_types:
            return strategy_types[0]()
        raise TypeError(f"No uint8 conversion is registered for dtype {normalized!r}.")

    @abstractmethod
    def prepare(self, array: np.ndarray) -> np.ndarray:
        """Return a uint8-compatible image array."""


class NativeUint8ImagePayloadStrategy(ImagePayloadUint8Strategy):
    """Uint8 arrays are already compatible with 8-bit raster formats."""

    value_type = np.uint8

    def prepare(self, array: np.ndarray) -> np.ndarray:
        return array


class BoolImagePayloadUint8Strategy(ImagePayloadUint8Strategy):
    """Boolean masks serialize as black/white 8-bit images."""

    value_type = np.bool_

    def prepare(self, array: np.ndarray) -> np.ndarray:
        return array.astype(np.uint8) * np.uint8(255)


class NumericImagePayloadUint8Strategy(ImagePayloadUint8Strategy):
    """Numeric images serialize through explicit clipping/scaling semantics."""

    value_type = np.number

    def prepare(self, array: np.ndarray) -> np.ndarray:
        values = _uint8_conversion_values(array)
        scale = _is_unit_interval(values)
        # Own the working pixels before reusing them through each conversion phase.
        working = values.copy(order="K") if values.dtype == array.dtype else values
        if scale:
            np.multiply(working, _scale_value(working, 255.0), out=working)
        np.nan_to_num(working, copy=False, nan=0.0, posinf=255.0, neginf=0.0)
        np.clip(working, 0.0, 255.0, out=working)
        np.rint(working, out=working)
        return working.astype(np.uint8)


class CompiledFloatImagePayloadUint8Strategy(NumericImagePayloadUint8Strategy):
    """Quantize plain NumPy pixels without floating working-pixel copies.

    The public payload conversion admits NumPy pixels with ``np.asarray``.
    Direct ``NumericImagePayloadUint8Strategy.prepare`` calls retain their NumPy
    hook behavior. Dtype-specific extensions replace the corresponding leaf in
    the existing nominal registry.
    """

    value_type = None
    value_type_label = None

    @classmethod
    def prepare_substrate(cls) -> None:
        scalar_type = cls.value_type
        for writeable in (True, False):
            values = np.asarray((0.0, 0.5, 1.0), dtype=scalar_type)
            values.flags.writeable = writeable
            quantize_image_uint8(
                values, np.empty(values.shape, dtype=np.uint8), scalar_type(255.0)
            )

    def prepare(self, array: np.ndarray) -> np.ndarray:
        # Normalize byte order only when demanded by the typed kernel ABI.
        values = np.asarray(array, dtype=array.dtype.type).ravel(order="K")
        output = np.empty_like(array, dtype=np.uint8, order="K")
        quantize_image_uint8(values, output.ravel(order="K"), array.dtype.type(255.0))
        return output


class Float32ImagePayloadUint8Strategy(CompiledFloatImagePayloadUint8Strategy):
    value_type = np.float32


class Float64ImagePayloadUint8Strategy(CompiledFloatImagePayloadUint8Strategy):
    value_type = np.float64


def image_file_source_metadata(path: Path | None) -> ImageFileSourceMetadata:
    """Return source metadata through the exact registered file format."""
    if path is None or not path.exists() or not ImageFileFormat.is_image_path(path):
        return ImageFileSourceMetadata()
    return ImageFileFormat.require_path(path).source_metadata(path)


def require_image_file_source_metadata(path: Path) -> ImageFileSourceMetadata:
    """Return strict header metadata from the one registered format owner."""

    image_format = ImageFileFormat.require_path(path)
    if not path.exists():
        raise ValueError(f"Image source does not exist: {path}.")
    return image_format.require_source_metadata(path)


def prepare_disk_image_payloads(
    payloads: Sequence[Any],
    paths: Sequence[str | Path],
) -> list[Any]:
    """Prepare image payloads for disk paths without changing runtime values."""
    if len(payloads) != len(paths):
        raise ValueError(
            "Image payload/path length mismatch: "
            f"{len(payloads)} payloads for {len(paths)} paths."
        )
    return [
        ImageFileFormat.require_path(path).prepare(payload)
        for payload, path in zip(payloads, paths)
    ]


def image_payload_as_uint8(payload: Any) -> np.ndarray:
    """Convert numeric image payloads to uint8 using explicit file semantics."""
    array = np.asarray(image_payload_data(payload))
    return ImagePayloadUint8Strategy.for_dtype(array.dtype).prepare(array)


def require_single_image_payload(payload: Any) -> np.ndarray:
    """Return pixels only when no runtime plane axis remains to project."""
    plane_axis = image_payload_metadata(payload).plane_axis
    if plane_axis is not None:
        raise ValueError(
            "Single-image raster serialization requires a payload projected off "
            f"its declared {plane_axis.value!r} plane axis."
        )
    return np.asarray(image_payload_data(payload))


def _is_unit_interval(values: np.ndarray) -> bool:
    finite_values = values[np.isfinite(values)]
    if finite_values.size == 0:
        return True
    return float(finite_values.min()) >= 0.0 and float(finite_values.max()) <= 1.0


def _uint8_conversion_values(array: np.ndarray) -> np.ndarray:
    if np.issubdtype(array.dtype, np.floating):
        return array.astype(array.dtype, copy=False)
    return array.astype(np.float64, copy=False)


def _scale_value(values: np.ndarray, value: float) -> Any:
    if np.issubdtype(values.dtype, np.floating):
        return values.dtype.type(value)
    return value
