"""Nominal viewer control-message values."""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass, field
from enum import Enum
from math import floor, isfinite
from numbers import Real
from typing import TYPE_CHECKING, ClassVar, Self, TypeAlias, TypeVar

from polystore.streaming.identity import StreamProducerIdentity
from zmqruntime.viewer_protocol import (
    ViewerNativeLayerTransform,
    ViewerSourceSpatialDomainPayload,
)
from openhcs.core.source_metadata import SourceVoxelSpacing

if TYPE_CHECKING:
    import numpy as np
    from openhcs.core.runtime_image_values import ImagePayloadMetadata

from zmqruntime.viewer_protocol import ViewerWireField

from openhcs.constants import AllComponents

ViewerScalar: TypeAlias = str | int | float | bool | None
VerticesYX: TypeAlias = tuple[tuple[float, float], ...]
ViewerPayloadAxisIndices: TypeAlias = tuple[int, ...] | dict[str, int]
ViewerShapePayloadValueT = TypeVar("ViewerShapePayloadValueT")


class ViewerShapePayloadProjection(str, Enum):
    """Declared shape-payload detail retained by a viewer projection."""

    projected_fields: tuple[ViewerWireField, ...] | None

    FULL = ("full", None)
    SUMMARY = (
        "summary",
        (ViewerWireField.TYPE, ViewerWireField.METADATA),
    )

    def __new__(
        cls,
        value: str,
        projected_fields: tuple[ViewerWireField, ...] | None,
    ) -> "ViewerShapePayloadProjection":
        member = str.__new__(cls, value)
        member._value_ = value
        member.projected_fields = projected_fields
        return member

    def selected_items(
        self,
        payload: Mapping[object, ViewerShapePayloadValueT],
    ) -> tuple[tuple[object, ViewerShapePayloadValueT], ...]:
        if self.projected_fields is None:
            return tuple(payload.items())
        return tuple(
            (field.value, payload[field.value])
            for field in self.projected_fields
            if field.value in payload
        )


class ViewerResultElementCoordinateAuthority:
    """Derive a selected element's slice from its native N-D coordinates."""

    @classmethod
    def axis_indices(
        cls,
        *,
        coordinates: Iterable[object],
        axis_labels: Sequence[str],
        displayed_axis_indices: Sequence[int],
    ) -> dict[str, int]:
        """Return exact route-local indices for every non-displayed axis."""

        displayed = tuple(displayed_axis_indices)
        if any(
            isinstance(axis, bool) or not isinstance(axis, int) for axis in displayed
        ):
            raise TypeError("Viewer displayed_axis_indices must contain integers.")
        if not displayed or len(set(displayed)) != len(displayed):
            raise ValueError(
                "Viewer displayed_axis_indices must be nonempty and unique."
            )

        labels = tuple(axis_labels)
        if any(not isinstance(label, str) or not label for label in labels):
            raise ValueError("Viewer axis_labels must contain non-empty strings.")
        if len(set(labels)) != len(labels):
            raise ValueError("Viewer axis_labels must be unique.")

        rows = cls._coordinate_rows(coordinates)
        coordinate_width = len(rows[0])
        if any(len(row) != coordinate_width for row in rows):
            raise ValueError(
                "Viewer result element coordinates must have a consistent width."
            )
        if coordinate_width != len(labels):
            raise ValueError(
                "Viewer result element coordinate width must match its axis labels: "
                f"{coordinate_width} != {len(labels)}."
            )
        if any(axis < 0 or axis >= coordinate_width for axis in displayed):
            raise ValueError(
                "Viewer displayed_axis_indices are outside the result coordinate width."
            )

        return {
            labels[axis_position]: cls._slice_index(
                rows,
                axis_position=axis_position,
                axis_label=labels[axis_position],
            )
            for axis_position in range(coordinate_width)
            if axis_position not in displayed
        }

    @classmethod
    def _coordinate_rows(
        cls,
        coordinates: Iterable[object],
    ) -> tuple[tuple[object, ...], ...]:
        if isinstance(coordinates, (str, bytes)):
            raise TypeError("Viewer result element coordinates must be numeric.")
        values = tuple(coordinates)
        if not values:
            raise ValueError("Viewer result element coordinates must not be empty.")
        if all(cls._is_coordinate_scalar(value) for value in values):
            return (values,)

        rows: list[tuple[object, ...]] = []
        for value in values:
            if isinstance(value, (str, bytes)) or not isinstance(value, Iterable):
                raise TypeError(
                    "Viewer result element coordinates must be one coordinate "
                    "or a sequence of coordinate rows."
                )
            row = tuple(value)
            if not row:
                raise ValueError(
                    "Viewer result element coordinate rows must not be empty."
                )
            if not all(cls._is_coordinate_scalar(item) for item in row):
                raise TypeError("Viewer result element coordinates must be numeric.")
            rows.append(row)
        return tuple(rows)

    @staticmethod
    def _is_coordinate_scalar(value: object) -> bool:
        return not isinstance(value, bool) and isinstance(value, Real)

    @classmethod
    def _slice_index(
        cls,
        rows: tuple[tuple[object, ...], ...],
        *,
        axis_position: int,
        axis_label: str,
    ) -> int:
        coordinates = tuple(
            cls._slice_coordinate(
                row[axis_position],
                axis_label=axis_label,
            )
            for row in rows
        )
        if len(set(coordinates)) != 1:
            raise ValueError(
                f"Viewer result element spans multiple {axis_label!r} slices: "
                f"{coordinates!r}."
            )
        return coordinates[0]

    @staticmethod
    def _slice_coordinate(value: object, *, axis_label: str) -> int:
        if isinstance(value, bool) or not isinstance(value, Real):
            raise TypeError(
                f"Viewer result element coordinate for axis {axis_label!r} "
                "must be numeric."
            )
        numeric_value = float(value)
        if not isfinite(numeric_value) or not numeric_value.is_integer():
            raise ValueError(
                f"Viewer result element coordinate for axis {axis_label!r} "
                f"must identify one integral slice, got {value!r}."
            )
        return int(numeric_value)


class ViewerFractionalZPointCoordinateAuthority(ViewerResultElementCoordinateAuthority):
    """Navigate to the nearest Z slice without rounding stored point geometry."""

    @staticmethod
    def _slice_coordinate(value: object, *, axis_label: str) -> int:
        if axis_label != AllComponents.Z_INDEX.value:
            return ViewerResultElementCoordinateAuthority._slice_coordinate(
                value, axis_label=axis_label
            )
        if isinstance(value, bool) or not isinstance(value, Real):
            raise TypeError("Viewer point Z coordinate must be numeric.")
        numeric_value = float(value)
        if not isfinite(numeric_value):
            raise ValueError("Viewer point Z coordinate must be finite.")
        return floor(numeric_value + 0.5)


@dataclass(frozen=True, slots=True)
class ViewerNativeDimensions:
    """Actual native readback; canvas_size is logical Qt (width, height)."""

    order: tuple[int, ...]
    ndisplay: int
    displayed_axes: tuple[str, ...]
    point: tuple[float, ...]
    camera_angles: tuple[float, float, float]
    canvas_size: tuple[int, int] | None

    def to_wire_mapping(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerPayloadControlOptions:
    """Caller-declared payload selection and inspection controls."""

    route_key: str | None = None
    axis_indices: ViewerPayloadAxisIndices | None = None
    include_array_values: bool = False
    max_array_elements: int = 4096
    array_slices: tuple[tuple[int, int], ...] | None = None
    include_shape_payloads: bool = True
    max_shape_payloads: int = 256

    def sample_axis_indices(
        self,
        data: np.ndarray,
        image_metadata: ImagePayloadMetadata | None,
        source_data: np.ndarray,
        removed_leading_axes: int,
    ) -> tuple[int, ...]:
        """Raw array slices retain their existing trailing-dimension contract."""
        return tuple(range(data.ndim - len(self.array_slices), data.ndim))

    def __post_init__(self) -> None:
        if self.route_key is not None and (
            not isinstance(self.route_key, str) or not self.route_key
        ):
            raise ValueError("Viewer payload route_key must be a non-empty string.")
        if self.axis_indices is not None:
            self._validate_axis_indices(self.axis_indices)
        if not isinstance(self.include_array_values, bool):
            raise TypeError("Viewer payload include_array_values must be a bool.")
        self._validate_nonnegative_int(
            self.max_array_elements,
            "max_array_elements",
        )
        if self.array_slices is not None:
            self._validate_array_slices(self.array_slices)
        if not isinstance(self.include_shape_payloads, bool):
            raise TypeError("Viewer payload include_shape_payloads must be a bool.")
        self._validate_nonnegative_int(
            self.max_shape_payloads,
            "max_shape_payloads",
        )

    @classmethod
    def from_overrides(
        cls,
        *,
        route_key: str | None = None,
        axis_indices: tuple[int, ...] | Mapping[str, int] | None = None,
        include_array_values: bool | None = None,
        max_array_elements: int | None = None,
        array_slices: tuple[tuple[int, int], ...] | None = None,
        include_shape_payloads: bool | None = None,
        max_shape_payloads: int | None = None,
    ) -> Self:
        defaults = cls(array_slices=array_slices)
        return cls(
            route_key=route_key,
            axis_indices=(
                dict(axis_indices)
                if isinstance(axis_indices, Mapping)
                else axis_indices
            ),
            include_array_values=(
                defaults.include_array_values
                if include_array_values is None
                else include_array_values
            ),
            max_array_elements=(
                defaults.max_array_elements
                if max_array_elements is None
                else max_array_elements
            ),
            array_slices=array_slices,
            include_shape_payloads=(
                defaults.include_shape_payloads
                if include_shape_payloads is None
                else include_shape_payloads
            ),
            max_shape_payloads=(
                defaults.max_shape_payloads
                if max_shape_payloads is None
                else max_shape_payloads
            ),
        )

    @staticmethod
    def _validate_axis_indices(value: ViewerPayloadAxisIndices) -> None:
        if isinstance(value, tuple):
            for index in value:
                ViewerPayloadControlOptions._validate_nonnegative_int(
                    index,
                    "axis_indices",
                )
            return
        if not isinstance(value, Mapping):
            raise TypeError("Viewer payload axis_indices must be a tuple or mapping.")
        for axis_name, index in value.items():
            if not isinstance(axis_name, str) or not axis_name:
                raise ValueError(
                    "Viewer payload axis_indices keys must be non-empty strings."
                )
            ViewerPayloadControlOptions._validate_nonnegative_int(
                index,
                f"axis_indices[{axis_name!r}]",
            )

    @staticmethod
    def _validate_array_slices(value: tuple[tuple[int, int], ...]) -> None:
        if not isinstance(value, tuple):
            raise TypeError("Viewer payload array_slices must be a tuple.")
        for slice_pair in value:
            if not isinstance(slice_pair, tuple) or len(slice_pair) != 2:
                raise ValueError(
                    "Viewer payload array_slices entries require start and stop."
                )
            start, stop = slice_pair
            ViewerPayloadControlOptions._validate_nonnegative_int(
                start,
                "array_slices start",
            )
            ViewerPayloadControlOptions._validate_nonnegative_int(
                stop,
                "array_slices stop",
            )
            if stop < start:
                raise ValueError(
                    "Viewer payload array_slices stop must not precede start."
                )

    @staticmethod
    def _validate_nonnegative_int(value: object, field_name: str) -> None:
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(f"Viewer payload {field_name} must be an integer.")
        if value < 0:
            raise ValueError(f"Viewer payload {field_name} must be nonnegative.")


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerImageSpatialSampleControls(ViewerPayloadControlOptions):
    """Semantic Y/X bounds; metadata, not payload rank or size, owns layout."""

    def __post_init__(self) -> None:
        super(ViewerImageSpatialSampleControls, self).__post_init__()
        if self.array_slices is None or len(self.array_slices) != 2:
            raise ValueError("Spatial image sampling requires exactly Y/X bounds.")

    def sample_axis_indices(
        self,
        data: np.ndarray,
        image_metadata: ImagePayloadMetadata | None,
        source_data: np.ndarray,
        removed_leading_axes: int,
    ) -> tuple[int, ...]:
        if image_metadata is None:
            raise ValueError("Spatial image sampling requires image metadata.")
        axes = image_metadata.spatial_axes_yx(source_data)
        if axes is None:
            raise ValueError("Image metadata does not declare a spatial Y/X layout.")
        projected = tuple(axis - removed_leading_axes for axis in axes)
        if any(axis < 0 or axis >= data.ndim for axis in projected):
            raise ValueError("Spatial Y/X axes were removed by the payload projection.")
        return projected


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerPayloadProjectionOptions:
    """Runtime projection policy over caller-declared payload controls."""

    controls: ViewerPayloadControlOptions = field(
        default_factory=ViewerPayloadControlOptions
    )
    max_total_shape_payloads: int | None = None
    shape_payload_projection: ViewerShapePayloadProjection = (
        ViewerShapePayloadProjection.FULL
    )

    def __post_init__(self) -> None:
        if not isinstance(self.controls, ViewerPayloadControlOptions):
            raise TypeError(
                "Viewer payload projection controls must be "
                "ViewerPayloadControlOptions."
            )
        if self.max_total_shape_payloads is not None:
            ViewerPayloadControlOptions._validate_nonnegative_int(
                self.max_total_shape_payloads,
                "max_total_shape_payloads",
            )
        if not isinstance(
            self.shape_payload_projection,
            ViewerShapePayloadProjection,
        ):
            raise TypeError(
                "Viewer payload shape_payload_projection must be a "
                "ViewerShapePayloadProjection."
            )


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerStateControlOptions:
    """Formal state-inspection controls shared by agent and viewer runtimes."""

    route_key: str | None = None
    include_component_values: bool = True
    max_component_values_per_layer: int | None = None
    include_payload_summaries: bool = True
    max_payload_summaries_per_layer: int | None = None

    def __post_init__(self) -> None:
        if self.route_key is not None and (
            not isinstance(self.route_key, str) or not self.route_key
        ):
            raise ValueError("Viewer state route_key must be a non-empty string.")
        if not isinstance(self.include_component_values, bool):
            raise TypeError("Viewer state include_component_values must be a bool.")
        self._validate_optional_limit(
            self.max_component_values_per_layer,
            "max_component_values_per_layer",
        )
        if not isinstance(self.include_payload_summaries, bool):
            raise TypeError("Viewer state include_payload_summaries must be a bool.")
        self._validate_optional_limit(
            self.max_payload_summaries_per_layer,
            "max_payload_summaries_per_layer",
        )

    @classmethod
    def from_overrides(
        cls,
        *,
        route_key: str | None = None,
        include_component_values: bool | None = None,
        max_component_values_per_layer: int | None = None,
        include_payload_summaries: bool | None = None,
        max_payload_summaries_per_layer: int | None = None,
    ) -> Self:
        defaults = cls()
        return cls(
            route_key=route_key,
            include_component_values=(
                defaults.include_component_values
                if include_component_values is None
                else include_component_values
            ),
            max_component_values_per_layer=max_component_values_per_layer,
            include_payload_summaries=(
                defaults.include_payload_summaries
                if include_payload_summaries is None
                else include_payload_summaries
            ),
            max_payload_summaries_per_layer=max_payload_summaries_per_layer,
        )

    @staticmethod
    def _validate_optional_limit(value: object, field_name: str) -> None:
        if value is None:
            return
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(f"Viewer state {field_name} must be an integer.")
        if value < 0:
            raise ValueError(f"Viewer state {field_name} must be nonnegative.")


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerRoutedImageControlOptions:
    """Exact route and route-local semantic image coordinates."""

    route_key: str
    axis_indices: Mapping[str, int] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not isinstance(self.route_key, str) or not self.route_key:
            raise ValueError("Viewer image route_key must be a non-empty string.")
        ViewerPayloadControlOptions._validate_axis_indices(dict(self.axis_indices))


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerIntensityWindowControlOptions(ViewerRoutedImageControlOptions):
    """Route-global image contrast derived from caller-declared percentiles.

    Semantic ``axis_indices`` select every real payload record matching those
    coordinates. An empty mapping deliberately selects every real payload
    coordinate on the route; display-array padding is outside this contract.
    """

    low_percentile: float = 1.0
    high_percentile: float = 99.0

    def __post_init__(self) -> None:
        ViewerRoutedImageControlOptions.__post_init__(self)
        low = self._percentile(self.low_percentile, "low_percentile")
        high = self._percentile(self.high_percentile, "high_percentile")
        if low >= high:
            raise ValueError(
                "Viewer intensity-window percentiles must satisfy "
                "low_percentile < high_percentile."
            )

    @classmethod
    def from_overrides(
        cls,
        *,
        route_key: str,
        axis_indices: Mapping[str, int] | None = None,
        low_percentile: float = 1.0,
        high_percentile: float = 99.0,
    ) -> Self:
        return cls(
            route_key=route_key,
            axis_indices={} if axis_indices is None else dict(axis_indices),
            low_percentile=low_percentile,
            high_percentile=high_percentile,
        )

    @staticmethod
    def _percentile(value: object, field_name: str) -> float:
        if isinstance(value, bool) or not isinstance(value, Real):
            raise TypeError(
                f"Viewer intensity-window {field_name} must be a real number."
            )
        numeric = float(value)
        if not isfinite(numeric) or not 0.0 <= numeric <= 100.0:
            raise ValueError(
                f"Viewer intensity-window {field_name} must be finite and within "
                "[0, 100]."
            )
        return numeric


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerFeatureMeasurementControlOptions(ViewerRoutedImageControlOptions):
    """Read-only source-native XY measurement, never a rendered screenshot."""

    vertices_yx: tuple[tuple[float, float], ...]
    max_pixels: int = 262144
    MAX_VERTICES: ClassVar[int] = 64
    MIN_VERTICES: ClassVar[int] = 2
    MAX_PIXELS: ClassVar[int] = 262144

    def __post_init__(self) -> None:
        ViewerRoutedImageControlOptions.__post_init__(self)
        self.validate_vertices(self.vertices_yx, self.MIN_VERTICES)
        self.validate_budget(self.max_pixels, "max_pixels", self.MAX_PIXELS)

    @classmethod
    def validate_vertices(
        cls, vertices: Sequence[Sequence[float]], minimum: int
    ) -> None:
        if not minimum <= len(vertices) <= cls.MAX_VERTICES:
            raise ValueError(
                f"Measurement requires {minimum}..{cls.MAX_VERTICES} vertices."
            )
        for vertex in vertices:
            if len(vertex) != 2:
                raise ValueError(
                    "Measurement vertices must be source-native (y,x) pairs."
                )
            for value in vertex:
                if isinstance(value, bool) or not isinstance(value, Real):
                    raise TypeError("Measurement coordinates must be real numbers.")
                if not isfinite(float(value)):
                    raise ValueError("Measurement coordinates must be finite.")

    @staticmethod
    def validate_budget(value: int, name: str, ceiling: int) -> None:
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(f"Measurement {name} must be an integer.")
        if not 1 <= value <= ceiling:
            raise ValueError(f"Measurement {name} must be within 1..{ceiling}.")


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerPolylineControlOptions(ViewerFeatureMeasurementControlOptions):
    """Polyline profile: inclusive endpoints, mean across a centred pixel band."""

    line_width: int = 1
    interpolation_order: int = 1
    max_samples: int = 4096

    def __post_init__(self) -> None:
        ViewerFeatureMeasurementControlOptions.__post_init__(self)
        self.validate_budget(self.line_width, "line_width", 31)
        self.validate_budget(self.max_samples, "max_samples", 4096)
        if isinstance(self.interpolation_order, bool) or not isinstance(
            self.interpolation_order, int
        ):
            raise TypeError("Measurement interpolation_order must be an integer.")
        if self.interpolation_order not in (0, 1):
            raise ValueError(
                "Only nearest(0) and bilinear(1) interpolation are supported."
            )


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerRegionControlOptions(ViewerFeatureMeasurementControlOptions):
    """An independently authored simple polygon, not a biological object mask."""

    MIN_VERTICES: ClassVar[int] = 3
    background_vertices_yx: tuple[tuple[float, float], ...] | None = None
    support_threshold: float | None = None
    background_sigma: float = 2.0

    def __post_init__(self) -> None:
        ViewerFeatureMeasurementControlOptions.__post_init__(self)
        if self.background_vertices_yx is not None:
            self.validate_vertices(self.background_vertices_yx, 3)
        for name, value in (
            ("support_threshold", self.support_threshold),
            ("background_sigma", self.background_sigma),
        ):
            if value is not None:
                if isinstance(value, bool) or not isinstance(value, Real):
                    raise TypeError(f"Measurement {name} must be numeric.")
                if not isfinite(float(value)):
                    raise ValueError(f"Measurement {name} must be finite.")
        if self.background_sigma < 0:
            raise ValueError("Measurement background_sigma must be nonnegative.")


@dataclass(frozen=True, slots=True)
class ViewerMeasurementCoordinates:
    """Audit projection from the admitted item and native coordinate owners."""

    route_key: str
    source_path: str
    producer: StreamProducerIdentity
    components: dict[str, ViewerScalar | tuple[ViewerScalar, ...]]
    axis_indices: dict[str, int]
    aggregate_axis_indices: tuple[int, ...]
    layer_axis_labels: tuple[str, ...]
    source_domain: ViewerSourceSpatialDomainPayload
    source_spacing: SourceVoxelSpacing
    native_transform: ViewerNativeLayerTransform
    world_units: tuple[str, ...]
    physical_calibration_verified: bool = False
    coordinate_convention: str = (
        "source-native (y,x) pixel centres; world points use mounted layer.data_to_world including full affine"
    )
    calibration_note: str = (
        "Source spacing/units are declared provenance, not independent physical verification; scale1 is not proof of micrometres."
    )


@dataclass(frozen=True, slots=True)
class ViewerIntensityStatistics:
    count: int
    minimum: float
    maximum: float
    mean: float
    median: float
    standard_deviation: float
    total: float

    @classmethod
    def from_pixels(cls, values: np.ndarray) -> ViewerIntensityStatistics:
        import numpy as np

        if not values.size or not np.isfinite(values).all():
            raise ValueError("Measurement pixels must be nonempty and finite.")
        result = cls(
            int(values.size),
            float(values.min()),
            float(values.max()),
            float(values.mean()),
            float(np.median(values)),
            float(values.std(ddof=0)),
            float(values.sum()),
        )
        if not all(
            isfinite(v) for v in (result.mean, result.standard_deviation, result.total)
        ):
            raise ValueError("Measurement statistics overflowed.")
        return result


@dataclass(frozen=True, slots=True)
class ViewerPolylineMeasurement:
    vertices_yx: VerticesYX
    world_vertices: tuple[tuple[float, ...], ...]
    data_length: float
    data_chord_length: float
    world_length: float
    world_chord_length: float
    profile_distance_data: tuple[float, ...]
    profile_distance_world: tuple[float, ...]
    profile_values: tuple[float, ...]
    statistics: ViewerIntensityStatistics
    line_width: int
    interpolation_order: int
    reduction: str = "mean across centred perpendicular band"
    sampling: str = (
        "ceil(segment length+1) endpoint-inclusive; repeated junction uses preceding segment; "
        "nearest(0)/bilinear(1), constant exterior=0 with full band admitted inside source"
    )
    data_length_unit: str = "pixel"
    intensity_unit: str = "raw source value"
    statistics_precision: str = "float64, population standard deviation (ddof=0)"


@dataclass(frozen=True, slots=True)
class ViewerPolygonGeometry:
    area: float
    perimeter: float
    extent: float
    roundness: float


@dataclass(frozen=True, slots=True)
class ViewerRasterRegionGeometry:
    area_pixels: int
    bbox_yx: tuple[int, int, int, int]
    centroid_yx: tuple[float, float]
    extent: float
    perimeter_pixels: float
    roundness: float | None
    eccentricity: float


@dataclass(frozen=True, slots=True)
class ViewerRegionMeasurement:
    vertices_yx: VerticesYX
    world_vertices: tuple[tuple[float, ...], ...]
    polygon: ViewerPolygonGeometry
    world_area: float
    world_perimeter: float
    world_roundness: float
    raster: ViewerRasterRegionGeometry
    statistics: ViewerIntensityStatistics
    background_vertices_yx: VerticesYX | None
    background_statistics: ViewerIntensityStatistics | None
    support_threshold: float | None
    support_count: int | None
    support_fraction: float | None
    foreground_minus_background_mean: float | None
    background_sigma: float
    region_definition: str = (
        "independent simple polygon; integer pixel centres including boundary; NOT a biological mask"
    )
    support_definition: str = (
        "raw values strictly > threshold; explicit threshold or background mean + sigma*population std"
    )
    geometry_definition: str = (
        "polygon area/perimeter are continuous; raster area/extent/perimeter use skimage.regionprops, 4-neighbour perimeter; roundness=4*pi*area/perimeter^2 (not clamped)"
    )
    data_area_unit: str = "pixel^2"
    intensity_unit: str = "raw source value"
    statistics_precision: str = "float64, population standard deviation (ddof=0)"


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerNavigationControlOptions:
    """Formal viewer navigation controls shared by agent and viewer runtimes."""

    DATA_INDEX_SEMANTICS: ClassVar[str] = (
        "Selecting a native feature row by data_index requires the target layer "
        "to remain visible and selected"
    )

    route_key: str
    axis_indices: Mapping[str, int] = field(default_factory=dict)
    visible: bool | None = None
    selected: bool | None = None
    data_index: int | None = None
    display_axes: tuple[str, str] | None = None

    def __post_init__(self) -> None:
        if self.display_axes is not None:
            if isinstance(self.display_axes, (str, bytes)):
                raise TypeError("Viewer display_axes must be a pair of axis names.")
            axes = tuple(self.display_axes)
            if len(axes) != 2 or any(
                not isinstance(axis, str) or not axis for axis in axes
            ):
                raise ValueError(
                    "Viewer display_axes requires two nonempty axis names."
                )
            if axes[0] == axes[1]:
                raise ValueError("Viewer display_axes must select distinct axes.")
            object.__setattr__(self, "display_axes", axes)
        if not isinstance(self.route_key, str) or not self.route_key:
            raise ValueError("Viewer navigation route_key must be a non-empty string.")
        if not isinstance(self.axis_indices, Mapping):
            raise TypeError("Viewer navigation axis_indices must be a mapping.")
        for axis_name, index in self.axis_indices.items():
            if not isinstance(axis_name, str) or not axis_name:
                raise ValueError(
                    "Viewer navigation axis_indices keys must be non-empty strings."
                )
            if isinstance(index, bool) or not isinstance(index, int):
                raise TypeError(
                    f"Viewer navigation index for axis {axis_name!r} must be an integer."
                )
            if index < 0:
                raise ValueError(
                    f"Viewer navigation index for axis {axis_name!r} must be nonnegative."
                )
        for field_name, value in (
            ("visible", self.visible),
            ("selected", self.selected),
        ):
            if value is not None and not isinstance(value, bool):
                raise TypeError(f"Viewer navigation {field_name} must be a bool.")
        if self.data_index is not None:
            if isinstance(self.data_index, bool) or not isinstance(
                self.data_index,
                int,
            ):
                raise TypeError("Viewer navigation data_index must be an integer.")
            if self.data_index < 0:
                raise ValueError("Viewer navigation data_index must be nonnegative.")
            if self.visible is False:
                raise ValueError(
                    f"Viewer navigation: {self.DATA_INDEX_SEMANTICS}; it cannot "
                    "target a hidden layer. Omit data_index when hiding the layer."
                )
            if self.selected is False:
                raise ValueError(
                    f"Viewer navigation: {self.DATA_INDEX_SEMANTICS}; it cannot "
                    "target a deselected layer. Omit data_index when deselecting "
                    "the layer."
                )

    @classmethod
    def from_overrides(
        cls,
        *,
        route_key: str,
        axis_indices: Mapping[str, int] | None = None,
        visible: bool | None = None,
        selected: bool | None = None,
        data_index: int | None = None,
        display_axes: tuple[str, str] | None = None,
    ) -> Self:
        return cls(
            route_key=route_key,
            axis_indices=dict(axis_indices or {}),
            visible=visible,
            selected=selected,
            data_index=data_index,
            display_axes=display_axes,
        )


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerLayerIsolationControlOptions:
    """Atomic visibility, selection, and navigation for a viewer layer set."""

    visible_route_keys: tuple[str, ...]
    selected_route_key: str | None = None
    axis_indices: Mapping[str, int] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not self.visible_route_keys:
            raise ValueError(
                "Viewer layer isolation requires at least one visible route key."
            )
        if any(
            not isinstance(route_key, str) or not route_key
            for route_key in self.visible_route_keys
        ):
            raise ValueError(
                "Viewer layer isolation route keys must be non-empty strings."
            )
        if self.selected_route_key is not None and (
            not isinstance(self.selected_route_key, str) or not self.selected_route_key
        ):
            raise ValueError(
                "Viewer layer isolation selected_route_key must be a non-empty string."
            )
        ViewerNavigationControlOptions.from_overrides(
            route_key=self.selected_route,
            axis_indices=self.axis_indices,
            visible=True,
            selected=True,
        )

    @classmethod
    def from_overrides(
        cls,
        *,
        visible_route_keys: Sequence[str],
        selected_route_key: str | None = None,
        axis_indices: Mapping[str, int] | None = None,
    ) -> Self:
        return cls(
            visible_route_keys=tuple(visible_route_keys),
            selected_route_key=selected_route_key,
            axis_indices=dict(axis_indices or {}),
        )

    @property
    def requested_visible_route_keys(self) -> tuple[str, ...]:
        return tuple(dict.fromkeys(self.visible_route_keys))

    @property
    def selected_route(self) -> str:
        return self.selected_route_key or self.requested_visible_route_keys[-1]

    @property
    def effective_visible_route_keys(self) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys((*self.requested_visible_route_keys, self.selected_route))
        )

    @property
    def visible_routes(self) -> frozenset[str]:
        return frozenset(self.effective_visible_route_keys)

    def navigation_for(self, route_key: str) -> ViewerNavigationControlOptions:
        selected = route_key == self.selected_route
        return ViewerNavigationControlOptions.from_overrides(
            route_key=route_key,
            axis_indices=self.axis_indices if selected else None,
            visible=route_key in self.visible_routes,
            selected=selected,
        )
