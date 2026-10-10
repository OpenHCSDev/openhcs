"""Nominal runtime image payload values and metadata."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import (
    Callable,
    Iterable,
    Sequence,
)
from dataclasses import dataclass, field, fields
from enum import Enum
from typing import Any, TypeVar

import numpy as np
from arraybridge import ArrayGeometry, MemoryType, detect_memory_type
from python_introspect import dataclass_from_mapping, to_jsonable
from zmqruntime.viewer_protocol import (
    ViewerWireField,
    ViewerWireMapping,
    ViewerWirePayload,
)
from collections.abc import Mapping

from openhcs.core.alias_property import AliasProperty
from openhcs.core.payload_axes import (
    AxisSpec,
    PayloadAxes,
    RuntimePlaneAxisSpec,
    SpatialAxisSpec,
    UndeclaredAxisSpec,
)
from openhcs.core.runtime_array_values import (
    DataBackedRuntimeArrayPayload,
    RuntimeArrayData,
    RuntimeArrayPayload,
    array_geometry,
    is_array_payload,
    mask_array,
    runtime_array_operand,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
    RuntimeSliceProjectableValue,
)
from openhcs.core.source_image_provenance import (
    SourceComponentMetadata,
    SourceImageProvenance,
    SourceImageProvenanceFields,
    SourcePlaneIndexedProvenanceExpansion,
)
from openhcs.core.source_metadata import (
    SourceMetadataScalar,
    SourceVoxelSpacing,
    SourceVoxelSpacingFields,
)
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    SourceSpatialDomainFields,
    SpatiallyPlacedValue,
)
from openhcs.core.source_spatial_domain import (
    _spatial_shape_pair as _source_spatial_shape_pair,
)
from openhcs.core.axes import AxisFamily, AxisRole, ColourAxis

PhysicalBorderEdgesYX = tuple[bool, bool, bool, bool] | None

OBJECT_LABEL_SOURCE_SPATIAL_VALUE_NAME = "Object-label"

MetadataValueT = TypeVar("MetadataValueT")


@dataclass(frozen=True, slots=True)
class ImageUnitIntervalIntensityMetadata:
    """Normalized analytical pixels, with optional exact quantization proof.

    An absent scale means arithmetic changed the quantization, not that current
    pixels reverted to acquisition codes. Absence of this record denotes the
    unnormalized source domain.
    """

    scale: int | None = None
    source_plane_scales: tuple[int | None, ...] = ()

    def scale_for_source_plane(self, plane_index: int) -> int | None:
        """Return one plane's proof, falling back to the scalar proof."""

        plane_scale = _tuple_value(self.source_plane_scales, plane_index)
        return self.scale if plane_scale is None else int(plane_scale)

    def for_source_plane(
        self, plane_index: int
    ) -> "ImageUnitIntervalIntensityMetadata":
        """Project this proof to one source plane."""

        return type(self)(scale=self.scale_for_source_plane(plane_index))

    def for_source_planes(
        self,
        plane_indices: tuple[int, ...],
    ) -> "ImageUnitIntervalIntensityMetadata":
        """Project per-plane proofs to an ordered source-plane subset."""

        return type(self)(
            scale=self.scale,
            source_plane_scales=_tuple_values_at_indices(
                self.source_plane_scales,
                plane_indices,
            ),
        )

    def without_source_planes(self) -> "ImageUnitIntervalIntensityMetadata":
        """Discard per-plane proofs after removing their represented axis."""

        return type(self)(scale=self.scale)


@dataclass
class ImagePayloadIntensityFields(ABC):
    """Current pixel intensity semantics, independent of provenance and placement.

    The composed metadata owner supplies payload construction and field
    replacement; this capability owns scale/quantization and
    their numerical interpretation. Dataclass fields remain the single stored
    declarations the metadata codecs read.
    """

    intensity_scale: float | None = None
    source_dtype: str | None = None
    unit_interval_intensity: ImageUnitIntervalIntensityMetadata | None = None
    source_plane_intensity_scales: tuple[float | None, ...] = ()
    source_plane_dtypes: tuple[str | None, ...] = ()

    @abstractmethod
    def replace_fields(self, **changes: Any) -> "ImagePayloadMetadata": ...

    @abstractmethod
    def payload_with(self, data: Any, mask: Any | None = None) -> Any: ...

    @property
    @abstractmethod
    def has_leading_intensity_axis(self) -> bool: ...

    @abstractmethod
    def require_leading_intensity_axis(self) -> None:
        """Require the declared plane layout before applying per-plane scales."""

    @property
    def has_normalized_intensity(self) -> bool:
        """Current pixels have left the raw acquisition-code domain."""
        return self.unit_interval_intensity is not None

    @property
    def unit_interval_intensity_scale(self) -> int | None:
        """Return the authored scalar unit-interval quantization proof."""
        if self.unit_interval_intensity is None:
            return None
        return self.unit_interval_intensity.scale

    @property
    def source_plane_unit_interval_intensity_scales(self) -> tuple[int | None, ...]:
        """Return authored per-plane unit-interval quantization proofs."""
        if self.unit_interval_intensity is None:
            return ()
        return self.unit_interval_intensity.source_plane_scales

    def intensity_scale_for_source_plane(self, plane_index: int) -> float | None:
        """Return the best available intensity scale for one source plane."""
        plane_scale = _tuple_value(self.source_plane_intensity_scales, plane_index)
        return self.intensity_scale if plane_scale is None else plane_scale

    def unit_interval_intensity_scale_for_source_plane(self, plane_index: int) -> int | None:
        """Return the scale proving current pixels are exact integer/scale values."""
        if self.unit_interval_intensity is None:
            return None
        return self.unit_interval_intensity.scale_for_source_plane(plane_index)

    def project_intensity_proof(self, plane_index: int | None) -> ImageUnitIntervalIntensityMetadata | None:
        """Select a plane's proof, or retain only the proof for the whole image."""
        if self.unit_interval_intensity is None:
            return None
        if plane_index is None:
            return self.unit_interval_intensity.without_source_planes()
        return self.unit_interval_intensity.for_source_plane(plane_index)

    def common_unit_interval_intensity_scale(self) -> int | None:
        """Return the common unit-interval quantization proof for this payload."""
        if self.source_plane_unit_interval_intensity_scales:
            present = tuple(
                scale
                for plane_index in range(len(self.source_plane_unit_interval_intensity_scales))
                for scale in (self.unit_interval_intensity_scale_for_source_plane(plane_index),)
            )
            if any(scale is None for scale in present):
                return None
            first = present[0]
            if all(scale == first for scale in present):
                return first
            return None
        return self.unit_interval_intensity_scale

    def with_unit_interval_intensity_scale(self, scale: int | None) -> "ImagePayloadMetadata":
        """Return metadata with the current unit-interval pixel proof updated."""
        return self.replace_fields(
            unit_interval_intensity=ImageUnitIntervalIntensityMetadata(scale=scale)
        )

    def without_unit_interval_intensity_scale(self) -> "ImagePayloadMetadata":
        """Invalidate quantization without changing the current intensity domain."""
        return self.replace_fields(
            unit_interval_intensity=(
                ImageUnitIntervalIntensityMetadata() if self.has_normalized_intensity
                else None
            )
        )

    def with_current_intensity_from(
        self, source: "ImagePayloadIntensityFields", *, plane_index: int | None = None,
    ) -> "ImagePayloadMetadata":
        """Retarget acquisition context onto an independently owned pixel buffer."""
        return self.replace_fields(
            unit_interval_intensity=(
                source.unit_interval_intensity if plane_index is None
                else source.project_intensity_proof(plane_index)
            )
        )

    @staticmethod
    def normalization_dtype(source_dtype: Any, dtype: Any) -> np.dtype | None:
        """Return the target dtype of a real-valued intensity conversion, or None."""
        target_dtype = np.dtype(np.float32 if dtype is None else dtype)
        if not (
            np.issubdtype(source_dtype, np.number)
            or np.issubdtype(source_dtype, np.bool_)
        ) or np.issubdtype(source_dtype, np.complexfloating):
            return None
        return target_dtype

    def normalize_intensity_payload(
        self, payload: Any, *, dtype: Any = None, channel_index: int = 0,
    ) -> Any:
        """Normalize the declared current domain, independently of storage dtype."""
        array = payload.data
        memory_type = MemoryType(detect_memory_type(array))
        target_dtype = self.normalization_dtype(
            memory_type.canonical_dtype_name(array.dtype), dtype,
        )
        if target_dtype is None:
            return payload
        if self.has_normalized_intensity:
            return self.payload_with(
                memory_type.astype(array, target_dtype), payload.mask,
            )
        if self.has_leading_intensity_axis and self.source_plane_intensity_scales:
            if len(self.source_plane_intensity_scales) != len(array):
                raise ValueError(
                    "Image intensity scales must match the declared leading plane axis."
                )
            self.require_leading_intensity_axis()
            source_dtype = np.dtype(memory_type.canonical_dtype_name(array.dtype))
            scale_proofs = tuple(
                self.normalization_scale(
                    source_dtype, self.intensity_scale_for_source_plane(index),
                )
                for index in range(len(array))
            )
            metadata = self.replace_fields(
                unit_interval_intensity=ImageUnitIntervalIntensityMetadata(
                    source_plane_scales=tuple(proof for _, proof in scale_proofs),
                ),
            )
            return metadata.payload_with(
                memory_type.normalize_planes(
                    array, target_dtype, tuple(scale for scale, _ in scale_proofs),
                ),
                payload.mask,
            )
        normalized, proof_scale = self.normalized_intensity_array(
            array, target_dtype=target_dtype,
            scale=self.intensity_scale_for_source_plane(channel_index),
        )
        return self.with_unit_interval_intensity_scale(proof_scale).payload_with(
            normalized, payload.mask,
        )

    @staticmethod
    def normalization_scale(
        source_dtype: np.dtype, scale: float | None,
    ) -> tuple[float | None, int | None]:
        """Return the current-domain divisor and its integer acquisition proof."""
        if scale is None:
            # A promoted float uses its declared source scale, never a range guess.
            scale = image_intensity_scale_for_dtype(source_dtype)
        if scale is None:
            return None, None
        if not np.isfinite(scale) or scale <= 0:
            raise ValueError("Source intensity scale must be finite and positive.")
        proof_scale = (
            int(scale)
            if np.issubdtype(source_dtype, np.integer) and float(scale).is_integer()
            else None
        )
        return scale, proof_scale

    @staticmethod
    def normalized_intensity_array(
        array: Any, *, target_dtype: np.dtype, scale: float | None,
    ) -> tuple[Any, int | None]:
        """Apply one numerical recipe without projecting image source identity."""
        memory_type = MemoryType(detect_memory_type(array))
        source_dtype = np.dtype(memory_type.canonical_dtype_name(array.dtype))
        scale, proof_scale = ImagePayloadIntensityFields.normalization_scale(
            source_dtype, scale,
        )
        normalized = memory_type.astype(array, target_dtype)
        if scale is not None:
            normalized = normalized / float(scale)
        return normalized, proof_scale

    @classmethod
    def intensity_coherent_payloads(cls, payloads: Sequence[Any]) -> tuple[Any, ...]:
        """Reconcile raw/normalized members before a dense buffer erases dtype."""
        metadata = tuple(payload.metadata for payload in payloads)
        normalized = tuple(record.has_normalized_intensity for record in metadata)
        if not any(normalized) or all(normalized):
            return tuple(payloads)
        return tuple(
            record.normalize_intensity_payload(payload)
            for record, payload in zip(metadata, payloads, strict=True)
        )


class ImagePayloadAxisFields(ABC):
    """Declared dimensions shared by image metadata capabilities.

    Concrete metadata stores the declarations (``axes``, ``plane_axis`` and the
    spatial domain). This capability resolves them against concrete pixels:
    which index carries a role, which indices are spatial, and how a
    declaration moves when a leading axis is added or removed.
    """

    @property
    @abstractmethod
    def axes(self) -> PayloadAxes: ...

    @property
    @abstractmethod
    def plane_axis(self) -> RuntimePlaneAxis | None: ...

    @property
    @abstractmethod
    def source_spatial_domain(self) -> SourceSpatialDomain: ...

    def require_scalar_source_plane(self) -> None:
        """Require source metadata for one scalar grayscale image plane."""
        if self.plane_axis is not None:
            raise ValueError("Exported source planes require scalar image metadata.")
        if self.axes.has_values:
            raise ValueError("Exported Z planes cannot carry declared non-spatial axes.")

    def require_leading_plane_axis(self, message: str) -> None:
        """Require axis presence before later ordered projection validation."""
        if self.plane_axis is None:
            raise ValueError(message)

    def axis_position(self, role: type[AxisRole]) -> int | None:
        """Return the declared rank-relative position of the axis carrying ``role``."""
        return self.axes.position_of(role)

    def axis_index(self, role: type[AxisRole], data: Any) -> int | None:
        """Return the index of the axis carrying ``role`` in ``data``."""
        return self.axes.index_of(role, array_geometry(data).ndim)

    def with_axis(self, spec: AxisSpec, position: int) -> "ImagePayloadMetadata":
        """Return metadata that declares ``spec`` at ``position``."""
        return self.replace_fields(axes=self.axes.with_axis(spec, position))

    def without_axis(self, role: type[AxisRole]) -> "ImagePayloadMetadata":
        """Return metadata after an operation removes the axis carrying ``role``."""
        return self.replace_fields(axes=self.axes.without_role(role))

    def undeclared_axes(self, data: Any) -> tuple[int, ...]:
        """Return pixel axes that no explicit axis declaration claims."""
        ndim = array_geometry(data).ndim
        declared = self.axes.indices(ndim)
        return tuple(axis for axis in range(ndim) if axis not in declared)

    def spatial_axes(self, data: Any) -> tuple[int, ...]:
        """Project the declared spatial domain onto current pixels.

        Source cohorts can add leading tile, time or binding axes without
        adding a physical dimension, and declared axes are never spatial. The
        spatial axes are the trailing undeclared axes, as many as the spatial
        domain's rank.
        """
        candidate_axes = self.undeclared_axes(data)
        spatial_rank = self.source_spatial_domain.spatial_rank
        if len(candidate_axes) < spatial_rank:
            raise ValueError(
                f"Declared spatial rank {spatial_rank} exceeds payload rank "
                f"{array_geometry(data).ndim} after excluding its declared axes."
            )
        return candidate_axes[len(candidate_axes) - spatial_rank:]

    def spatial_axes_yx(self, data: Any) -> tuple[int, int] | None:
        """Return the axes that carry the spatial domain's planar Y/X placement."""
        if self.source_spatial_domain.spatial_rank < 2:
            return None
        candidate_axes = self.undeclared_axes(data)
        if len(candidate_axes) < 2:
            return None
        return candidate_axes[-2], candidate_axes[-1]

    def payload_axes(self, data: Any) -> tuple[AxisSpec, ...]:
        """Return one declared dimension per axis of ``data``."""
        ndim = array_geometry(data).ndim
        resolved: dict[int, AxisSpec] = dict(self.axes.indices(ndim))
        if self.plane_axis is not None:
            if 0 in resolved:
                raise ValueError("Image metadata declares its leading plane axis twice.")
            resolved[0] = RuntimePlaneAxisSpec(self.plane_axis.value)
        candidates = tuple(axis for axis in range(ndim) if axis not in resolved)
        names = self.source_spatial_domain.axis_names
        spatial = candidates[len(candidates) - len(names):] if names else ()
        if len(spatial) == len(names):
            for axis, name in zip(spatial, names, strict=True):
                resolved[axis] = SpatialAxisSpec(name)
        return tuple(resolved.get(axis, UndeclaredAxisSpec()) for axis in range(ndim))

    def declares_colour_samples_plane(self, data: Any) -> bool:
        """Return whether this payload declares one colour-sampled image plane."""
        return self.axis_index(ColourAxis, data) is not None and self.plane_axis is None

    def declares_colour_samples_stack(self, data: Any) -> bool:
        """Return whether this payload declares a plane stack of colour-sampled images."""
        return self.axis_index(ColourAxis, data) is not None and self.plane_axis is not None

    def spatial_shape_yx(self, data: Any) -> tuple[int, int] | None:
        """Return the planar Y/X shape from the declared spatial axes."""
        axes = self.spatial_axes_yx(data)
        if axes is None:
            return None
        shape = array_geometry(data).shape
        return shape[axes[0]], shape[axes[1]]

    @property
    def has_leading_intensity_axis(self) -> bool:
        """Bind intensity projection to the existing image-axis declaration."""
        return self.plane_axis is not None

    def require_leading_intensity_axis(self) -> None:
        """Keep numerical normalization inside the existing image-axis domain."""
        self.require_leading_plane_axis(
            "Leading intensity normalization requires a declared plane axis."
        )
        self.axes.after_leading_axis_removed()


@dataclass(slots=True)
class ImagePayloadMetadata(
    SourceImageProvenanceFields,
    ImagePayloadAxisFields,
    ImagePayloadIntensityFields,
    SourceSpatialDomainFields,
    SourceVoxelSpacingFields,
):
    """Generic source-image metadata that should travel with runtime pixels."""

    physical_border_edges_yx: PhysicalBorderEdgesYX = None
    mask_defines_border: bool | None = None
    axes: PayloadAxes = field(
        default_factory=PayloadAxes, metadata={ViewerWireField.IMAGE_METADATA: True}
    )
    plane_axis: RuntimePlaneAxis | None = field(
        default=None, metadata={ViewerWireField.IMAGE_METADATA: True}
    )

    @classmethod
    def viewer_field_names(cls) -> frozenset[str]:
        """Derive the viewer projection from its actual metadata declarations."""
        return frozenset(
            member.name
            for member in fields(cls)
            if member.metadata.get(ViewerWireField.IMAGE_METADATA, False)
        )

    def require_source_image_pixels(self, data: Any) -> None:
        """Validate decoded pixels against declared XY placement and dtype."""
        self.source_spatial_domain.require_image_window(data.shape)
        if self.source_dtype is not None and np.dtype(self.source_dtype) != data.dtype:
            raise ValueError(
                "Exported image pixels conflict with their declared dtype."
            )

    def singleton_plane_projection(self) -> RuntimePlaneAxisValueProjection | None:
        """Select a declared leading axis only with one exact runtime source plane."""
        plane_count = self.source_provenance.source_plane_count
        if self.plane_axis is None or plane_count != 1:
            return None
        return RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=self.plane_axis,
            axis_size=plane_count,
            plane_index=0,
            source_aliases=self.source_image_names,
        )

    def to_viewer_image_metadata(self) -> ViewerWireMapping:
        return ViewerWirePayload.mapping(
            {
                name: to_jsonable(getattr(self, name))
                for name in self.viewer_field_names()
            },
            context="viewer image metadata",
        )

    @classmethod
    def from_viewer_image_metadata(
        cls, values: Mapping[str, object]
    ) -> "ImagePayloadMetadata":
        """Decode only declaration-owned viewer fields, never hidden source records."""
        if not isinstance(values, Mapping):
            raise TypeError("Viewer image metadata requires a mapping.")
        extras = set(values) - cls.viewer_field_names()
        if extras:
            raise ValueError(f"Undeclared viewer metadata fields: {sorted(extras)!r}.")
        return cls.from_mapping(values)

    @classmethod
    def from_mapping(cls, values: Mapping[str, object]) -> "ImagePayloadMetadata":
        """Restore all declared metadata fields through their field codecs."""
        decoded = dict(values)
        if "source_provenance" in decoded:
            decoded["source_provenance"] = SourceImageProvenance.from_mapping(
                decoded["source_provenance"]
            )
        if "source_spatial_domain" in decoded:
            decoded["source_spatial_domain"] = SourceSpatialDomain.from_mapping(
                decoded["source_spatial_domain"]
            )
        if "axes" in decoded:
            decoded["axes"] = PayloadAxes.from_mapping(decoded["axes"])
        return dataclass_from_mapping(cls, decoded)

    def retained_plane_component_values(
        self,
    ) -> dict[str, tuple[SourceMetadataScalar, ...]]:
        """Derive varying source coordinates of the retained nominal plane axis.

        Source provenance can also describe contributors after a projection.
        Only a retained plane-axis declaration makes those coordinates a pixel
        axis; artifact storage/grouping axes do not declare that image domain.
        """

        if self.plane_axis is None:
            return {}
        return self.source_provenance.varying_plane_component_values(
            AxisFamily.active().axes
        )

    @classmethod
    def for_array(
        cls,
        array: Any,
        *,
        source_path: str | None = None,
    ) -> "ImagePayloadMetadata":
        """Build metadata from an image array's source dtype."""
        import numpy as np

        dtype = np.asarray(array).dtype
        return cls(
            intensity_scale=image_intensity_scale_for_dtype(dtype),
            source_dtype=str(dtype),
            source_path=source_path,
        )

    @classmethod
    def for_array_payload(
        cls,
        array: Any,
        *,
        source_path: str | None = None,
    ) -> "ImagePayloadMetadata":
        """Build source metadata from an arraybridge-detectable payload."""
        from openhcs.core.memory import MEMORY_TYPE_NUMPY, detect_memory_type

        memory_type = detect_memory_type(array)
        dtype = array.dtype
        if memory_type == MEMORY_TYPE_NUMPY:
            intensity_scale = image_intensity_scale_for_dtype(dtype)
        else:
            intensity_scale = None
        return cls(
            intensity_scale=intensity_scale,
            source_dtype=str(dtype),
            source_path=source_path,
        )

    def __post_init__(self, *source_provenance_values: object) -> None:
        self.absorb_explicit_source_provenance(source_provenance_values)
        self.normalize_metadata_fields()

    def normalize_metadata_fields(self) -> None:
        """Normalize this metadata's typed fields in their constructor effect order."""
        self.source_voxel_spacing = self.source_voxel_spacing.with_missing_from(
            SourceVoxelSpacing.from_source_metadata(self.source_component_metadata)
        )
        self.normalize_source_provenance_fields()
        self.normalize_source_spatial_domain_fields()
        self.normalize_source_voxel_spacing_fields()
        if not isinstance(self.axes, PayloadAxes):
            raise TypeError("ImagePayloadMetadata.axes must be PayloadAxes.")
        if self.plane_axis is not None:
            self.plane_axis = RuntimePlaneAxis(self.plane_axis)


    @property
    def has_values(self) -> bool:
        """Return whether this metadata carries any semantic image facts."""
        return any(
            (
                self.intensity_scale is not None,
                self.source_dtype is not None,
                self.source_path is not None,
                self.source_component_metadata is not None,
                self.unit_interval_intensity is not None,
                bool(self.source_plane_intensity_scales),
                bool(self.source_plane_dtypes),
                self.source_image_provenance_planes.has_values,
                self.source_spatial_domain.has_values,
                self.source_voxel_spacing.has_values,
                self.physical_border_edges_yx is not None,
                self.mask_defines_border is not None,
                bool(self.source_image_names),
                self.axes.has_values,
                self.plane_axis is not None,
            )
        )

    def attach_to(self, payload: "ImagePayload") -> "ImagePayload":
        """Attach this metadata to image pixels, wrapping bare pixels once."""
        return ImagePayload.of(payload).with_metadata(self)

    def attach_source_context_to(self, payload: "ImagePayload") -> "ImagePayload":
        """Attach source context while retaining the payload's declared array axes."""

        return self.replace_fields(
            axes=payload.metadata.axes,
            plane_axis=payload.metadata.plane_axis,
        ).attach_to(payload)

    def derive_payload(
        self,
        source_payload: "ImagePayload",
        data: "ImagePayload",
        *,
        plane_projection: RuntimePlaneAxisValueProjection | None = None,
    ) -> "ImagePayload":
        """Project this source metadata and mask onto derived image data."""
        source_shape_yx = self.spatial_shape_yx(source_payload)
        output_metadata = data.metadata
        output_shape_yx = output_metadata.spatial_shape_yx(data)
        same_spatial_domain = (
            source_shape_yx is not None
            and output_shape_yx is not None
            and source_shape_yx == output_shape_yx
        )
        metadata = self._derived_metadata(data, plane_projection)
        if (
            not same_spatial_domain
            and not output_metadata.source_spatial_domain.has_values
        ):
            metadata = metadata.without_spatial_domain()
        output_mask = data.mask
        if output_mask is None and same_spatial_domain:
            output_mask = project_image_mask_to_data_domain(
                source_payload.mask,
                data.data,
                metadata=metadata,
            )
        return metadata.payload_with(data.data, output_mask)

    def _derived_metadata(
        self,
        data: "ImagePayload",
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> "ImagePayloadMetadata":
        output_metadata = data.metadata.with_indexed_source_plane_provenance(None)
        source_metadata = self.with_indexed_source_plane_provenance(None)
        output_metadata_is_authoritative = output_metadata.has_values
        declared_output_axis = (
            output_metadata.plane_axis
            if output_metadata_is_authoritative
            else source_metadata.plane_axis
        )
        if plane_projection is None and (
            declared_output_axis is not None or source_metadata.plane_axis is not None
        ):
            declared_axis = declared_output_axis or source_metadata.plane_axis
            raise ValueError(
                "Derived image payload carries a declared plane axis but the "
                "invocation supplied no plane projection: "
                f"{declared_axis.value!r}."
            )
        if plane_projection is not None and plane_projection.plane_index is None:
            for owner_name, metadata in (
                ("source", source_metadata),
                ("output", output_metadata),
            ):
                if (
                    metadata.plane_axis is not None
                    and metadata.plane_axis is not plane_projection.axis
                ):
                    raise ValueError(
                        f"Derived image {owner_name} metadata axis conflicts with "
                        "the invocation projection: "
                        f"{metadata.plane_axis.value!r} != "
                        f"{plane_projection.axis.value!r}."
                    )
            source_metadata = source_metadata.with_indexed_source_plane_provenance(
                plane_projection.axis_size
            )
            if declared_output_axis is not None:
                plane_projection.validate_shape(
                    data.geometry.shape,
                    value_name="Derived image payload",
                )
                output_metadata = output_metadata.with_indexed_source_plane_provenance(
                    plane_projection.axis_size
                )
        elif plane_projection is not None:
            for owner_name, metadata in (
                ("source", source_metadata),
                ("output", output_metadata),
            ):
                if metadata.plane_axis is not None:
                    raise ValueError(
                        f"Derived image {owner_name} metadata retains an unconsumed "
                        f"{metadata.plane_axis.value!r} axis after the invocation "
                        "selected one plane."
                    )
        # Read current source fields before deriving the output. This private
        # snapshot owns its stripped axes; no intermediate image is published.
        source_context = source_metadata.replace_fields(plane_axis=None)
        if not data.inherits_source_axes:
            source_context.axes = PayloadAxes()
        # Take current output calibration and geometry before replacing stale
        # source identity. These fields belong to the returned pixel domain.
        metadata = output_metadata.with_source_spatial_context_from(source_context)
        if source_metadata.source_provenance.has_values:
            # The source owns derived-image provenance. Do not merge every
            # output plane into a value that this source identity supersedes.
            source_provenance = (
                source_metadata.source_provenance.with_derived_source_image_names(
                    output_metadata.source_image_names
                    or source_metadata.source_image_names
                )
            )
        else:
            source_provenance = metadata.source_provenance.with_missing_from(
                source_context.source_provenance
            )
        return metadata.replace_fields(
            source_provenance=source_provenance,
            axes=(
                metadata.axes if metadata.axes.has_values else source_context.axes
            ),
            plane_axis=declared_output_axis,
            **metadata._missing_intensity_fields(source_metadata),
        )

    def project_channel_payload(
        self,
        source_payload: "ImagePayload",
        source_data: Any,
        channel_index: int,
        *,
        channel_data: Any | None = None,
        channel_axis: int = 0,
    ) -> "ImagePayload":
        """Project one channel while preserving metadata and mask semantics."""
        if channel_data is None:
            channel_data = ImageMaskDomain.channel_axis_slice(
                source_data,
                channel_axis=channel_axis,
                channel_index=channel_index,
            )
        colour_axis = self.axis_index(ColourAxis, source_data)
        projected_axis = channel_axis % array_geometry(source_data).ndim
        metadata = (
            self.for_source_plane(channel_index)
            if self.has_plane_specific_values
            else self
        )
        if colour_axis == projected_axis:
            metadata = metadata.without_axis(ColourAxis)
        mask = source_payload.mask
        if mask is not None:
            mask = ImageMaskDomain.projected_channel_mask(
                mask,
                source_data=source_data,
                channel_data=channel_data,
                channel_index=channel_index,
                channel_axis=channel_axis,
            )
        return metadata.payload_with(channel_data, mask)

    def has_complete_source_identity(
        self,
        payload: "ImagePayload",
        plane_projection: RuntimePlaneAxisValueProjection | None = None,
    ) -> bool:
        """Validate source identity against declared runtime-plane semantics."""
        planes = self.source_image_provenance_planes
        if (
            plane_projection is not None
            and plane_projection.plane_index is None
            and plane_projection.axis_size > 1
            and self.plane_axis is None
        ):
            return False
        if plane_projection is not None and self.plane_axis is not None:
            if self.plane_axis is not plane_projection.axis:
                raise ValueError(
                    "Image payload plane declaration conflicts with the execution "
                    f"projection: {self.plane_axis!r} != {plane_projection.axis!r}."
                )
            plane_projection.validate_shape(
                payload.geometry.shape,
                value_name="Source-identified image payload",
            )
            if planes.count != plane_projection.axis_size:
                return False
        if planes.has_values:
            return all(plane.addressable for plane in planes.planes)
        return self.source_provenance.addressable

    @classmethod
    def compose(
        cls,
        payloads: Sequence["ImagePayload"],
        *,
        mode: "ImagePayloadMetadataCompositionMode | None" = None,
        source_metadata: Sequence["ImagePayloadMetadata"] | None = None,
    ) -> "ImagePayloadMetadata":
        """Compose metadata for payloads assembled on a new leading axis."""
        resolved_mode = (
            ImagePayloadMetadataCompositionMode.STACK if mode is None else mode
        )
        return _ImagePayloadMetadataComposer(
            payloads=tuple(payloads),
            mode=resolved_mode,
            source_metadata_override=source_metadata,
            metadata_type=cls,
        ).compose()


    def mask_domain(self, data: Any) -> "ImageMaskDomain":
        """Return the mask domain declared for this payload."""
        spatial_axes_yx = (
            self.spatial_axes_yx(data)
            if self.source_spatial_domain.source_shape_yx is not None
            else None
        )
        shape = array_geometry(data).shape
        return ImageMaskDomain(
            shape,
            tuple(sorted(self.axes.indices(len(shape)))),
            self.plane_axis,
            spatial_axes_yx,
        )

    def persists_whole_image(self) -> bool:
        """Keep intrinsic pixels whole, excluding a distinct image-binding axis."""
        return (
            self.source_spatial_domain.persists_whole_image()
            and self.plane_axis is not RuntimePlaneAxis.SOURCE_BINDING
        )

    def for_leading_source_plane(self, plane_index: int) -> "ImagePayloadMetadata":
        """Project metadata after explicitly removing its leading plane axis."""
        return LeadingSourcePlaneMetadataProjection(self, plane_index).project()

    def without_leading_plane_axis(
        self, *, projection: "ImageMetadataProjection | None" = None
    ) -> "ImagePayloadMetadata":
        """Remove an axis through the projection's declared result ownership."""
        self.require_leading_plane_axis(
            "Image metadata has no leading plane axis to remove."
        )
        axes = self.axes.after_leading_axis_removed()
        if projection is None:
            projection = LeadingPlaneAxisMetadataProjection(self)
        projected = projection.project_source_provenance(
            self, self.source_provenance.with_runtime_planes_as_contributors()
        )
        if self.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE:
            projected.source_spatial_domain = (
                projected.source_spatial_domain.for_intrinsic_plane()
            )
        projected.plane_axis = None
        projected.axes = axes
        projected.source_plane_intensity_scales = ()
        projected.source_plane_dtypes = ()
        projected.unit_interval_intensity = self.project_intensity_proof(None)
        projected.normalize_metadata_fields()
        return projected

    def collapse_leading_plane_axis(self) -> "ImagePayloadMetadata":
        """Return scalar metadata after reducing every plane of the leading axis."""

        collapsed = self.without_leading_plane_axis()
        return collapsed.with_source_provenance(
            collapsed.source_provenance.with_common_scalar_identity_from_planes()
        )

    @property
    def has_plane_specific_values(self) -> bool:
        """Return whether selecting a payload plane can change metadata."""
        return any(
            (
                bool(self.source_plane_intensity_scales),
                bool(self.source_plane_dtypes),
                bool(self.source_plane_unit_interval_intensity_scales),
                self.source_provenance.source_plane_count > 0,
                len(self.source_image_names) > 1,
            )
        )

    @property
    def source_image_paths(self) -> tuple[str, ...]:
        """Return paths from exact source identities represented by this payload."""
        return tuple(
            dict.fromkeys(
                str(identity.path)
                for identity in self.source_provenance.represented_source_identities
                if identity.path is not None and str(identity.path)
            )
        )

    @property
    def source_plane_metadata_count(self) -> int:
        """Return the cardinality represented by plane-specific metadata."""
        return max(
            1,
            self.source_provenance.source_plane_count,
            len(self.source_plane_intensity_scales),
            len(self.source_plane_dtypes),
            len(self.source_plane_unit_interval_intensity_scales),
        )

    def source_metadata_by_payload(self) -> tuple["ImagePayloadMetadata", ...]:
        """Return one scalar metadata record per represented source plane."""
        if (
            self.source_plane_metadata_count == 1
            and not self.source_provenance.source_plane_count
        ):
            return (self,)
        return tuple(
            self.for_source_plane(plane_index)
            for plane_index in range(self.source_plane_metadata_count)
        )

    def payload_with(self, data: Any, mask: Any | None = None) -> "ImagePayload":
        """Return the image payload that carries this metadata and mask on ``data``."""
        if mask is not None:
            return MaskedImagePayload(data=data, mask=mask, metadata=self)
        if self.has_values:
            return ImageMetadataPayload(data=data, metadata=self)
        return PlainImagePayload(data)

    def for_source_plane(self, plane_index: int) -> "ImagePayloadMetadata":
        """Return metadata for one source plane sliced from a stacked payload."""
        return SourcePlaneImageMetadataProjection(self, plane_index).project()

    def for_source_planes(
        self,
        plane_indices: Sequence[int],
    ) -> "ImagePayloadMetadata":
        """Return metadata projected to an ordered group of source planes."""
        normalized_indices = tuple(int(index) for index in plane_indices)
        if not normalized_indices:
            raise ValueError("Source-plane metadata projection cannot be empty.")
        if not self.has_plane_specific_values:
            return self
        invalid_indices = tuple(
            index
            for index in normalized_indices
            if index < 0 or index >= self.source_plane_metadata_count
        )
        if invalid_indices:
            raise IndexError(
                "Source-plane metadata projection indices must be within "
                f"0..{self.source_plane_metadata_count - 1}; got "
                f"{invalid_indices!r}."
            )
        if len(normalized_indices) == 1:
            return self.for_source_plane(normalized_indices[0])
        return self.with_source_provenance(
            self.source_provenance.for_source_planes(normalized_indices)
        ).replace_fields(
            source_plane_intensity_scales=_tuple_values_at_indices(
                self.source_plane_intensity_scales,
                normalized_indices,
            ),
            source_plane_dtypes=_tuple_values_at_indices(
                self.source_plane_dtypes,
                normalized_indices,
            ),
            unit_interval_intensity=(
                None
                if self.unit_interval_intensity is None
                else self.unit_interval_intensity.for_source_planes(normalized_indices)
            ),
        )

    def project_declared_source_image(
        self,
        payload: "ImagePayload",
        source_image_name: str,
    ) -> "ImagePayload":
        """Project pixels and metadata to one exact declared source image."""

        source_plane_selection = self.source_provenance.source_plane_selection(
            source_image_name
        )
        if source_plane_selection is None:
            raise ValueError(
                f"Image metadata does not represent declared source image "
                f"{source_image_name!r}; represented names are "
                f"{self.source_provenance.represented_source_image_names!r}, "
                "with provenance planes "
                f"{self.source_image_provenance_planes.identity!r}."
            )
        return self.project_source_planes(payload, source_plane_selection)

    def project_source_planes(
        self,
        payload: "ImagePayload",
        source_plane_selection: tuple[int, ...],
    ) -> "ImagePayload":
        """Project selected provenance planes through their declared pixel axis."""
        if not source_plane_selection:
            return self.attach_to(payload)
        complete_source_axis = tuple(range(self.source_provenance.source_plane_count))
        if self.plane_axis is None:
            if source_plane_selection == complete_source_axis:
                return self.attach_to(payload)
            channel_axis = self.axis_index(ColourAxis, payload)
            if channel_axis is not None:
                if len(source_plane_selection) != 1:
                    raise ValueError(
                        "Declared source-image channel projection requires exactly "
                        f"one channel; got source planes {source_plane_selection!r} "
                        "for the requested source selection."
                    )
                return self.project_channel_payload(
                    payload,
                    payload.data,
                    source_plane_selection[0],
                    channel_axis=channel_axis,
                )
            raise ValueError(
                "Declared source-image payload projection requires a declared "
                "plane or channel axis."
            )
        if self.plane_axis not in (
            RuntimePlaneAxis.RUNTIME_SLICE,
            RuntimePlaneAxis.SOURCE_BINDING,
        ):
            raise ValueError(
                "Source-image identity projection requires a runtime-slice, "
                "source-binding, or channel axis."
            )
        axis_projection = RuntimePlaneAxisValueProjection.preserve(
            axis=self.plane_axis,
            axis_size=self.source_provenance.source_plane_count,
            source_aliases=self.source_image_names,
        )
        axis_projection.validate_shape(
            payload.geometry.shape,
            value_name="Declared source-image payload",
        )
        if source_plane_selection == complete_source_axis:
            return self.attach_to(payload)

        from openhcs.core.aligned_image_payload import stack_image_payloads

        projected_planes = tuple(
            payload.value_for_slice(axis_projection.selected_plane(plane_index))
            for plane_index in source_plane_selection
        )
        if len(projected_planes) == 1:
            return projected_planes[0]
        return stack_image_payloads(
            projected_planes,
            metadata_mode=ImagePayloadMetadataCompositionMode.for_plane_axis(
                self.plane_axis
            ),
        )

    def with_indexed_source_plane_provenance(
        self,
        expected_plane_count: int | None,
    ) -> "ImagePayloadMetadata":
        """Expand scalar source-plane metadata into per-plane provenance."""
        source_provenance = SourcePlaneIndexedProvenanceExpansion(
            self.source_provenance,
            expected_plane_count=expected_plane_count,
        ).expanded()
        if (
            source_provenance is self.source_provenance
            or source_provenance == self.source_provenance
        ):
            return self
        return self.with_source_provenance(source_provenance)

    def for_grouped_source_plane_projection(
        self,
        *,
        source_plane_indices: tuple[int, ...] | None,
        runtime_plane_index: int,
        runtime_plane_count: int | None = None,
    ) -> "ImagePayloadMetadata":
        """Return metadata for a runtime plane that may group source planes."""
        metadata = self.with_indexed_source_plane_provenance(runtime_plane_count)
        if source_plane_indices is None:
            return metadata.for_source_plane(runtime_plane_index)
        if len(source_plane_indices) == 1:
            return metadata.for_source_plane(source_plane_indices[0])
        if not source_plane_indices:
            if metadata.has_plane_specific_values:
                raise ValueError(
                    "Cannot assign one image metadata record to a runtime plane "
                    "that represents multiple source planes: "
                    f"{source_plane_indices!r}."
                )
            return metadata
        return metadata.for_source_planes(source_plane_indices)



    def without_spatial_domain(self) -> "ImagePayloadMetadata":
        """Return metadata with invalidated source-spatial placement removed."""
        return self.replace_fields(
            source_spatial_domain=SourceSpatialDomain(),
            source_voxel_spacing=self.source_voxel_spacing,
            physical_border_edges_yx=None,
            mask_defines_border=None,
        )

    def object_label_source_spatial_domain(self) -> SourceSpatialDomain:
        """Return this metadata's object-label source-image coordinate domain."""
        return self.source_spatial_domain.with_value_name(
            OBJECT_LABEL_SOURCE_SPATIAL_VALUE_NAME,
        )

    def _source_spatial_context_fields(
        self,
        source: "ImagePayloadMetadata",
    ) -> dict[str, Any]:
        spatial_domain = self.source_spatial_domain.with_missing_from(
            source.source_spatial_domain
        )
        return {
            "source_spatial_domain": spatial_domain,
            "source_voxel_spacing": self.source_voxel_spacing.with_missing_from(
                source.source_voxel_spacing
            ),
            "physical_border_edges_yx": (
                self.physical_border_edges_yx
                if self.physical_border_edges_yx is not None
                else source.physical_border_edges_yx
            ),
            "mask_defines_border": (
                self.mask_defines_border
                if self.mask_defines_border is not None
                else source.mask_defines_border
            ),
        }

    def with_source_spatial_context_from(
        self,
        source: "ImagePayloadMetadata",
    ) -> "ImagePayloadMetadata":
        """Fill missing source-image geometry without changing provenance."""
        return self.replace_fields(**self._source_spatial_context_fields(source))

    def with_source_context_from(
        self,
        source: "ImagePayloadMetadata",
    ) -> "ImagePayloadMetadata":
        """Fill missing source-image identity and spatial context from a source."""
        fallback_provenance = source.source_provenance
        # Scalar context cannot collapse coordinates that vary across this
        # payload's represented source planes, including runtime stacks.
        varying = self.source_provenance.varying_plane_component_values(
            AxisFamily.active().axes
        )
        if varying:
            fallback_provenance = fallback_provenance.with_source_component_metadata(
                {
                    key: value
                    for key, value in (
                        fallback_provenance.source_component_metadata or {}
                    ).items()
                    if key not in varying
                }
            )
        source_provenance = self.source_provenance.with_missing_from(
            fallback_provenance
        )
        axes = self.axes if self.axes.has_values else source.axes
        plane_axis = self.plane_axis
        if plane_axis is None:
            plane_axis = source.plane_axis
        elif source.plane_axis is not None and source.plane_axis is not plane_axis:
            raise ValueError(
                "Cannot combine image metadata with conflicting plane axes: "
                f"{plane_axis.value!r} != {source.plane_axis.value!r}."
            )
        return self.replace_fields(
            source_provenance=source_provenance,
            **self._source_spatial_context_fields(source),
            axes=axes,
            plane_axis=plane_axis,
        )

    def _missing_intensity_fields(
        self,
        source: "ImagePayloadMetadata",
    ) -> dict[str, Any]:
        return {
            "intensity_scale": (
                self.intensity_scale
                if self.intensity_scale is not None
                else source.intensity_scale
            ),
            "source_dtype": (
                self.source_dtype
                if self.source_dtype is not None
                else source.source_dtype
            ),
            "unit_interval_intensity": (
                self.unit_interval_intensity
                if self.unit_interval_intensity is not None
                else source.unit_interval_intensity
            ),
            "source_plane_intensity_scales": (
                self.source_plane_intensity_scales
                or source.source_plane_intensity_scales
            ),
            "source_plane_dtypes": (
                self.source_plane_dtypes or source.source_plane_dtypes
            ),
        }

    def with_missing_intensity_from(
        self,
        source: "ImagePayloadMetadata",
    ) -> "ImagePayloadMetadata":
        """Fill missing pixel-type and intensity metadata from a source payload."""
        return self.replace_fields(**self._missing_intensity_fields(source))

    def with_source_provenance(
        self,
        source_provenance: SourceImageProvenance,
    ) -> "ImagePayloadMetadata":
        """Return metadata with source-image provenance replaced atomically."""
        return self.replace_fields(source_provenance=source_provenance)

    def with_source_component_metadata(
        self,
        source_component_metadata: SourceComponentMetadata | None,
    ) -> "ImagePayloadMetadata":
        """Return metadata with only scalar source component metadata changed."""
        return self.with_source_provenance(
            self.source_provenance.with_source_component_metadata(
                source_component_metadata
            )
        )

    def physical_border_edges_for_shape(
        self,
        image_shape_yx: Sequence[int],
    ) -> tuple[bool, bool, bool, bool]:
        """Return which local image edges are true source-image edges.

        Edge tuple order is ``(top, bottom, left, right)``. Missing spatial
        metadata means the current image is treated as the full physical image,
        preserving historical behavior for plain arrays.
        """
        if self.physical_border_edges_yx is not None:
            return tuple(bool(edge) for edge in self.physical_border_edges_yx)
        return self.source_spatial_domain.physical_border_edges_for_shape(
            image_shape_yx
        )

    def with_spatial_crop(
        self,
        *,
        input_shape_yx: Sequence[int],
        output_shape_yx: Sequence[int],
        offset_yx: tuple[int, int],
        physical_border_edges_yx: PhysicalBorderEdgesYX = None,
    ) -> "ImagePayloadMetadata":
        """Return metadata for a crop of this image payload."""
        output_shape = _source_spatial_shape_pair(output_shape_yx, "output_shape_yx")
        spatial_domain = self.source_spatial_domain.with_spatial_crop(
            input_shape_yx=input_shape_yx,
            output_shape_yx=output_shape_yx,
            offset_yx=offset_yx,
        )
        if physical_border_edges_yx is None:
            physical_border_edges_yx = spatial_domain.physical_border_edges_for_shape(
                output_shape
            )
        return self.replace_fields(
            source_spatial_domain=spatial_domain,
            physical_border_edges_yx=tuple(
                bool(edge) for edge in physical_border_edges_yx
            ),
        )

    def with_spatial_resize(
        self,
        output_shape_yx: Sequence[int],
    ) -> "ImagePayloadMetadata":
        """Return metadata in the local coordinate domain created by a resize."""

        return self.replace_fields(
            source_spatial_domain=self.source_spatial_domain.with_spatial_resize(
                output_shape_yx
            ),
            physical_border_edges_yx=(True, True, True, True),
            mask_defines_border=None,
        )

    def with_materialized_source_domain(
        self,
        target_domain: SourceSpatialDomain,
    ) -> "ImagePayloadMetadata":
        """Return metadata after pixels are expanded to source-image XY."""
        return self.replace_fields(
            source_spatial_domain=(
                self.source_spatial_domain.as_materialized_source_domain(target_domain)
            ),
            physical_border_edges_yx=(True, True, True, True),
        )


class ImagePayload(RuntimeArrayPayload, RuntimeSliceProjectableValue, SpatiallyPlacedValue):
    """A tensor payload: pixels with their metadata, mask and declared axes.

    Every image value inside the runtime is an ``ImagePayload``. A bare array
    becomes one exactly once, through :meth:`of`, where it enters: a processing
    function's primary argument, a function's return value, a file loader.
    """

    @property
    @abstractmethod
    def data(self) -> Any:
        """Return concrete pixels in the payload's declared image domain."""

    @property
    @abstractmethod
    def metadata(self) -> ImagePayloadMetadata:
        """Return the image metadata attached to this payload."""

    @property
    def mask(self) -> Any | None:
        """Return the validity mask this payload carries, if any."""
        return None

    @property
    def geometry(self) -> ArrayGeometry:
        """Inspect the image domain; structured payloads derive it from slices."""
        return ArrayGeometry.require_from_value(self.data, value_name="Image payload")

    @property
    def memory_type(self) -> str:
        """Return the actual pixel placement; structured payloads may derive it."""
        return detect_memory_type(self.data)

    @property
    def axes(self) -> tuple[AxisSpec, ...]:
        """Return one declared dimension per pixel axis."""
        return self.metadata.payload_axes(self)

    @property
    def inherits_source_axes(self) -> bool:
        """Whether a derived output takes its declared axes from its source."""
        return False

    @property
    def declared_plane_axis(self) -> RuntimePlaneAxis | None:
        return self.metadata.plane_axis

    @property
    def invocation_plane_axis(self) -> RuntimePlaneAxis | None:
        """Return the plane axis a callable invocation iterates over."""
        return self.metadata.plane_axis

    def copied(self, *, memory_type: str, device_id: int | None) -> "ImagePayload":
        """Copy pixels, mask and metadata into an independent buffer."""
        from openhcs.core.memory import stack_runtime_slices

        copied_data = stack_runtime_slices((self.data,), memory_type, device_id)[0]
        mask = self.mask
        copied_mask = (
            None if mask is None
            else stack_runtime_slices((mask,), memory_type, device_id)[0]
        )
        return self.metadata.replace_fields().payload_with(copied_data, copied_mask)

    @classmethod
    def of(cls, value: Any) -> "ImagePayload":
        """Return ``value`` as an image payload, wrapping a bare array once."""
        if isinstance(value, ImagePayload):
            return value
        if isinstance(value, RuntimeSliceProjectableValue):
            raise TypeError(
                f"{type(value).__name__} is a runtime value, not an image payload."
            )
        return PlainImagePayload(value)

    def spatial_adapter(
        self,
        *,
        source_shape_override_yx: tuple[int, int] | None = None,
    ) -> Any:
        """Place this payload in the source domain its metadata declares."""
        from openhcs.core.aligned_image_payload import (
            ImagePayloadSourceSpatialDomainAdapter,
        )

        del source_shape_override_yx
        return ImagePayloadSourceSpatialDomainAdapter.for_payload(self)

    def with_metadata(self, metadata: ImagePayloadMetadata) -> "ImagePayload":
        """Attach ``metadata`` to this payload's existing pixels and mask."""
        return metadata.payload_with(self.data, self.mask)

    def with_pixels(
        self,
        data: Any,
        *,
        mask: Any | None = None,
        metadata: ImagePayloadMetadata | None = None,
    ) -> "ImagePayload":
        """Replace pixels, keeping this payload's mask and metadata unless given."""
        resolved_metadata = self.metadata if metadata is None else metadata
        resolved_mask = project_image_mask_to_data_domain(
            self.mask if mask is None else mask,
            data,
            metadata=resolved_metadata,
        )
        return resolved_metadata.payload_with(data, resolved_mask)

    def mask_for_data(self, data: Any, *, mask: Any | None = None) -> Any | None:
        """Return this payload's mask, or ``mask``, broadcast onto ``data``."""
        source_mask = self.mask if mask is None else mask
        projected_mask = project_image_mask_to_data_domain(
            source_mask, data, metadata=self.metadata,
        )
        if projected_mask is None:
            return None
        return self.metadata.mask_domain(data).broadcast_to_data(projected_mask)

    def slice_payload(
        self,
        data: Any,
        plane_index: int,
        *,
        plane_axis: RuntimePlaneAxis | None = None,
    ) -> "ImagePayload":
        """Attach one source plane of this payload's context to slice pixels."""
        metadata = self.metadata
        if plane_axis is not None:
            plane_axis = RuntimePlaneAxis(plane_axis)
            if metadata.plane_axis is not None and metadata.plane_axis is not plane_axis:
                raise ValueError(
                    "Image slice projection axis conflicts with payload metadata: "
                    f"{plane_axis.value!r} != {metadata.plane_axis.value!r}."
                )
            if metadata.plane_axis is not plane_axis:
                metadata = metadata.replace_fields(plane_axis=plane_axis)
        return ImagePayloadSliceProjector(
            mask=self.mask,
            metadata=metadata,
        ).payload_for_slice(data, plane_index)

    def intensity_scale(self, *, channel_index: int = 0) -> float | None:
        """Return the best semantic intensity scale for these pixels."""
        metadata_scale = self.metadata.intensity_scale_for_source_plane(channel_index)
        if metadata_scale is not None and metadata_scale > 0:
            return float(metadata_scale)
        return image_intensity_scale_for_dtype(self.dtype)

    def normalize_intensity_payload(
        self, *, dtype: Any = None, channel_index: int = 0,
    ) -> "ImagePayload":
        """Normalize through the metadata-owned numerical policy."""
        return self.metadata.normalize_intensity_payload(
            self, dtype=dtype, channel_index=channel_index,
        )

    def project_declared_source(self, source_image_name: str) -> "ImagePayload":
        """Return the pixels of one declared source image this payload represents."""
        return self.metadata.project_declared_source_image(self, source_image_name)

    # -- main-flow outputs ------------------------------------------------------

    @property
    def declares_whole_image_output(self) -> bool:
        """Whether a main-flow output publishes this payload as one whole image."""
        return self.metadata.plane_axis is None or self.metadata.persists_whole_image()

    def keeps_whole_as_single_member(
        self, *, declared_plane_axis: RuntimePlaneAxis | None,
    ) -> bool:
        """Whether this payload, alone in a cohort, is passed on without a new leading axis.

        Only a member that already spans the cohort axis stays whole: a
        persisted whole image (volume), or a member saved with its declared
        plane axis. A member that declares no plane axis is composed on the
        runtime-slice axis exactly as it is in a cohort of several, so the
        rank a callable receives never depends on how many files matched.
        """
        return self.metadata.persists_whole_image() or (
            declared_plane_axis is not None
            and declared_plane_axis is self.metadata.plane_axis
        )

    @property
    def owns_output_surfaces(self) -> bool:
        """Whether this output names its own output surfaces (filename qualifiers)."""
        return False

    def plane_axis_for_output_context(self, context: Any) -> RuntimePlaneAxis | None:
        """Return the plane axis one published output slice was taken along."""
        del context
        return self.metadata.plane_axis

    def main_output_slices(
        self, unstack: Callable[[Any], tuple[Any, ...]],
    ) -> tuple[tuple["ImagePayload", Any], ...]:
        """Split a main-flow output into published slices, each with its context.

        ``unstack`` splits raw pixels along the leading axis in the plan's
        output memory domain; it is used when no runtime-slice axis is declared.
        A context of None lets the runtime derive it from the step's outputs.
        """
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        projection = RuntimeSliceProjection.preserved_context_for_value(self)
        if projection is not None:
            return tuple(
                (self.value_for_slice(projection.selected_plane(index)), None)
                for index in range(projection.axis_size)
            )
        from openhcs.core.aligned_image_payload import unstack_image_payload_context

        return tuple(
            (payload, None)
            for payload in unstack_image_payload_context(
                self,
                unstack(self.data),
                default_plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            )
        )

    def output_stack_copy(
        self,
        projected_outputs: Sequence[tuple[Any, Any]],
        *,
        memory_type: str,
        device_id: int | None,
    ) -> "ImagePayload | None":
        """Return an independent buffer for the published output stack."""
        del projected_outputs
        if self.declares_whole_image_output:
            return self.copied(memory_type=memory_type, device_id=device_id)
        return self

    # -- derived image outputs ------------------------------------------------

    @property
    def keeps_own_source_context(self) -> bool:
        """Whether this payload, returned as an output, already owns its source context."""
        return False

    def requires_output_plane_contextualization(
        self,
        output: "ImagePayload",
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        """Whether an output derived from this source must bind an undeclared axis."""
        del output, plane_projection
        return False

    def fill_output_source_context(self, output: "ImagePayload") -> "ImagePayload":
        """Fill an output's missing source context from this source."""
        output_metadata = output.metadata
        contextualized = output_metadata.with_source_context_from(
            self.metadata
        ).attach_source_context_to(output)
        if contextualized.metadata == output_metadata:
            return output
        return contextualized

    def contextualize_image_output(
        self,
        output: "ImagePayload",
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> "ImagePayload":
        """Attach this source's image context to an output derived from it."""
        if output.keeps_own_source_context:
            return output
        return self.metadata.derive_payload(
            self, output, plane_projection=plane_projection,
        )

    def object_label_output(
        self,
        source: Any,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> Any:
        """Build object labels from these dense label pixels in ``source``'s domain."""
        from openhcs.core.runtime_object_label_building import (
            SourceImageObjectLabelBuildRequest,
        )

        return SourceImageObjectLabelBuildRequest(
            image=source,
            labels=self.data,
            plane_projection=plane_projection,
        ).payload()

    def alignment_slices(self) -> tuple[Any, ...]:
        """Return this payload split along its declared runtime-slice axis."""
        slice_count = self.runtime_slice_count()
        if slice_count is None:
            return (self,)
        projection = RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=slice_count,
        )
        return tuple(
            self.value_for_slice(projection.selected_plane(index))
            for index in range(slice_count)
        )

    # -- RuntimeSliceProjectableValue -------------------------------------

    def runtime_slice_count(self) -> int | None:
        if self.metadata.plane_axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return None
        geometry = self.geometry
        if geometry.ndim <= AxisFamily.active().payload_spatial_rank:
            from openhcs.core.runtime_slice_projection import (
                RuntimeSliceProjectionDeclarationError,
            )

            raise RuntimeSliceProjectionDeclarationError(
                "Runtime-slice image payload must expose its declared plane axis "
                f"as the leading dimension, got shape {geometry.shape!r}."
            )
        return geometry.shape[0]

    def value_for_slice(self, context: RuntimePlaneAxisValueProjection) -> Any:
        if self.metadata.plane_axis is not context.axis:
            return self
        shape = self.geometry.shape
        context.validate_shape(shape, value_name="Image payload")
        plane_index = context.require_plane_index()
        context.validate_plane_index(plane_index, shape)
        return self.slice_payload(
            self.data[plane_index], plane_index, plane_axis=context.axis,
        )

    def aligned_value(self, resolver: Any) -> Any:
        return resolver.resolve_source_spatial_value(self)


def owned_runtime_value(value: Any) -> Any:
    """Return a function's returned value with a bare array wrapped once.

    Owned values (every ``RuntimeSliceProjectableValue``) and foreign
    non-array values (mappings, rows) are returned unchanged; a bare array
    becomes a ``PlainImagePayload``.
    """
    if isinstance(value, RuntimeSliceProjectableValue) or not is_array_payload(value):
        return value
    return PlainImagePayload(value)


def image_metadata_of(value: Any) -> "ImagePayloadMetadata":
    """Image metadata of a runtime value of any artifact kind.

    Kind-generic layers (projection items, materialization, output recording)
    hold values of every artifact kind. Only image payloads carry image
    metadata; every other kind carries none. This is the one place that
    decision is made until K2 gives each artifact kind its own metadata.
    """
    value = owned_runtime_value(value)
    return value.metadata if isinstance(value, ImagePayload) else ImagePayloadMetadata()


def array_data_of(value: Any) -> Any:
    """Array of an image payload, or a value of another artifact kind unchanged."""
    value = owned_runtime_value(value)
    return value.data if isinstance(value, ImagePayload) else value


@dataclass(frozen=True, slots=True)
class PlainImagePayload(DataBackedRuntimeArrayPayload, ImagePayload):
    """Pixels that carry no metadata and no mask."""

    data: Any

    def __post_init__(self) -> None:
        if isinstance(self.data, RuntimeArrayPayload) or not is_array_payload(self.data):
            raise TypeError(
                "PlainImagePayload wraps bare array pixels, got "
                f"{type(self.data).__name__}."
            )

    @property
    def metadata(self) -> ImagePayloadMetadata:
        return ImagePayloadMetadata()

    @property
    def inherits_source_axes(self) -> bool:
        return True

    @property
    def declares_whole_image_output(self) -> bool:
        """An undeclared main-flow output stacks runtime slices on its leading axis."""
        return False

    def plane_axis_for_output_context(self, context: Any) -> RuntimePlaneAxis:
        del context
        return RuntimePlaneAxis.RUNTIME_SLICE

    def with_data(self, data: Any) -> "PlainImagePayload":
        return type(self)(data)

    def spatial_adapter(
        self,
        *,
        source_shape_override_yx: tuple[int, int] | None = None,
    ) -> Any:
        """Bare pixels sit at the origin of the source domain a caller supplies."""
        from openhcs.core.aligned_image_payload import (
            BareArraySourceSpatialDomainAdapter,
        )

        return BareArraySourceSpatialDomainAdapter.for_array(
            self.data, source_shape_override_yx=source_shape_override_yx,
        )

    def aligned_value(self, resolver: Any) -> Any:
        """Bare pixels declare no source domain to project into."""
        del resolver
        return self


@dataclass(frozen=True, slots=True)
class ImageMetadataPayload(DataBackedRuntimeArrayPayload, ImagePayload):
    """Image data plus metadata, without requiring a validity mask."""

    data: Any
    metadata: ImagePayloadMetadata

    def __post_init__(self) -> None:
        if (
            ArrayGeometry.require_from_value(
                self.data,
                value_name="ImageMetadataPayload.data",
            ).ndim
            == 0
        ):
            raise TypeError(
                "ImageMetadataPayload.data requires array-like image data, "
                f"got {type(self.data).__name__}."
            )
        if not self.metadata.has_values:
            raise ValueError("ImageMetadataPayload.metadata cannot be empty.")

    def with_data(
        self,
        data: Any,
        *,
        metadata: ImagePayloadMetadata | None = None,
    ) -> "ImageMetadataPayload":
        """Return the same metadata attached to replacement data."""
        return type(self)(
            data=data,
            metadata=self.metadata if metadata is None else metadata,
        )


@dataclass(frozen=True, slots=True)
class MaskedImagePayload(DataBackedRuntimeArrayPayload, ImagePayload):
    """Image data plus an authoritative per-pixel validity mask."""

    data: Any
    mask: Any
    metadata: ImagePayloadMetadata = field(default_factory=ImagePayloadMetadata)

    def __post_init__(self) -> None:
        data_geometry = ArrayGeometry.require_from_value(
            self.data,
            value_name="MaskedImagePayload.data",
        )
        if data_geometry.ndim == 0:
            raise TypeError(
                "MaskedImagePayload.data requires array-like image data, "
                f"got {type(self.data).__name__}."
            )
        mask_shape = ArrayGeometry.require_from_value(
            self.mask,
            value_name="MaskedImagePayload.mask",
        ).shape
        if not mask_shape:
            raise TypeError(
                "MaskedImagePayload.mask requires array-like mask data, "
                f"got {type(self.mask).__name__}."
            )
        data_shape = data_geometry.shape
        if not self.metadata.mask_domain(self.data).accepts(mask_shape):
            raise ValueError(
                "MaskedImagePayload.mask shape must match the image spatial "
                f"domain; got mask {mask_shape!r} for image {data_shape!r}."
            )

    def with_data(self, data: Any, mask: Any | None = None) -> "MaskedImagePayload":
        """Return the same semantic image mask attached to replacement data."""
        return type(self)(
            data=data,
            mask=self.mask if mask is None else mask,
            metadata=self.metadata,
        )


def preserved_image_plane_projection(
    value: Any,
    projector: RuntimePlaneAxisProjector,
    source_aliases: tuple[str, ...] = (),
) -> RuntimePlaneAxisValueProjection | None:
    """Resolve a value's declared leading plane axis against one invocation."""

    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    plane_axis = RuntimeSliceProjection.declared_plane_axis(value)
    if plane_axis is None:
        return RuntimeSliceProjection.preserved_context_for_value(value)
    if plane_axis is RuntimePlaneAxis.RUNTIME_SLICE:
        invocation_projection = RuntimePlaneAxisValueProjection.from_projector(
            projector,
            plane_axis,
            source_aliases,
        )
        if (
            invocation_projection is not None
            and invocation_projection.plane_index is not None
        ):
            return None
        payload_projection = RuntimeSliceProjection.preserved_context_for_value(value)
        if payload_projection is None:
            raise ValueError(
                "Runtime-slice image metadata requires a payload with the same "
                "nominal leading axis."
            )
        return payload_projection

    shape = value.geometry.shape
    if len(shape) <= AxisFamily.active().payload_spatial_rank:
        raise ValueError(
            "Source-binding image metadata requires its declared plane axis as "
            f"the leading dimension, got shape {shape!r}."
        )
    axis_size = shape[0]
    return RuntimePlaneAxisValueProjection(
        axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_aliases=source_aliases,
        plane_index=value.metadata.source_provenance.source_alias_plane_index(
            source_aliases,
            axis_size,
        ),
        axis_size=axis_size,
    )


def preserve_declared_image_payload_axis(
    projector: RuntimePlaneAxisProjector,
    output_value: Any,
    *,
    source_payload: Any = None,
) -> RuntimePlaneAxisValueProjection | None:
    """Preserve the plane axis declared by the output, else by its source."""

    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    def declared_axis(value: Any) -> RuntimePlaneAxis | None:
        plane_axis = RuntimeSliceProjection.declared_plane_axis(value)
        if plane_axis is not None:
            return plane_axis
        projection = RuntimeSliceProjection.preserved_context_for_value(value)
        return None if projection is None else projection.axis

    if declared_axis(output_value) is not None:
        owner = output_value
    elif declared_axis(source_payload) is not None:
        owner = source_payload
    else:
        return None
    return preserved_image_plane_projection(owner, projector)


def project_image_mask_to_data_domain(
    mask: Any,
    data: Any,
    *,
    metadata: ImagePayloadMetadata | None = None,
) -> Any | None:
    """Validate a mask against the image domain that ``metadata`` declares.

    Without ``metadata`` the domain is the one ``data`` itself declares.
    """
    if mask is None:
        return None
    if metadata is None:
        metadata = image_metadata_of(data)
    data_array = runtime_array_operand(data)
    candidate = mask_array(mask)
    target = MemoryType(detect_memory_type(data_array))
    candidate = MemoryType(detect_memory_type(candidate)).convert_to(
        candidate, target, target.device_id_of(data_array),
    )
    candidate = target.astype(candidate, bool)
    mask_shape = tuple(candidate.shape)
    mask_domain = metadata.mask_domain(data)
    if mask_domain.accepts(mask_shape):
        return candidate
    raise ValueError(
        f"Mask shape {mask_shape!r} does not match declared image mask domain "
        f"{tuple(sorted(mask_domain.valid_shapes()))!r}."
    )


@dataclass(frozen=True, slots=True)
class ImageMetadataProjection(ABC):
    """Construct one metadata result from nominal source and axis transformations."""

    metadata: ImagePayloadMetadata

    def project(self) -> ImagePayloadMetadata:
        return self.project_axis_metadata(self.project_source_metadata())

    @abstractmethod
    def project_source_metadata(self) -> ImagePayloadMetadata:
        """Select source metadata with this projection's declared ownership."""

    def project_axis_metadata(
        self, metadata: ImagePayloadMetadata
    ) -> ImagePayloadMetadata:
        """Retain declared axes unless a nominal axis capability transforms them."""
        return metadata

    @abstractmethod
    def project_source_provenance(
        self, metadata: ImagePayloadMetadata, provenance: SourceImageProvenance
    ) -> ImagePayloadMetadata:
        """Apply provenance using the result ownership established by source selection."""


@dataclass(frozen=True, slots=True)
class SourcePlaneImageMetadataProjection(ImageMetadataProjection):
    """Select scalar source-image facts without removing an array axis."""

    plane_index: int

    def project_source_metadata(self) -> ImagePayloadMetadata:
        provenance = self.metadata.source_provenance.for_source_plane(self.plane_index)
        return self.metadata.replace_fields(
            intensity_scale=self.metadata.intensity_scale_for_source_plane(
                self.plane_index
            ),
            source_dtype=_tuple_value(
                self.metadata.source_plane_dtypes, self.plane_index
            )
            or self.metadata.source_dtype,
            source_provenance=provenance,
            unit_interval_intensity=self.metadata.project_intensity_proof(
                self.plane_index
            ),
            source_plane_intensity_scales=(),
            source_plane_dtypes=(),
        )

    def project_source_provenance(
        self, metadata: ImagePayloadMetadata, provenance: SourceImageProvenance
    ) -> ImagePayloadMetadata:
        """Normalize the independently owned result created by source selection."""
        metadata.source_provenance = provenance
        metadata.normalize_metadata_fields()
        return metadata


class LeadingPlaneAxisMetadataProjection(ImageMetadataProjection):
    """Remove a declared leading axis while preserving its source contributors."""

    def project_source_metadata(self) -> ImagePayloadMetadata:
        return self.metadata

    def project_axis_metadata(
        self, metadata: ImagePayloadMetadata
    ) -> ImagePayloadMetadata:
        return metadata.without_leading_plane_axis(projection=self)

    def project_source_provenance(
        self, metadata: ImagePayloadMetadata, provenance: SourceImageProvenance
    ) -> ImagePayloadMetadata:
        """Create the standalone result after its axis guards and source derivation."""
        return metadata.replace_fields(source_provenance=provenance)


class LeadingSourcePlaneMetadataProjection(
    SourcePlaneImageMetadataProjection,
    LeadingPlaneAxisMetadataProjection,
):
    """Remove the leading axis of independently owned selected-source metadata."""

    def project_source_metadata(self) -> ImagePayloadMetadata:
        self.metadata.require_leading_plane_axis(
            "Leading source-plane projection requires a declared plane axis."
        )
        return super().project_source_metadata()


@dataclass(frozen=True, slots=True)
class ImagePayloadSliceProjector:
    """Project payload context from a parent image into one child image slice."""

    mask: RuntimeArrayData | None
    metadata: ImagePayloadMetadata

    def payloads_for_slices(
        self,
        slices: Sequence[RuntimeArrayData],
    ) -> list[RuntimeArrayData]:
        """Project each child once, keeping strict batch-mask cardinality."""
        if self.metadata.plane_axis is None:
            if len(slices) != 1:
                raise ValueError(
                    "Image payload produced multiple slices without a declared "
                    "plane axis."
                )
            return [self.metadata.payload_with(slices[0], self.mask)]
        metadata = self.metadata.with_indexed_source_plane_provenance(len(slices))
        masks = self._masks_for_slices(slices) if self.mask is not None else None
        payloads: list[RuntimeArrayData] = []
        for index, slice_data in enumerate(slices):
            slice_metadata = metadata.for_leading_source_plane(index)
            mask = None if masks is None else masks[index]
            if mask is not None and not slice_metadata.mask_domain(slice_data).accepts(
                tuple(np.shape(mask))
            ):
                raise ValueError(
                    "Image payload mask shape must match the selected slice "
                    f"domain; got {tuple(np.shape(mask))!r} for "
                    f"{tuple(np.shape(slice_data))!r}."
                )
            payloads.append(slice_metadata.payload_with(slice_data, mask))
        return payloads

    def _masks_for_slices(
        self,
        slices: Sequence[RuntimeArrayData],
    ) -> tuple[RuntimeArrayData, ...]:
        """Select batch masks only after checking exact leading cardinality."""
        if self.mask is None:
            raise ValueError("Masked slice projection requires a mask payload.")
        mask_array = np.asarray(self.mask, dtype=bool)
        if mask_array.ndim == 0 or mask_array.shape[0] != len(slices):
            raise ValueError(
                "Image payload mask cardinality must exactly match the declared "
                f"plane axis: {mask_array.shape!r} for {len(slices)} slice(s)."
            )
        return tuple(mask_array[index] for index in range(len(slices)))

    def payload_for_slice(
        self,
        data_slice: RuntimeArrayData,
        index: int,
    ) -> RuntimeArrayData:
        """Project one metadata snapshot for both child pixels and mask."""
        metadata = self.metadata.for_leading_source_plane(index)
        mask = self._mask_for_projected_slice(data_slice, index, metadata)
        return metadata.payload_with(data_slice, mask)

    def mask_for_slice(
        self,
        data_slice: RuntimeArrayData,
        index: int,
    ) -> RuntimeArrayData | None:
        """Project a standalone mask through the same scalar slice policy."""
        if self.mask is None:
            return None
        metadata = self.metadata.for_leading_source_plane(index)
        return self._mask_for_projected_slice(data_slice, index, metadata)

    def _mask_for_projected_slice(
        self,
        data_slice: RuntimeArrayData,
        plane_index: int,
        slice_metadata: ImagePayloadMetadata,
    ) -> RuntimeArrayData | None:
        if self.mask is None:
            return None
        mask_array = np.asarray(self.mask)
        if (
            self.metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
            and slice_metadata.mask_domain(data_slice).accepts(mask_array.shape)
        ):
            candidate = mask_array
        else:
            if mask_array.ndim == 0 or plane_index >= mask_array.shape[0]:
                raise ValueError(
                    "Image payload mask does not carry the requested declared "
                    f"slice index {plane_index}; got shape {mask_array.shape!r}."
                )
            candidate = mask_array[plane_index]
        if slice_metadata.mask_domain(data_slice).accepts(
            array_geometry(candidate).shape
        ):
            return candidate
        raise ValueError(
            "Image payload mask cannot be projected into slice domain; "
            f"got mask {mask_array.shape!r} for slice "
            f"{array_geometry(data_slice).shape!r}."
        )


class ImagePayloadMetadataCompositionMode(Enum):
    """Source-provenance topology for composed image metadata."""

    def __new__(
        cls,
        value: str,
        plane_axis: RuntimePlaneAxis,
    ):
        member = object.__new__(cls)
        member._value_ = value
        member._plane_axis = plane_axis
        return member

    STACK = ("stack", RuntimePlaneAxis.RUNTIME_SLICE)
    BUNDLE = ("bundle", RuntimePlaneAxis.SOURCE_BINDING)
    plane_axis = AliasProperty[RuntimePlaneAxis]("_plane_axis")

    @classmethod
    def for_plane_axis(
        cls,
        plane_axis: RuntimePlaneAxis,
    ) -> "ImagePayloadMetadataCompositionMode":
        """Return the unique composition operation that creates an axis."""

        matches = tuple(mode for mode in cls if mode.plane_axis is plane_axis)
        if len(matches) != 1:
            raise ValueError(
                f"No unique image composition mode owns {plane_axis.value!r}."
            )
        return matches[0]

    def preserves_plane_topology(
        self,
        plane_axis: RuntimePlaneAxis | None,
    ) -> bool:
        """Return whether composition retains an existing runtime-plane axis."""

        return plane_axis is self.plane_axis or (
            plane_axis is None and self.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
        )


@dataclass(slots=True)
class _ImagePayloadMetadataComposer:
    """Stateful implementation for composing image metadata on a leading axis."""

    payloads: tuple["ImagePayload", ...]
    mode: ImagePayloadMetadataCompositionMode = (
        ImagePayloadMetadataCompositionMode.STACK
    )
    source_metadata_override: Sequence[ImagePayloadMetadata] | None = None
    metadata_type: type[ImagePayloadMetadata] = ImagePayloadMetadata

    def __post_init__(self) -> None:
        self.payloads = tuple(self.payloads)
        if not self.payloads:
            raise ValueError("Image metadata composition payloads cannot be empty.")
        if self.source_metadata_override is None:
            return
        self.source_metadata_override = tuple(self.source_metadata_override)
        if len(self.source_metadata_override) != len(self.payloads):
            raise ValueError(
                "Image metadata composition source metadata must match payload count."
            )

    @property
    def source_metadata(self) -> tuple[ImagePayloadMetadata, ...]:
        if self.source_metadata_override is None:
            return tuple(payload.metadata for payload in self.payloads)
        return tuple(self.source_metadata_override)

    @staticmethod
    def source_plane_metadata_for_payload(
        metadata: ImagePayloadMetadata,
    ) -> ImagePayloadMetadata:
        """Return metadata for one payload on the newly composed leading axis."""
        if metadata.plane_axis is not None:
            return metadata
        if metadata.source_provenance.source_plane_count == 1:
            return metadata.for_source_plane(0)
        return metadata

    def compose(self) -> ImagePayloadMetadata:
        metadata_by_payload = self.source_metadata
        if not any(metadata.has_values for metadata in metadata_by_payload):
            return self.metadata_type(plane_axis=self.mode.plane_axis)
        source_metadata_by_payload = tuple(
            self.source_plane_metadata_for_payload(metadata)
            for metadata in metadata_by_payload
        )
        compose_provenance = (
            SourceImageProvenance.stack
            if self.mode is ImagePayloadMetadataCompositionMode.STACK
            else SourceImageProvenance.bundle
        )
        source_provenance = compose_provenance(
            tuple(
                metadata.source_provenance for metadata in source_metadata_by_payload
            ),
            scalar_sources=tuple(
                metadata.source_provenance for metadata in metadata_by_payload
            ),
            preserve_single_topology=(
                len(source_metadata_by_payload) == 1
                and self.mode.preserves_plane_topology(
                    source_metadata_by_payload[0].plane_axis
                )
            ),
        )
        common_source_voxel_spacing = self.common_metadata_value(
            metadata.source_voxel_spacing
            for metadata in metadata_by_payload
            if metadata.source_voxel_spacing.has_values
        )
        if common_source_voxel_spacing is None:
            common_source_voxel_spacing = SourceVoxelSpacing()
        return self.metadata_type(
            source_provenance=source_provenance,
            source_plane_intensity_scales=tuple(
                metadata.intensity_scale for metadata in source_metadata_by_payload
            ),
            source_plane_dtypes=tuple(
                metadata.source_dtype for metadata in source_metadata_by_payload
            ),
            unit_interval_intensity=self.composed_unit_interval_intensity(
                source_metadata_by_payload
            ),
            source_spatial_domain=SourceSpatialDomain.common_from_domains(
                metadata.source_spatial_domain for metadata in metadata_by_payload
            ),
            source_voxel_spacing=common_source_voxel_spacing,
            physical_border_edges_yx=self.common_metadata_value(
                metadata.physical_border_edges_yx for metadata in metadata_by_payload
            ),
            mask_defines_border=self.common_metadata_value(
                metadata.mask_defines_border for metadata in metadata_by_payload
            ),
            axes=PayloadAxes.common_after_stacking(
                (metadata.axes, payload.geometry.ndim)
                for payload, metadata in zip(
                    self.payloads, metadata_by_payload, strict=True,
                )
            ),
            plane_axis=self.mode.plane_axis,
        )

    @staticmethod
    def composed_unit_interval_intensity(
        metadata_records: Sequence[ImagePayloadMetadata],
    ) -> ImageUnitIntervalIntensityMetadata | None:
        """Compose only unit-interval proof state authored by an input payload."""

        if not any(
            metadata.unit_interval_intensity is not None
            for metadata in metadata_records
        ):
            return None
        return ImageUnitIntervalIntensityMetadata(
            source_plane_scales=tuple(
                metadata.unit_interval_intensity_scale for metadata in metadata_records
            )
        )

    @staticmethod
    def common_metadata_value(
        values: Iterable[MetadataValueT | None],
    ) -> MetadataValueT | None:
        values_tuple = tuple(values)
        present = tuple(value for value in values_tuple if value is not None)
        if not present:
            return None
        first = present[0]
        if all(value == first for value in present):
            return first
        return None


def image_intensity_scale_for_dtype(dtype: Any) -> float | None:
    """Return the conventional full-scale intensity for a pixel dtype."""
    normalized = np.dtype(dtype)
    if np.issubdtype(normalized, np.bool_):
        return 1.0
    if np.issubdtype(normalized, np.integer):
        return float(np.iinfo(normalized).max)
    return None


def _tuple_value(values: tuple[Any, ...], index: int) -> Any | None:
    if 0 <= index < len(values):
        return values[index]
    return None


def _tuple_values_at_indices(
    values: tuple[Any, ...],
    indices: tuple[int, ...],
) -> tuple[Any, ...]:
    """Project optional plane-specific tuple values without inventing records."""
    if not values:
        return ()
    return tuple(_tuple_value(values, index) for index in indices)


@dataclass(frozen=True, slots=True)
class ImageMaskDomain:
    """Accepted mask shapes for an explicitly declared image data domain.

    A mask may omit every declared non-spatial axis (it then applies to each
    value along them); a source-binding stack may share one mask over the
    axes its spatial domain places.
    """

    data_shape: tuple[int, ...]
    declared_axes: tuple[int, ...] = ()
    plane_axis: RuntimePlaneAxis | None = None
    placement_axes: tuple[int, ...] | None = None

    def __post_init__(self) -> None:
        data_shape = tuple(int(axis_size) for axis_size in self.data_shape)
        object.__setattr__(self, "data_shape", data_shape)
        declared_axes = tuple(sorted(int(axis) for axis in self.declared_axes))
        if any(axis < 0 or axis >= len(data_shape) for axis in declared_axes):
            raise ValueError(
                f"Image mask declared axes {declared_axes!r} are invalid for "
                f"shape {data_shape!r}."
            )
        object.__setattr__(self, "declared_axes", declared_axes)
        placement_axes = self.placement_axes
        if placement_axes is None:
            return
        if len(set(placement_axes)) != len(placement_axes) or any(
            axis < 0 or axis >= len(data_shape) for axis in placement_axes
        ):
            raise ValueError(
                "Image mask placement axes must be distinct data axes; "
                f"got {placement_axes!r} for shape {data_shape!r}."
            )

    @staticmethod
    def channel_axis_slice(
        value: Any,
        *,
        channel_axis: int,
        channel_index: int,
    ) -> Any:
        geometry = array_geometry(value)
        normalized_axis = channel_axis % geometry.ndim
        slices = [slice(None)] * geometry.ndim
        slices[normalized_axis] = slice(channel_index, channel_index + 1)
        return value[tuple(slices)]

    @classmethod
    def projected_channel_mask(
        cls,
        mask: Any,
        *,
        source_data: Any,
        channel_data: Any,
        channel_index: int,
        channel_axis: int,
    ) -> Any:
        candidate = mask_array(mask)
        candidate = MemoryType(detect_memory_type(candidate)).astype(candidate, bool)
        if candidate.shape != array_geometry(source_data).shape:
            return candidate
        channel_mask = cls.channel_axis_slice(
            candidate,
            channel_axis=channel_axis,
            channel_index=channel_index,
        )
        if array_geometry(channel_mask).shape == array_geometry(channel_data).shape:
            return channel_mask
        squeezed_mask = MemoryType(detect_memory_type(channel_mask)).reshape(
            channel_mask,
            tuple(
                size for axis, size in enumerate(channel_mask.shape)
                if axis != channel_axis % len(channel_mask.shape)
            ),
        )
        if array_geometry(squeezed_mask).shape == array_geometry(channel_data).shape:
            return squeezed_mask
        return channel_mask

    @property
    def shared_spatial_mask_shape(self) -> tuple[int, ...] | None:
        """Return a mask domain shared by declared source-binding planes."""
        if (
            self.plane_axis is not RuntimePlaneAxis.SOURCE_BINDING
            or self.placement_axes is None
        ):
            return None
        return tuple(self.data_shape[axis] for axis in self.placement_axes)

    @property
    def undeclared_shape(self) -> tuple[int, ...] | None:
        """Return the data shape without its declared axes, if any are declared."""
        if not self.declared_axes:
            return None
        return tuple(
            axis_size
            for axis, axis_size in enumerate(self.data_shape)
            if axis not in self.declared_axes
        )

    def accepts(self, mask_shape: tuple[int, ...]) -> bool:
        return mask_shape in self.valid_shapes()

    def valid_shapes(self) -> frozenset[tuple[int, ...]]:
        valid = {self.data_shape}
        if self.undeclared_shape is not None:
            valid.add(self.undeclared_shape)
        if self.shared_spatial_mask_shape is not None:
            valid.add(self.shared_spatial_mask_shape)
        return frozenset(valid)

    def default_mask_shape(self) -> tuple[int, ...]:
        """Return the mask shape this declared image domain uses by default."""
        if self.shared_spatial_mask_shape is not None:
            return self.shared_spatial_mask_shape
        if self.undeclared_shape is None:
            return self.data_shape
        return self.undeclared_shape

    def broadcast_to_data(self, mask: Any) -> Any:
        """Broadcast a valid mask across its declared non-spatial axes."""
        candidate = mask_array(mask)
        memory_type = MemoryType(detect_memory_type(candidate))
        candidate = memory_type.astype(candidate, bool)
        mask_shape = tuple(candidate.shape)
        if mask_shape == self.data_shape:
            return candidate
        if mask_shape == self.shared_spatial_mask_shape:
            if self.placement_axes is None:
                raise AssertionError("Shared spatial mask axes are missing.")
            broadcast_shape = [1] * len(self.data_shape)
            for mask_axis, data_axis in enumerate(self.placement_axes):
                broadcast_shape[data_axis] = mask_shape[mask_axis]
            return memory_type.broadcast_to(
                memory_type.reshape(candidate, tuple(broadcast_shape)),
                self.data_shape,
            )
        if self.undeclared_shape is None or mask_shape != self.undeclared_shape:
            raise ValueError(
                f"Mask shape {mask_shape!r} is not valid for image "
                f"shape {self.data_shape!r}."
            )
        broadcast_shape = list(mask_shape)
        for axis in self.declared_axes:
            broadcast_shape.insert(axis, 1)
        return memory_type.broadcast_to(
            memory_type.reshape(candidate, tuple(broadcast_shape)),
            self.data_shape,
        )
