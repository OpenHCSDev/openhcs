"""Nominal runtime image payload values and metadata."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import (
    Iterable,
    Sequence,
)
from dataclasses import dataclass, field, fields
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

import numpy as np
from arraybridge import ArrayGeometry, MemoryType, detect_memory_type
from python_introspect import dataclass_from_mapping
from zmqruntime.viewer_protocol import (
    ViewerWireField,
    ViewerWireMapping,
    ViewerWirePayload,
)
from openhcs.serialization.json import to_jsonable
from collections.abc import Mapping

from openhcs.core.alias_property import AliasProperty
from openhcs.core.runtime_array_values import (
    DataBackedRuntimeArrayPayload,
    RuntimeArrayData,
    is_array_payload,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
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
)
from openhcs.core.source_spatial_domain import (
    _spatial_shape_pair as _source_spatial_shape_pair,
)
from openhcs.core.axes import AxisFamily

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
    declarations consumed by the original metadata codecs.
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
        """Admit the declared plane layout before applying per-plane scales."""

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
        """Admit one real-valued intensity conversion before touching its domain."""
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
        data = image_payload_data(payload)
        array = data if is_array_payload(data) else np.asarray(data)
        memory_type = MemoryType(detect_memory_type(array))
        target_dtype = self.normalization_dtype(
            memory_type.canonical_dtype_name(array.dtype), dtype,
        )
        if target_dtype is None:
            return payload
        if self.has_normalized_intensity:
            return self.payload_with(
                memory_type.astype(array, target_dtype), image_payload_mask(payload),
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
                image_payload_mask(payload),
            )
        normalized, proof_scale = self.normalized_intensity_array(
            array, target_dtype=target_dtype,
            scale=self.intensity_scale_for_source_plane(channel_index),
        )
        return self.with_unit_interval_intensity_scale(proof_scale).payload_with(
            normalized, image_payload_mask(payload),
        )

    @staticmethod
    def normalization_scale(
        source_dtype: np.dtype, scale: float | None,
    ) -> tuple[float | None, int | None]:
        """Admit one current-domain divisor and its integer acquisition proof."""
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
        metadata = tuple(image_payload_metadata(payload) for payload in payloads)
        normalized = tuple(record.has_normalized_intensity for record in metadata)
        if not any(normalized) or all(normalized):
            return tuple(payloads)
        return tuple(
            record.normalize_intensity_payload(payload)
            for record, payload in zip(metadata, payloads, strict=True)
        )


class ImagePayloadAxisFields(ABC):
    """Declared plane/channel geometry shared by image metadata capabilities.

    Concrete metadata owns the stored declarations. This capability owns their
    validation and derived array-axis views, independent of source identity and
    numerical intensity conversion.
    """

    @property
    @abstractmethod
    def source_channel_axis(self) -> int | None: ...

    @property
    @abstractmethod
    def plane_axis(self) -> RuntimePlaneAxis | None: ...

    def require_scalar_source_plane(self) -> None:
        """Require source metadata for one scalar grayscale image plane."""
        if self.plane_axis is not None:
            raise ValueError("Exported source planes require scalar image metadata.")
        if self.source_channel_axis is not None:
            raise ValueError("Exported Z planes cannot carry an undeclared color axis.")

    def require_leading_plane_axis(self, message: str) -> None:
        """Require axis presence before later ordered projection validation."""
        if self.plane_axis is None:
            raise ValueError(message)

    def validate_source_channel_axis(self) -> None:
        """Validate the authored channel declaration before transforming axes."""
        if self.source_channel_axis is not None and (
            not isinstance(self.source_channel_axis, int)
            or isinstance(self.source_channel_axis, bool)
        ):
            raise TypeError(
                "ImagePayloadMetadata.source_channel_axis must be int or None."
            )

    def normalized_source_channel_axis(self, data: Any) -> int | None:
        """Return this declared channel axis normalized for ``data``."""
        if self.source_channel_axis is None:
            return None
        ndim = image_payload_geometry(data).ndim
        axis = self.source_channel_axis
        normalized = axis if axis >= 0 else ndim + axis
        if normalized < 0 or normalized >= ndim:
            raise ValueError(
                f"Source channel axis {axis} is invalid for payload rank {ndim}."
            )
        return normalized

    def non_channel_axes(self, data: Any) -> tuple[int, ...]:
        """Return pixel axes excluding this payload's declared channel axis."""
        ndim = image_payload_geometry(data).ndim
        channel_axis = self.normalized_source_channel_axis(data)
        return tuple(axis for axis in range(ndim) if axis != channel_axis)

    def spatial_axes_yx(self, data: Any) -> tuple[int, int] | None:
        """Return Y/X axes after excluding the declared channel axis."""
        candidate_axes = self.non_channel_axes(data)
        if len(candidate_axes) < 2:
            return None
        return candidate_axes[-2], candidate_axes[-1]

    def is_declared_source_channel_plane(self, data: Any) -> bool:
        """Return whether this payload declares one channel-bearing image plane."""
        if self.normalized_source_channel_axis(data) is None:
            return False
        return self.plane_axis is None

    def is_declared_source_channel_stack(self, data: Any) -> bool:
        """Return whether this payload declares a plane stack with a channel axis."""
        if self.normalized_source_channel_axis(data) is None:
            return False
        return self.plane_axis is not None

    def spatial_shape_yx(self, data: Any) -> tuple[int, int] | None:
        """Return Y/X shape using only declared channel-axis semantics."""
        axes = self.spatial_axes_yx(data)
        if axes is None:
            return None
        shape = image_payload_geometry(data).shape
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
        self.validate_source_channel_axis()
        self.channel_axis_without_leading_plane()

    def channel_axis_without_leading_plane(self) -> int | None:
        """Validate distinct plane/channel axes and derive the scalar channel."""
        source_channel_axis = self.source_channel_axis
        if source_channel_axis == 0:
            raise ValueError(
                "Image metadata cannot declare the same leading axis as both "
                "plane and channel."
            )
        if source_channel_axis is not None and source_channel_axis > 0:
            source_channel_axis -= 1
        return source_channel_axis


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
    source_channel_axis: int | None = field(
        default=None, metadata={ViewerWireField.IMAGE_METADATA: True}
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
        """Restore all declared metadata fields through their canonical codecs."""
        decoded = dict(values)
        if "source_provenance" in decoded:
            decoded["source_provenance"] = SourceImageProvenance.from_mapping(
                decoded["source_provenance"]
            )
        if "source_spatial_domain" in decoded:
            decoded["source_spatial_domain"] = SourceSpatialDomain.from_mapping(
                decoded["source_spatial_domain"]
            )
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
        self.validate_source_channel_axis()
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
                self.source_channel_axis is not None,
                self.plane_axis is not None,
            )
        )

    def attach_to(self, payload: Any) -> RuntimeArrayData:
        """Attach this metadata to an existing image payload."""
        if isinstance(payload, ImagePayloadMetadataCarrier):
            return payload.with_metadata(self)
        return self.payload_with(
            image_payload_data(payload), image_payload_mask(payload),
        )

    def attach_source_context_to(self, payload: Any) -> RuntimeArrayData:
        """Attach source context while retaining the payload's declared array axes."""

        payload_metadata = image_payload_metadata(payload)
        return self.replace_fields(
            source_channel_axis=payload_metadata.source_channel_axis,
            plane_axis=payload_metadata.plane_axis,
        ).attach_to(payload)

    def derive_payload(
        self,
        source_payload: RuntimeArrayData | None,
        data: RuntimeArrayData,
        *,
        plane_projection: RuntimePlaneAxisValueProjection | None = None,
    ) -> RuntimeArrayData:
        """Project this source metadata and mask onto derived image data."""
        source_shape_yx = self.spatial_shape_yx(source_payload)
        output_shape_yx = image_payload_metadata(data).spatial_shape_yx(data)
        same_spatial_domain = (
            source_shape_yx is not None
            and output_shape_yx is not None
            and source_shape_yx == output_shape_yx
        )
        output_metadata = image_payload_metadata(data)
        metadata = self._derived_metadata(data, plane_projection)
        output_declares_spatial_domain = (
            isinstance(data, ImagePayloadMetadataCarrier)
            and output_metadata.source_spatial_domain.has_values
        )
        if not same_spatial_domain and not output_declares_spatial_domain:
            metadata = metadata.without_spatial_domain()
        output_mask = image_payload_mask(data)
        if output_mask is None and same_spatial_domain:
            output_mask = project_image_mask_to_data_domain(
                image_payload_mask(source_payload),
                image_payload_data(data),
                metadata=metadata,
            )
        return metadata.payload_with(image_payload_data(data), output_mask)

    def _derived_metadata(
        self,
        data: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> "ImagePayloadMetadata":
        output_metadata = image_payload_metadata(
            data
        ).with_indexed_source_plane_provenance(None)
        source_metadata = self.with_indexed_source_plane_provenance(None)
        output_metadata_is_authoritative = (
            isinstance(data, ImagePayloadMetadataCarrier) and output_metadata.has_values
        )
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
                    image_payload_geometry(
                        data,
                        value_name="Derived image payload",
                    ).shape,
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
        # Admit current source fields before deriving the output. This private
        # snapshot owns its stripped axes; no intermediate image is published.
        source_context = source_metadata.replace_fields(plane_axis=None)
        if isinstance(data, ImagePayloadMetadataCarrier):
            source_context.source_channel_axis = None
        # Admit current output calibration and geometry before replacing stale
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
            source_channel_axis=(
                metadata.source_channel_axis
                if metadata.source_channel_axis is not None
                else source_context.source_channel_axis
            ),
            plane_axis=declared_output_axis,
            **metadata._missing_intensity_fields(source_metadata),
        )

    def project_channel_payload(
        self,
        source_payload: RuntimeArrayData,
        source_data: Any,
        channel_index: int,
        *,
        channel_data: Any | None = None,
        channel_axis: int = 0,
    ) -> RuntimeArrayData:
        """Project one channel while preserving metadata and mask semantics."""
        if channel_data is None:
            channel_data = ImageMaskDomain.channel_axis_slice(
                source_data,
                channel_axis=channel_axis,
                channel_index=channel_index,
            )
        source_channel_axis = self.normalized_source_channel_axis(source_data)
        projected_axis = (
            channel_axis
            % image_payload_geometry(
                source_data,
                value_name="Source image payload",
            ).ndim
        )
        metadata = (
            self.for_source_plane(channel_index)
            if self.has_plane_specific_values
            else self
        )
        if source_channel_axis == projected_axis:
            metadata = metadata.without_source_channel_axis()
        mask = image_payload_mask(source_payload)
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
        payload: RuntimeArrayData,
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
                image_payload_geometry(
                    payload,
                    value_name="Source-identified image payload",
                ).shape,
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
        payloads: Sequence[RuntimeArrayData],
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


    def spatial_axes(self, data: Any) -> tuple[int, ...]:
        """Project the declared intrinsic spatial domain onto current pixels.

        Source cohorts can add leading SITE, time or binding axes without
        adding a physical dimension. Channel axes likewise do not belong to
        the spatial domain. Intrinsic Y/X or Z/Y/X axes are the trailing
        non-channel axes, including an assembled Z cohort admitted by the
        original volume-domain owner.
        """
        candidate_axes = self.non_channel_axes(data)
        spatial_rank = self.source_spatial_domain.spatial_rank
        if len(candidate_axes) < spatial_rank:
            raise ValueError(
                f"Declared spatial rank {spatial_rank} exceeds payload rank "
                f"{image_payload_geometry(data).ndim} after excluding its "
                "source channel axis."
            )
        return candidate_axes[-spatial_rank:]

    def mask_domain(self, data: Any) -> "ImageMaskDomain":
        """Return the mask domain declared for this payload."""
        spatial_axes_yx = (
            self.spatial_axes_yx(data)
            if self.source_spatial_domain.source_shape_yx is not None
            else None
        )
        return ImageMaskDomain(
            image_payload_geometry(data).shape,
            self.normalized_source_channel_axis(data),
            self.plane_axis,
            spatial_axes_yx,
        )

    def without_source_channel_axis(self) -> "ImagePayloadMetadata":
        """Return metadata after an operation collapses the source channel axis."""
        return self.replace_fields(source_channel_axis=None)

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
        source_channel_axis = self.channel_axis_without_leading_plane()
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
        projected.source_channel_axis = source_channel_axis
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

    def payload_with(self, data: Any, mask: Any | None = None) -> Any:
        """Return image payload data carrying this metadata."""
        if mask is None and self.has_values:
            return ImageMetadataPayload(data=data, metadata=self)
        if mask is None:
            return data
        return MaskedImagePayload(data=data, mask=mask, metadata=self)

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
        payload: RuntimeArrayData,
        source_image_name: str,
    ) -> RuntimeArrayData:
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
        payload: RuntimeArrayData,
        source_plane_selection: tuple[int, ...],
    ) -> RuntimeArrayData:
        """Project selected provenance planes through their declared pixel axis."""
        if not source_plane_selection:
            return self.attach_to(payload)
        complete_source_axis = tuple(range(self.source_provenance.source_plane_count))
        if self.plane_axis is None:
            if source_plane_selection == complete_source_axis:
                return self.attach_to(payload)
            channel_axis = self.normalized_source_channel_axis(payload)
            if channel_axis is not None:
                if len(source_plane_selection) != 1:
                    raise ValueError(
                        "Declared source-image channel projection requires exactly "
                        f"one channel; got source planes {source_plane_selection!r} "
                        "for the requested source selection."
                    )
                return self.project_channel_payload(
                    payload,
                    image_payload_data(payload),
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
            image_payload_geometry(
                payload,
                value_name="Declared source-image payload",
            ).shape,
            value_name="Declared source-image payload",
        )
        if source_plane_selection == complete_source_axis:
            return self.attach_to(payload)

        from openhcs.core.aligned_image_payload import stack_image_payloads
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        projected_planes = tuple(
            RuntimeSliceProjection.value_for_slice(
                payload,
                axis_projection.selected_plane(plane_index),
            )
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
        source_channel_axis = self.source_channel_axis
        if source_channel_axis is None:
            source_channel_axis = source.source_channel_axis
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
            source_channel_axis=source_channel_axis,
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


class ImagePayloadMetadataCarrier(ABC):
    """Nominal contract for image payloads that carry runtime metadata."""

    @abstractmethod
    def image_data(self) -> Any:
        """Return concrete pixels in the payload's declared image domain."""

    def image_geometry(self) -> ArrayGeometry:
        """Inspect the image domain; structured owners may derive it from slices."""
        return ArrayGeometry.require_from_value(
            self.image_data(), value_name="Image payload",
        )

    def image_mask(self) -> Any | None:
        """Return an authoritative validity mask when this owner carries one."""
        return None

    def image_memory_type(self) -> str:
        """Return the actual pixel placement; structured owners may derive it."""
        return detect_memory_type(self.image_data())

    def with_metadata(self, metadata: ImagePayloadMetadata) -> Any:
        """Retarget admitted metadata onto this owner's existing pixels and mask."""
        return metadata.payload_with(self.image_data(), self.image_mask())

    def normalize_intensity_payload(
        self, *, dtype: Any = None, channel_index: int = 0,
    ) -> Any:
        """Normalize through the metadata-owned numerical policy."""
        return self.metadata.normalize_intensity_payload(
            self, dtype=dtype, channel_index=channel_index,
        )

    @property
    @abstractmethod
    def metadata(self) -> ImagePayloadMetadata:
        """Return the image metadata attached to this payload."""


@dataclass(frozen=True, slots=True)
class ImageMetadataPayload(DataBackedRuntimeArrayPayload, ImagePayloadMetadataCarrier):
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

    def image_data(self) -> Any:
        """Return the concrete image pixels carried by this payload."""
        return self.data

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
class MaskedImagePayload(DataBackedRuntimeArrayPayload, ImagePayloadMetadataCarrier):
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

    def image_data(self) -> Any:
        """Return the concrete image pixels carried by this payload."""
        return self.data

    def image_mask(self) -> Any:
        return self.mask

    def with_data(self, data: Any, mask: Any | None = None) -> "MaskedImagePayload":
        """Return the same semantic image mask attached to replacement data."""
        return type(self)(
            data=data,
            mask=self.mask if mask is None else mask,
            metadata=self.metadata,
        )


def image_payload_data(payload: Any) -> Any:
    """Return concrete image pixels from a runtime image payload."""
    if isinstance(payload, ImagePayloadMetadataCarrier):
        return payload.image_data()
    return payload


def image_payload_geometry(
    payload: Any,
    *,
    value_name: str = "Image payload",
) -> ArrayGeometry:
    """Return declared array geometry without moving device data to the host."""
    if isinstance(payload, ImagePayloadMetadataCarrier):
        return payload.image_geometry()
    return ArrayGeometry.require_from_value(payload, value_name=value_name)


def image_payload_mask(payload: Any) -> Any | None:
    """Return a runtime image mask when present."""
    if isinstance(payload, ImagePayloadMetadataCarrier):
        return payload.image_mask()
    return None


def image_payload_metadata(payload: Any) -> ImagePayloadMetadata:
    """Return runtime image metadata when present."""
    if isinstance(payload, ImagePayloadMetadataCarrier):
        return payload.metadata
    return ImagePayloadMetadata()


def preserved_image_plane_projection(
    payload: Any,
    projector: RuntimePlaneAxisProjector,
    source_aliases: tuple[str, ...] = (),
) -> RuntimePlaneAxisValueProjection | None:
    """Resolve the declared leading image axis against one runtime invocation."""

    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    metadata = image_payload_metadata(payload)
    if metadata.plane_axis is None:
        return RuntimeSliceProjection.preserved_context_for_value(payload)
    if metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE:
        invocation_projection = RuntimePlaneAxisValueProjection.from_projector(
            projector,
            metadata.plane_axis,
            source_aliases,
        )
        if (
            invocation_projection is not None
            and invocation_projection.plane_index is not None
        ):
            return None
        payload_projection = RuntimeSliceProjection.preserved_context_for_value(payload)
        if payload_projection is None:
            raise ValueError(
                "Runtime-slice image metadata requires a payload with the same "
                "nominal leading axis."
            )
        return payload_projection

    shape = image_payload_geometry(
        payload,
        value_name="Source-binding image payload",
    ).shape
    if len(shape) < 3:
        raise ValueError(
            "Source-binding image metadata requires its declared plane axis as "
            f"the leading dimension, got shape {shape!r}."
        )
    axis_size = shape[0]
    return RuntimePlaneAxisValueProjection(
        axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_aliases=source_aliases,
        plane_index=metadata.source_provenance.source_alias_plane_index(
            source_aliases,
            axis_size,
        ),
        axis_size=axis_size,
    )


def preserve_declared_image_payload_axis(
    projector: RuntimePlaneAxisProjector,
    output_payload: Any,
    *,
    source_payload: Any | None = None,
) -> RuntimePlaneAxisValueProjection | None:
    """Preserve the exact image axis declared by output or source ownership."""

    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    output_metadata = image_payload_metadata(output_payload)
    output_projection = RuntimeSliceProjection.preserved_context_for_value(
        output_payload
    )
    output_axis = output_metadata.plane_axis or (
        None if output_projection is None else output_projection.axis
    )

    source_metadata = image_payload_metadata(source_payload)
    source_projection = RuntimeSliceProjection.preserved_context_for_value(
        source_payload
    )
    source_axis = source_metadata.plane_axis or (
        None if source_projection is None else source_projection.axis
    )
    if output_axis is not None:
        owner = output_payload
    elif source_axis is not None:
        owner = source_payload
    else:
        return None
    return preserved_image_plane_projection(
        owner,
        projector,
    )


def project_image_mask_to_data_domain(
    mask: Any,
    data: Any,
    *,
    metadata: ImagePayloadMetadata | None = None,
) -> Any | None:
    """Validate a mask against explicit image-domain metadata."""
    if mask is None:
        return None
    data_array = image_payload_data(data)
    mask_array = image_payload_data(mask) if is_array_payload(mask) else np.asarray(mask)
    target = MemoryType(detect_memory_type(data_array))
    mask_array = MemoryType(detect_memory_type(mask_array)).convert_to(
        mask_array, target, target.device_id_of(data_array),
    )
    mask_array = target.astype(mask_array, bool)
    mask_shape = tuple(mask_array.shape)
    resolved_metadata = image_payload_metadata(data) if metadata is None else metadata
    mask_domain = resolved_metadata.mask_domain(data)
    if mask_domain.accepts(mask_shape):
        return mask_array
    raise ValueError(
        f"Mask shape {mask_shape!r} does not match declared image mask domain "
        f"{tuple(sorted(mask_domain.valid_shapes()))!r}."
    )


def image_mask_for_data_domain(
    *,
    source_payload: Any,
    data: Any,
    explicit_mask: Any | None = None,
) -> Any | None:
    """Return the effective image mask projected into a concrete data domain."""
    source_mask = (
        image_payload_mask(source_payload)
        if explicit_mask is None
        else image_payload_data(explicit_mask)
    )
    metadata = image_payload_metadata(source_payload)
    projected_mask = project_image_mask_to_data_domain(
        source_mask,
        data,
        metadata=metadata,
    )
    if projected_mask is None:
        return None
    return metadata.mask_domain(data).broadcast_to_data(projected_mask)


def with_image_payload_data(
    payload: Any,
    data: Any,
    *,
    mask: Any | None = None,
    metadata: ImagePayloadMetadata | None = None,
) -> Any:
    """Preserve image-mask and metadata semantics while replacing pixels."""
    resolved_mask = project_image_mask_to_data_domain(
        image_payload_mask(payload) if mask is None else mask,
        data,
        metadata=image_payload_metadata(payload) if metadata is None else metadata,
    )
    resolved_metadata = (
        image_payload_metadata(payload) if metadata is None else metadata
    )
    return resolved_metadata.payload_with(data, resolved_mask)


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
            image_payload_geometry(candidate, value_name="Projected image mask").shape
        ):
            return candidate
        raise ValueError(
            "Image payload mask cannot be projected into slice domain; "
            f"got mask {mask_array.shape!r} for slice "
            f"{image_payload_geometry(data_slice).shape!r}."
        )


def image_payload_slice_context(
    payload: Any,
    data: Any,
    plane_index: int,
    *,
    plane_axis: RuntimePlaneAxis | None = None,
) -> Any:
    """Attach one source plane of a payload's image context to slice data."""
    metadata = image_payload_metadata(payload)
    if plane_axis is not None:
        plane_axis = RuntimePlaneAxis(
            plane_axis,
        )
        if metadata.plane_axis is not None and metadata.plane_axis is not plane_axis:
            raise ValueError(
                "Image slice projection axis conflicts with payload metadata: "
                f"{plane_axis.value!r} != {metadata.plane_axis.value!r}."
            )
        if metadata.plane_axis is not plane_axis:
            metadata = metadata.replace_fields(plane_axis=plane_axis)
    return ImagePayloadSliceProjector(
        mask=image_payload_mask(payload),
        metadata=metadata,
    ).payload_for_slice(data, plane_index)


def image_payload_mask_for_slice(
    *,
    mask: Any | None,
    metadata: ImagePayloadMetadata,
    data_slice: RuntimeArrayData,
    plane_index: int,
) -> RuntimeArrayData | None:
    """Project a shared or plane-specific mask into one declared image slice."""

    return ImagePayloadSliceProjector(mask=mask, metadata=metadata).mask_for_slice(
        data_slice, plane_index
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

    payloads: tuple[RuntimeArrayData, ...]
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
            return tuple(image_payload_metadata(payload) for payload in self.payloads)
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
            source_channel_axis=self.composed_source_channel_axis(metadata_by_payload),
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

    def composed_source_channel_axis(
        self,
        metadata_by_payload: tuple[ImagePayloadMetadata, ...],
    ) -> int | None:
        """Return the channel axis after this composition adds a leading axis."""
        normalized = tuple(
            metadata.normalized_source_channel_axis(payload)
            for payload, metadata in zip(
                self.payloads,
                metadata_by_payload,
                strict=True,
            )
        )
        present = tuple(value for value in normalized if value is not None)
        if not present:
            return None
        first = present[0]
        if any(value != first for value in present[1:]):
            raise ValueError(
                "Cannot compose image payloads with conflicting source channel axes: "
                f"{present!r}."
            )
        return first + 1


def image_intensity_scale_for_dtype(dtype: Any) -> float | None:
    """Return the conventional full-scale intensity for a pixel dtype."""
    normalized = np.dtype(dtype)
    if np.issubdtype(normalized, np.bool_):
        return 1.0
    if np.issubdtype(normalized, np.integer):
        return float(np.iinfo(normalized).max)
    return None


def image_payload_intensity_scale(
    payload: Any,
    *,
    channel_index: int = 0,
) -> float | None:
    """Return the best semantic intensity scale for an image payload."""
    import numpy as np

    metadata_scale = image_payload_metadata(payload).intensity_scale_for_source_plane(
        channel_index
    )
    if metadata_scale is not None and metadata_scale > 0:
        return float(metadata_scale)
    data = image_payload_data(payload)
    dtype = getattr(data, "dtype", None)
    if dtype is None:
        dtype = np.asarray(data).dtype
    return image_intensity_scale_for_dtype(dtype)


def normalize_image_payload_intensity(
    payload: Any,
    *,
    dtype: Any = None,
    channel_index: int = 0,
) -> Any:
    """Enter the metadata-owned normalization recipe once at the array boundary."""
    if isinstance(payload, ImagePayloadMetadataCarrier):
        return payload.normalize_intensity_payload(dtype=dtype, channel_index=channel_index)
    return image_payload_metadata(payload).normalize_intensity_payload(
        payload, dtype=dtype, channel_index=channel_index,
    )


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
    """Accepted mask shapes for an explicitly declared image data domain."""

    data_shape: tuple[int, ...]
    channel_axis: int | None = None
    plane_axis: RuntimePlaneAxis | None = None
    spatial_axes_yx: tuple[int, int] | None = None

    def __post_init__(self) -> None:
        data_shape = tuple(int(axis_size) for axis_size in self.data_shape)
        object.__setattr__(self, "data_shape", data_shape)
        channel_axis = self.channel_axis
        if channel_axis is not None:
            normalized = int(channel_axis)
            if normalized < 0:
                normalized += len(data_shape)
            if normalized < 0 or normalized >= len(data_shape):
                raise ValueError(
                    f"Image mask channel axis {channel_axis} is invalid for "
                    f"shape {data_shape!r}."
                )
            object.__setattr__(self, "channel_axis", normalized)
        spatial_axes_yx = self.spatial_axes_yx
        if spatial_axes_yx is None:
            return
        if len(set(spatial_axes_yx)) != 2 or any(
            axis < 0 or axis >= len(data_shape) for axis in spatial_axes_yx
        ):
            raise ValueError(
                "Image mask spatial axes must be two distinct data axes; "
                f"got {spatial_axes_yx!r} for shape {data_shape!r}."
            )

    @staticmethod
    def channel_axis_slice(
        value: Any,
        *,
        channel_axis: int,
        channel_index: int,
    ) -> Any:
        geometry = image_payload_geometry(
            value,
            value_name="Channel-bearing image payload",
        )
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
        mask_array = image_payload_data(mask) if is_array_payload(mask) else np.asarray(mask)
        mask_array = MemoryType(detect_memory_type(mask_array)).astype(mask_array, bool)
        if mask_array.shape != image_payload_geometry(source_data).shape:
            return mask_array
        channel_mask = cls.channel_axis_slice(
            mask_array,
            channel_axis=channel_axis,
            channel_index=channel_index,
        )
        if (
            image_payload_geometry(channel_mask).shape
            == image_payload_geometry(channel_data).shape
        ):
            return channel_mask
        squeezed_mask = MemoryType(detect_memory_type(channel_mask)).reshape(
            channel_mask,
            tuple(
                size for axis, size in enumerate(channel_mask.shape)
                if axis != channel_axis % len(channel_mask.shape)
            ),
        )
        if (
            image_payload_geometry(squeezed_mask).shape
            == image_payload_geometry(channel_data).shape
        ):
            return squeezed_mask
        return channel_mask

    @property
    def shared_spatial_mask_shape(self) -> tuple[int, int] | None:
        """Return a mask domain shared by declared source-binding planes."""
        if (
            self.plane_axis is not RuntimePlaneAxis.SOURCE_BINDING
            or self.spatial_axes_yx is None
        ):
            return None
        return tuple(self.data_shape[axis] for axis in self.spatial_axes_yx)

    def accepts(self, mask_shape: tuple[int, ...]) -> bool:
        return mask_shape in self.valid_shapes()

    def valid_shapes(self) -> frozenset[tuple[int, ...]]:
        valid = {self.data_shape}
        if self.channel_axis is not None:
            valid.add(
                tuple(
                    axis_size
                    for axis, axis_size in enumerate(self.data_shape)
                    if axis != self.channel_axis
                )
            )
        if self.shared_spatial_mask_shape is not None:
            valid.add(self.shared_spatial_mask_shape)
        return frozenset(valid)

    def default_mask_shape(self) -> tuple[int, ...]:
        """Return the canonical mask shape for this declared image domain."""
        if self.shared_spatial_mask_shape is not None:
            return self.shared_spatial_mask_shape
        if self.channel_axis is None:
            return self.data_shape
        return tuple(
            axis_size
            for axis, axis_size in enumerate(self.data_shape)
            if axis != self.channel_axis
        )

    def broadcast_to_data(self, mask: Any) -> Any:
        """Broadcast a valid mask across its declared non-spatial axes."""
        mask_array = image_payload_data(mask) if is_array_payload(mask) else np.asarray(mask)
        memory_type = MemoryType(detect_memory_type(mask_array))
        mask_array = memory_type.astype(mask_array, bool)
        mask_shape = tuple(mask_array.shape)
        if mask_shape == self.data_shape:
            return mask_array
        if mask_shape == self.shared_spatial_mask_shape:
            if self.spatial_axes_yx is None:
                raise AssertionError("Shared spatial mask axes are missing.")
            broadcast_shape = [1] * len(self.data_shape)
            for mask_axis, data_axis in enumerate(self.spatial_axes_yx):
                broadcast_shape[data_axis] = mask_shape[mask_axis]
            return memory_type.broadcast_to(
                memory_type.reshape(mask_array, tuple(broadcast_shape)),
                self.data_shape,
            )
        channel_free_shape = (
            None
            if self.channel_axis is None
            else tuple(
                axis_size
                for axis, axis_size in enumerate(self.data_shape)
                if axis != self.channel_axis
            )
        )
        if mask_shape != channel_free_shape or self.channel_axis is None:
            raise ValueError(
                f"Mask shape {mask_shape!r} is not valid for image "
                f"shape {self.data_shape!r}."
            )
        broadcast_shape = list(mask_shape)
        broadcast_shape.insert(self.channel_axis, 1)
        return memory_type.broadcast_to(
            memory_type.reshape(mask_array, tuple(broadcast_shape)),
            self.data_shape,
        )
