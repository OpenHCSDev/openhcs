"""Generic aligned image-payload composition for multi-source runtime inputs."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, replace
from enum import Enum
from typing import Any, ClassVar, Mapping

import numpy as np
from metaclass_registry import AutoRegisterMeta

from openhcs.core.image_payload_execution_mode import (
    ImagePayloadExecutionMode,
)

from openhcs.core.alias_property import AliasProperty
from openhcs.core.artifacts import ArtifactOutputPlan, ArtifactSpec, ArtifactSpecRef
from openhcs.core.memory import (
    MEMORY_TYPE_NUMPY,
    MemoryType,
    convert_memory,
    detect_memory_type,
    stack_runtime_slices,
)
from openhcs.core.registry_strategies import (
    NominalTypeKeyedStrategyMixin,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImageMetadataProjection,
    ImagePayloadSliceProjector,
    ImagePayloadMetadataCarrier,
    ImagePayloadMetadataCompositionMode,
    ImageMaskDomain,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata_projection,
    preserved_image_plane_projection,
    with_image_payload_data,
)
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.core.runtime_object_labels import ObjectLabelRepresentation
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
    RuntimeSliceProjectableValue,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValueSet
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    SourceSpatialDomainAdapter,
)


@dataclass(frozen=True, slots=True)
class ImagePayloadSourceSpatialDomainAdapter(SourceSpatialDomainAdapter):
    """Source-domain adapter for image payload data and masks."""

    value_type = ImagePayloadMetadataCarrier
    value_type_label = "image_payload"
    value: Any
    source_domain: SourceSpatialDomain
    domain = AliasProperty[SourceSpatialDomain]("source_domain")

    @property
    def array(self) -> Any:
        return image_payload_data(self.value)

    @classmethod
    def for_value(
        cls,
        value: Any,
        *,
        source_shape_override_yx: tuple[int, int] | None = None,
    ) -> "ImagePayloadSourceSpatialDomainAdapter | None":
        if not isinstance(value, ImagePayloadMetadataCarrier):
            return None
        return cls(
            value,
            cls.domain_from_metadata(
                image_payload_metadata_projection(value),
                value_name="Image payload",
            ),
        )

    @classmethod
    def domain_from_metadata(
        cls,
        metadata: ImageMetadataProjection,
        *,
        fill_value: Any = 0,
        source_domain: SourceSpatialDomain | None = None,
        value_name: str,
    ) -> SourceSpatialDomain:
        domain = metadata.read_value("source_spatial_domain")
        if source_domain is not None:
            domain = domain.with_missing_from(source_domain)
        return (
            domain.with_missing_from(SourceSpatialDomain(origin_yx=(0, 0)))
            .with_fill_value(fill_value)
            .with_value_name(value_name)
        )

    @property
    def spatial_axes_yx(self) -> tuple[int, int]:
        axes = image_payload_metadata_projection(self.value).spatial_axes_yx(self.value)
        if axes is None:
            raise ValueError(
                "Source-spatial image payload metadata does not declare two "
                f"spatial axes for shape {tuple(np.shape(self.array))!r}."
            )
        return axes

    @property
    def spatial_shape_yx(self) -> tuple[int, int]:
        shape = image_payload_metadata_projection(self.value).spatial_shape_yx(
            self.value
        )
        if shape is None:
            raise ValueError(
                "Source-spatial image payloads require at least two dimensions, "
                f"got shape {tuple(np.shape(self.array))!r}."
            )
        return shape

    @classmethod
    def payloads_aligned_to_common_source_domain(
        cls,
        payloads: tuple[RuntimeArrayData, ...],
    ) -> tuple[RuntimeArrayData, ...]:
        adapters = cls.source_domain_adapters(payloads)
        source_domain = SourceSpatialDomainAdapter.common_source_domain(
            adapters,
            value_name="Image bundle source image",
        )
        if (
            source_domain is None
            or not SourceSpatialDomainAdapter.requires_source_domain_alignment(adapters)
        ):
            return payloads
        return tuple(
            cls.payload_in_source_domain(payload, source_domain) for payload in payloads
        )

    @classmethod
    def source_domain_adapters(
        cls,
        payloads: tuple[RuntimeArrayData, ...],
    ) -> tuple["ImagePayloadSourceSpatialDomainAdapter", ...]:
        adapters: list[ImagePayloadSourceSpatialDomainAdapter] = []
        for payload in payloads:
            adapter = SourceSpatialDomainAdapter.for_value(payload)
            if not isinstance(adapter, cls):
                raise TypeError(
                    "Image bundle alignment requires image payload adapters."
                )
            adapters.append(adapter)
        return tuple(adapters)

    @classmethod
    def payload_in_source_domain(
        cls,
        payload: RuntimeArrayData,
        source_domain: SourceSpatialDomain,
    ) -> RuntimeArrayData:
        metadata = image_payload_metadata_projection(payload)
        source_extent = source_domain.with_origin_yx(None)
        source_metadata = metadata.with_materialized_source_domain(source_extent)
        data = cls(
            payload,
            cls.domain_from_metadata(
                metadata,
                source_domain=source_extent,
                value_name="Image payload",
            ),
        ).materialize()
        return source_metadata.payload_with(
            data,
            cls.mask_in_source_domain(payload, metadata, source_extent),
        )

    @classmethod
    def mask_in_source_domain(
        cls,
        payload: RuntimeArrayData,
        metadata: ImageMetadataProjection,
        source_domain: SourceSpatialDomain,
    ) -> RuntimeArrayData | None:
        mask = image_payload_mask(payload)
        if mask is None:
            return None
        return NumPyImagePayloadSourceSpatialDomainAdapter(
            mask,
            cls.domain_from_metadata(
                metadata,
                fill_value=False,
                source_domain=source_domain,
                value_name="Image mask",
            ),
        ).materialize()

    def value_in_payload_domain(
        self,
        target: SourceSpatialDomainAdapter,
    ) -> RuntimeArrayData:
        """Project this image payload into another declared payload domain."""
        materialized = self.payload_in_source_domain(self.value, target.domain)
        target_domain = SourceSpatialDomain(
            origin_yx=target.payload_domain.origin_yx,
            source_shape_yx=target.payload_domain.source_shape_yx,
            fill_value=self.domain.fill_value,
            value_name=self.domain.value_name,
        )
        metadata = image_payload_metadata_projection(materialized).derive_fields(
            source_spatial_domain=target_domain,
            physical_border_edges_yx=target_domain.physical_border_edges_for_shape(
                target.payload_domain.spatial_shape_yx
            ),
        )
        materialized_mask = image_payload_mask(materialized)
        return with_image_payload_data(
            materialized,
            target.extract_source_array(
                image_payload_data(materialized),
                spatial_axes_yx=self.spatial_axes_yx,
            ),
            mask=(
                None
                if materialized_mask is None
                else target.extract_source_array(
                    materialized_mask,
                    spatial_axes_yx=self.spatial_axes_yx,
                )
            ),
            metadata=metadata,
        )


class NumPyImagePayloadSourceSpatialDomainAdapter(
    ImagePayloadSourceSpatialDomainAdapter
):
    """Source-domain adapter for raw NumPy image arrays."""

    value_type = np.ndarray
    value_type_label = "numpy_image"

    @classmethod
    def for_value(
        cls,
        value: Any,
        *,
        source_shape_override_yx: tuple[int, int] | None = None,
    ) -> "NumPyImagePayloadSourceSpatialDomainAdapter | None":
        if not isinstance(value, np.ndarray):
            return None
        return cls(
            value,
            SourceSpatialDomain(
                origin_yx=(0, 0),
                source_shape_yx=source_shape_override_yx,
                fill_value=0,
                value_name="NumPy image payload",
            ),
        )

    @property
    def array(self) -> Any:
        return self.value

    @property
    def spatial_shape_yx(self) -> tuple[int, int]:
        shape = ImagePayloadMetadata().spatial_shape_yx(self.value)
        if shape is None:
            raise ValueError(
                "NumPy source-spatial image payloads require at least two "
                f"dimensions, got shape {tuple(np.shape(self.value))!r}."
            )
        return shape

    def value_in_payload_domain(
        self,
        target: SourceSpatialDomainAdapter,
    ) -> Any:
        """Project a raw array without introducing a nominal payload carrier."""
        return target.extract_source_array(
            self.materialize(),
            spatial_axes_yx=self.spatial_axes_yx,
        )


@dataclass(frozen=True, slots=True)
class ObjectLabelPayloadSourceSpatialDomainAdapter(SourceSpatialDomainAdapter):
    """Source-domain adapter for object-label payload values."""

    value_type = ObjectLabelValue
    value_type_label = "object_label_payload"
    value: ObjectLabelValue
    source_shape_override_yx: tuple[int, int] | None = None

    @classmethod
    def for_value(
        cls,
        value: Any,
        *,
        source_shape_override_yx: tuple[int, int] | None = None,
    ) -> "ObjectLabelPayloadSourceSpatialDomainAdapter | None":
        if not isinstance(value, ObjectLabelValue):
            return None
        return cls(value, source_shape_override_yx=source_shape_override_yx)

    @property
    def array(self) -> Any:
        return object_label_dense_array(self.value)

    @property
    def domain(self) -> SourceSpatialDomain:
        return self.value.object_label_source_spatial_domain().with_missing_from(
            SourceSpatialDomain(source_shape_yx=self.source_shape_override_yx)
        )

    @property
    def spatial_axes_yx(self) -> tuple[int, int]:
        array = np.asarray(self.array)
        if array.ndim < 2:
            raise ValueError(
                "Object-label source-spatial payloads require at least two "
                f"dimensions, got shape {array.shape!r}."
            )
        return array.ndim - 2, array.ndim - 1

    def dense_variant(self, labels: object) -> object:
        """Materialize one label variant through its nominal object-label carrier."""
        variant = self.value.with_labels(labels)
        return object_label_dense_array(variant)

    def value_in_payload_domain(
        self,
        target: SourceSpatialDomainAdapter,
    ) -> ObjectLabelValue:
        """Project every label variant into another declared payload domain."""
        target_domain = SourceSpatialDomain(
            origin_yx=target.payload_domain.origin_yx,
            source_shape_yx=target.payload_domain.source_shape_yx,
            fill_value=self.domain.fill_value,
            value_name=self.domain.value_name,
        )
        variants = self.value.variant_data.project(
            lambda labels: target.extract_source_array(
                self.domain.materialize(
                    self.dense_variant(labels),
                    spatial_axes_yx=self.spatial_axes_yx,
                ),
                spatial_axes_yx=self.spatial_axes_yx,
            )
        )
        return self.value.with_variants(
            variants,
            source_spatial_domain=target_domain,
            representation=ObjectLabelRepresentation.DENSE_LABELS,
        )


@dataclass(frozen=True, slots=True)
class AlignedImageStackKwargResolver:
    """Materialize one kwarg for a specific aligned image-stack slice."""

    projection_axis: "RuntimePlaneAxisValueProjection"
    reference_payload: Any | None = None

    def resolve(self, value: Any) -> Any:
        strategy = AlignedImageStackKwargResolutionStrategy.require_nominal_value(
            value,
            context="Aligned image-stack kwarg resolution",
        )
        return strategy.resolve(value, self)

    def resolve_source_spatial_value(self, value: Any) -> Any:
        """Project a nominal value into the declared reference payload domain."""
        if self.reference_payload is None:
            return value
        metadata = image_payload_metadata_projection(self.reference_payload)
        source_shape = metadata.read_value("source_spatial_domain").source_shape_yx
        if source_shape is None:
            return value
        adapter = SourceSpatialDomainAdapter.for_value(
            value,
            source_shape_override_yx=source_shape,
        )
        reference = SourceSpatialDomainAdapter.for_value(self.reference_payload)
        if adapter is None or reference is None:
            return value
        return adapter.value_in_payload_domain(reference)


def stack_image_payload_context(
    image_payloads: Sequence[Any],
    stack: RuntimeArrayData,
    *,
    metadata_mode: ImagePayloadMetadataCompositionMode,
) -> Any:
    """Attach composed image metadata and masks to a freshly stacked payload."""
    payloads = tuple(image_payloads)
    metadata = ImagePayloadMetadata.compose(
        payloads,
        mode=metadata_mode,
    )
    return metadata.payload_with(stack, _stack_image_payload_mask(payloads, stack))


class ImagePayloadStackComposition(ABC):
    """Compose pixels, masks and provenance on one declared leading axis."""

    @property
    @abstractmethod
    def composition_payloads(self) -> tuple[Any, ...]: ...

    @property
    @abstractmethod
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode: ...

    @staticmethod
    def copy_whole_image(
        value: RuntimeArrayData,
        *,
        memory_type: str,
        device_id: int | None,
    ) -> RuntimeArrayData:
        """Copy pixels, mask and metadata without adding a composition axis."""
        copied_data = stack_runtime_slices(
            (image_payload_data(value),),
            memory_type,
            device_id,
        )[0]
        mask = image_payload_mask(value)
        copied_mask = (
            None
            if mask is None
            else stack_runtime_slices((mask,), memory_type, device_id)[0]
        )
        return (
            image_payload_metadata_projection(value)
            .derive_fields()
            .payload_with(
                copied_data,
                copied_mask,
            )
        )

    def composition_source_metadata(self) -> tuple[ImageMetadataProjection, ...]:
        return tuple(
            self.composition_payload_metadata(
                image_payload_metadata_projection(payload)
            )
            for payload in self.composition_payloads
        )

    def composition_payload_metadata(
        self, metadata: ImageMetadataProjection
    ) -> ImageMetadataProjection:
        """Preserve each input's declared provenance unless the axis owner projects it."""
        return metadata

    def compose(self) -> Any:
        payloads = self.composition_payloads
        composed = self.compose_unmasked(
            tuple(image_payload_data(payload) for payload in payloads)
        )
        metadata = ImagePayloadMetadata.compose(
            payloads,
            mode=self.composition_metadata_mode,
            source_metadata=self.composition_source_metadata(),
        )
        return metadata.payload_with(composed, self.compose_mask(composed, metadata))

    def compose_unmasked(
        self, payloads: tuple[RuntimeArrayData, ...]
    ) -> RuntimeArrayData:
        memory_type = detect_memory_type(payloads[0])
        return stack_runtime_slices(
            payloads, memory_type, MemoryType(memory_type).device_id_of(payloads[0])
        )

    def compose_mask(
        self, composed: Any, metadata: ImageMetadataProjection
    ) -> Any | None:
        return _stack_image_payload_mask(
            self.composition_payloads,
            composed,
            output_mask_domain=metadata.mask_domain(composed),
        )


@dataclass(slots=True)
class ImagePayloadStackContext(ImagePayloadStackComposition):
    """Explicit dense stack inputs; the ancestor owns composition."""

    payloads: Sequence[RuntimeArrayData]
    metadata_mode: ImagePayloadMetadataCompositionMode

    def __post_init__(self) -> None:
        self.payloads = tuple(self.payloads)
        if not self.payloads:
            raise ValueError("Cannot stack an empty image payload sequence.")

    @property
    def composition_payloads(self) -> tuple[Any, ...]:
        return tuple(self.payloads)

    @property
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode:
        return self.metadata_mode


def stack_image_payloads(
    image_payloads: Sequence[Any],
    *,
    metadata_mode: ImagePayloadMetadataCompositionMode,
) -> Any:
    """Stack image payloads in their declared memory domain with full context."""

    return ImagePayloadStackContext(image_payloads, metadata_mode).compose()


def stack_image_payload_context_from_metadata(
    image_payloads: Sequence[Any],
    stack: RuntimeArrayData,
    metadata_by_payload: Sequence[ImageMetadataProjection],
    *,
    metadata_mode: ImagePayloadMetadataCompositionMode,
) -> Any:
    """Attach composed image context using already resolved payload metadata."""
    payloads = tuple(image_payloads)
    metadata = ImagePayloadMetadata.compose(
        payloads,
        mode=metadata_mode,
        source_metadata=tuple(metadata_by_payload),
    )
    return metadata.payload_with(stack, _stack_image_payload_mask(payloads, stack))


def _stack_image_payload_mask(
    image_payloads: Sequence[Any],
    stack: RuntimeArrayData,
    *,
    output_mask_domain: ImageMaskDomain | None = None,
) -> RuntimeArrayData | None:
    masks = tuple(image_payload_mask(payload) for payload in image_payloads)
    if not any(mask is not None for mask in masks):
        return None
    payloads = tuple(image_payloads)
    stack_shape = tuple(np.shape(stack))
    if stack_shape[:1] != (len(payloads),):
        raise ValueError(
            "Image payload stack mask composition requires output stack "
            f"axis length {len(payloads)}, got stack shape {stack_shape!r}."
        )
    output_slice_domains = tuple(
        stack[slice_index] for slice_index in range(len(payloads))
    )
    resolved_masks = tuple(
        _complete_image_payload_mask(payload, slice_domain, mask)
        for payload, slice_domain, mask in zip(
            payloads,
            output_slice_domains,
            masks,
            strict=True,
        )
    )
    stacked_mask_shape = (len(payloads), *tuple(np.shape(resolved_masks[0])))
    if output_mask_domain is not None and not output_mask_domain.accepts(
        stacked_mask_shape
    ):
        resolved_masks = tuple(
            image_payload_metadata_projection(payload)
            .mask_domain(slice_domain)
            .broadcast_to_data(mask)
            for payload, slice_domain, mask in zip(
                payloads, output_slice_domains, resolved_masks, strict=True
            )
        )
    return stack_runtime_slices(
        resolved_masks,
        detect_memory_type(stack),
        0,
    )


def _complete_image_payload_mask(
    payload: Any,
    payload_data: RuntimeArrayData,
    mask: RuntimeArrayData | None,
) -> RuntimeArrayData:
    mask_domain = image_payload_metadata_projection(payload).mask_domain(payload_data)
    if mask is not None:
        if not mask_domain.accepts(tuple(np.shape(mask))):
            raise ValueError(
                "Image payload mask must match the selected output slice "
                f"domain; got mask {tuple(np.shape(mask))!r} for slice "
                f"{tuple(np.shape(payload_data))!r}."
            )
        return mask
    return np.ones(mask_domain.default_mask_shape(), dtype=bool)


def unstack_image_payload_context(
    payload: Any,
    slices: Sequence[Any],
    *,
    default_plane_axis: RuntimePlaneAxis | None = None,
) -> list[Any]:
    """Attach one source plane of payload context to each unstacked image slice."""
    mask = image_payload_mask(payload)
    metadata = image_payload_metadata_projection(payload)
    if mask is None and not metadata.has_values:
        return list(slices)
    if metadata.read_value("plane_axis") is None and default_plane_axis is not None:
        metadata = metadata.derive_fields(plane_axis=default_plane_axis)
    projector = ImagePayloadSliceProjector(mask=mask, metadata=metadata)
    return projector.payloads_for_slices(slices)


class AlignedImageStackKwargResolutionStrategy(
    NominalTypeKeyedStrategyMixin,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Nominal strategy for resolving one slice-aligned runtime kwarg."""

    __registry_key__ = "value_type_label"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[str, type["AlignedImageStackKwargResolutionStrategy"]]
    ] = {}
    value_type: ClassVar[type[Any] | None] = None
    value_type_label: ClassVar[str | None] = None

    @abstractmethod
    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        """Return the value in the current aligned slice context."""


class TupleAlignedKwargResolutionStrategy(AlignedImageStackKwargResolutionStrategy):
    """Resolve tuple-valued kwargs elementwise while preserving tuple structure."""

    value_type = tuple

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        return tuple(resolver.resolve(item) for item in value)


class ImagePayloadAlignedKwargResolutionStrategy(
    AlignedImageStackKwargResolutionStrategy
):
    """Resolve image payloads without discarding metadata or masks."""

    value_type = ImagePayloadMetadataCarrier

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        return resolver.resolve_source_spatial_value(value)


class ObjectLabelAlignedKwargResolutionStrategy(
    AlignedImageStackKwargResolutionStrategy
):
    """Resolve object labels by runtime-slice and source-spatial contracts."""

    value_type = ObjectLabelValue

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        if not isinstance(value, ObjectLabelValue):
            raise TypeError(
                "Object-label aligned kwarg resolution requires ObjectLabelValue."
            )
        slice_count = value.runtime_slice_plane_count()
        if slice_count is not None:
            if slice_count != resolver.projection_axis.axis_size:
                raise ValueError(
                    "Runtime-slice object-label cardinality must exactly match the "
                    f"declared projection axis: {slice_count} != "
                    f"{resolver.projection_axis.axis_size}."
                )
            from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

            projected = RuntimeSliceProjection.value_for_slice(
                value,
                resolver.projection_axis,
            )
        else:
            projected = value
        return resolver.resolve_source_spatial_value(projected)


class RuntimeSliceAlignedValueKwargResolutionStrategy(
    AlignedImageStackKwargResolutionStrategy
):
    """Select non-image values that explicitly declare runtime-slice alignment."""

    value_type = RuntimeSliceAlignedValueSet

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        if not isinstance(value, RuntimeSliceAlignedValueSet):
            raise TypeError(
                "RuntimeSliceAlignedValueKwargResolutionStrategy requires "
                "RuntimeSliceAlignedValueSet."
            )
        return resolver.projection_axis.aligned_value(value)


class RuntimeSliceProjectableAlignedKwargResolutionStrategy(
    AlignedImageStackKwargResolutionStrategy
):
    """Project values through their declared runtime-slice hook."""

    value_type = RuntimeSliceProjectableValue

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return RuntimeSliceProjection.value_for_slice(
            value,
            resolver.projection_axis,
        )


class PassThroughAlignedKwargResolutionStrategy(
    AlignedImageStackKwargResolutionStrategy,
):
    """Leave non-slice-aligned kwargs in their native runtime domain."""

    value_type = object

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        del resolver
        return value


@dataclass(frozen=True, slots=True)
class ImagePayloadComposition:
    """Resolved image payload plus its execution mode."""

    payload: Any
    execution_mode: ImagePayloadExecutionMode

    @property
    def plane_axis(self) -> RuntimePlaneAxis | None:
        """Return the axis declared by the composed payload owner."""
        if isinstance(self.payload, AlignedImageStack):
            return RuntimePlaneAxis.RUNTIME_SLICE
        return image_payload_metadata_projection(self.payload).read_value("plane_axis")

    def preserved_plane_projection(
        self,
        projector: RuntimePlaneAxisProjector,
        *,
        source_aliases: tuple[str, ...] = (),
    ) -> RuntimePlaneAxisValueProjection | None:
        """Return the complete projection owned by the composed payload axis."""

        axis = self.plane_axis
        if axis is None:
            return None
        return preserved_image_plane_projection(
            self.payload,
            projector,
            source_aliases,
        )


@dataclass(slots=True)
class ImagePayloadBundleContext(ImagePayloadStackContext):
    """Compose same-slice image bundle data, masks, and metadata together."""

    metadata_mode: ImagePayloadMetadataCompositionMode = (
        ImagePayloadMetadataCompositionMode.BUNDLE
    )

    def __post_init__(self) -> None:
        super(ImagePayloadBundleContext, self).__post_init__()
        declared_axes = tuple(
            (
                index,
                metadata.read_value("plane_axis"),
                metadata.read_value("source_provenance").source_image_names,
                tuple(np.shape(image_payload_data(payload))),
            )
            for index, (payload, metadata) in enumerate(
                zip(self.payloads, self.source_metadata, strict=True)
            )
            if metadata.read_value("plane_axis") is not None
        )
        if declared_axes:
            raise ValueError(
                "Same-slice image bundles require every payload plane axis to be "
                f"projected before composition; got {declared_axes!r}."
            )

    @property
    def source_metadata(self) -> tuple[ImageMetadataProjection, ...]:
        return self.composition_source_metadata()

    @property
    def data_payloads(self) -> tuple[RuntimeArrayData, ...]:
        return tuple(image_payload_data(payload) for payload in self.payloads)

    @property
    def masks(self) -> tuple[RuntimeArrayData | None, ...]:
        return tuple(image_payload_mask(payload) for payload in self.payloads)

    @property
    def present_masks(self) -> tuple[RuntimeArrayData, ...]:
        return tuple(mask for mask in self.masks if mask is not None)

    @classmethod
    def from_payloads(
        cls,
        payloads: tuple[RuntimeArrayData, ...],
        *,
        metadata_mode: ImagePayloadMetadataCompositionMode = (
            ImagePayloadMetadataCompositionMode.BUNDLE
        ),
    ) -> "ImagePayloadBundleContext":
        return cls(
            ImagePayloadSourceSpatialDomainAdapter.payloads_aligned_to_common_source_domain(
                payloads
            ),
            metadata_mode=metadata_mode,
        )

    def compose_mask(
        self,
        composed: Any,
        metadata: ImageMetadataProjection,
    ) -> Any | None:
        masks = self.present_masks
        if not masks:
            return None
        shared_spatial_shape = metadata.mask_domain(composed).shared_spatial_mask_shape
        if shared_spatial_shape is not None and all(
            tuple(np.shape(mask)) == shared_spatial_shape for mask in masks
        ):
            return self.combined_mask()
        resolved_masks = tuple(
            _complete_image_payload_mask(payload, data, mask)
            for payload, data, mask in zip(
                self.payloads,
                self.data_payloads,
                self.masks,
                strict=True,
            )
        )
        memory_type = detect_memory_type(resolved_masks[0])
        memory_type_owner = MemoryType(memory_type)
        stacked = stack_runtime_slices(
            resolved_masks,
            memory_type,
            memory_type_owner.device_id_of(resolved_masks[0]),
        )
        return memory_type_owner.astype(stacked, bool)

    def combined_mask(self) -> RuntimeArrayData | None:
        masks = self.present_masks
        if not masks:
            return None
        mask_shapes = tuple(tuple(np.shape(mask)) for mask in masks)
        if any(shape != mask_shapes[0] for shape in mask_shapes[1:]):
            raise ValueError(
                "Image bundle mask intersection requires one exact declared "
                f"spatial mask shape; got {mask_shapes!r}."
            )
        memory_type = MemoryType(detect_memory_type(masks[0]))
        combined = memory_type.astype(masks[0], bool)
        for mask in masks[1:]:
            combined = memory_type.logical_and(
                combined,
                memory_type.astype(mask, bool),
            )
        return combined

    def compose_unmasked(
        self,
        payloads: tuple[RuntimeArrayData, ...],
    ) -> RuntimeArrayData:
        """Compose image payload arrays without mask/metadata wrapping."""
        memory_type = detect_memory_type(payloads[0])
        device_id = MemoryType(memory_type).device_id_of(payloads[0])
        channel_axes = tuple(
            metadata.normalized_source_channel_axis(payload)
            for payload, metadata in zip(
                payloads,
                self.source_metadata,
                strict=True,
            )
        )
        declared_channel_count = sum(axis is not None for axis in channel_axes)
        if declared_channel_count in {0, len(payloads)}:
            return stack_runtime_slices(payloads, memory_type, device_id)
        return self.compose_mixed_channel_payloads(
            payloads,
            channel_axes=channel_axes,
            memory_type=memory_type,
            device_id=device_id,
        )

    @staticmethod
    def compose_mixed_channel_payloads(
        payloads: tuple[RuntimeArrayData, ...],
        *,
        channel_axes: tuple[int | None, ...],
        memory_type: str,
        device_id: int | None,
    ) -> RuntimeArrayData:
        """Promote channel-free payloads using declared channel-axis semantics."""
        numpy_payloads = tuple(
            np.asarray(
                convert_memory(
                    data=payload,
                    source_type=detect_memory_type(payload),
                    target_type=MEMORY_TYPE_NUMPY,
                    gpu_id=device_id,
                )
            )
            for payload in payloads
        )
        declared_axes = tuple(axis for axis in channel_axes if axis is not None)
        channel_axis = declared_axes[0]
        if any(axis != channel_axis for axis in declared_axes[1:]):
            raise ValueError(
                "Image bundle payloads declare conflicting source channel axes: "
                f"{channel_axes!r}."
            )
        channel_counts = tuple(
            int(payload.shape[channel_axis])
            for payload, axis in zip(numpy_payloads, channel_axes, strict=True)
            if axis is not None
        )
        channel_count = channel_counts[0]
        if any(count != channel_count for count in channel_counts[1:]):
            raise ValueError(
                "Image bundle payloads declare incompatible channel counts: "
                f"{channel_counts!r}."
            )
        source_shapes = tuple(
            (
                tuple(payload.shape)
                if axis is None
                else tuple(
                    dimension
                    for index, dimension in enumerate(payload.shape)
                    if index != axis
                )
            )
            for payload, axis in zip(numpy_payloads, channel_axes, strict=True)
        )
        if any(shape != source_shapes[0] for shape in source_shapes[1:]):
            raise ValueError(
                "Image bundle payloads must share one declared source image shape: "
                f"{source_shapes!r}."
            )
        promoted = tuple(
            (
                payload
                if axis is not None
                else np.repeat(
                    np.expand_dims(payload, axis=channel_axis),
                    channel_count,
                    axis=channel_axis,
                )
            )
            for payload, axis in zip(numpy_payloads, channel_axes, strict=True)
        )
        stacked = np.stack(promoted, axis=0)
        if memory_type == MEMORY_TYPE_NUMPY:
            return stacked
        return convert_memory(
            data=stacked,
            source_type=MEMORY_TYPE_NUMPY,
            target_type=memory_type,
            gpu_id=device_id,
        )


@dataclass(frozen=True, slots=True)
class AlignedImageSliceContext:
    """Declared semantic context for one aligned image output slice."""

    MAIN_FLOW_OUTPUT_KIND: ClassVar[str] = "main"
    ANONYMOUS_MAIN_FLOW_OUTPUT_KEY: ClassVar[str] = "main"

    output_kind: str
    output_key: str
    projection_key: str
    artifact_kind: str | None = None

    @property
    def persisted_source_alias(self) -> str | None:
        """Expose a declared artifact name, preserving anonymous main flow."""
        return self.output_key if self.artifact_kind is not None else None

    @classmethod
    def main_flow(
        cls,
        output_key: str,
        *,
        projection_key: str | None = None,
        artifact_kind: str | None = None,
    ) -> "AlignedImageSliceContext":
        """Return declared context for one main-flow output surface."""
        return cls(
            output_kind=cls.MAIN_FLOW_OUTPUT_KIND,
            output_key=output_key,
            projection_key=(
                cls.MAIN_FLOW_OUTPUT_KIND if projection_key is None else projection_key
            ),
            artifact_kind=artifact_kind,
        )

    @classmethod
    def independent_main_flow(
        cls,
        output_key: str,
        *,
        artifact_kind: str | None = None,
    ) -> AlignedImageSliceContext:
        """Return a named output that owns an independent viewer projection."""

        return cls.main_flow(
            output_key,
            projection_key=output_key,
            artifact_kind=artifact_kind,
        )

    @classmethod
    def main_flow_for_artifact_specs(
        cls,
        specs: Sequence[ArtifactSpec],
    ) -> tuple[AlignedImageSliceContext, ...]:
        """Return safe pre-compilation contexts for exact output declarations."""

        declared = tuple(specs)
        return tuple(
            cls.main_flow(
                output_key=spec.name,
                projection_key=(
                    cls.MAIN_FLOW_OUTPUT_KIND if len(declared) == 1 else spec.name
                ),
                artifact_kind=spec.artifact_type.value,
            )
            for spec in declared
        )

    @classmethod
    def main_flow_for_output_plans(
        cls,
        plans: Sequence[ArtifactOutputPlan],
    ) -> tuple[AlignedImageSliceContext, ...]:
        """Project compiled output coordinates into stable producer identities."""

        compiled = tuple(plans)
        if any(not isinstance(plan, ArtifactOutputPlan) for plan in compiled):
            raise TypeError(
                "Main-flow output projection requires ArtifactOutputPlan values."
            )
        share_projection = len(compiled) == 1 or all(
            left.is_component_coordinate_disjoint_from(right)
            for index, left in enumerate(compiled)
            for right in compiled[index + 1 :]
        )
        return tuple(
            cls.main_flow(
                output_key=plan.name,
                projection_key=(
                    cls.MAIN_FLOW_OUTPUT_KIND if share_projection else plan.name
                ),
                artifact_kind=plan.artifact_type.value,
            )
            for plan in compiled
        )

    @classmethod
    def anonymous_main_flow(cls) -> "AlignedImageSliceContext":
        """Return context for ordinary unnamed main-flow output."""
        return cls.main_flow(cls.ANONYMOUS_MAIN_FLOW_OUTPUT_KEY)

    @property
    def is_anonymous_main_flow(self) -> bool:
        return (
            self.output_kind == self.MAIN_FLOW_OUTPUT_KIND
            and self.output_key == self.ANONYMOUS_MAIN_FLOW_OUTPUT_KEY
            and self.artifact_kind is None
        )

    def contextualize_image_payload(
        self, payload: RuntimeArrayData
    ) -> RuntimeArrayData:
        """Attach this named main-flow identity to an image payload."""

        if self.is_anonymous_main_flow:
            return payload
        metadata = image_payload_metadata_projection(payload)
        return metadata.derive_fields(
            source_provenance=metadata.read_value(
                "source_provenance"
            ).with_derived_source_image_names((self.output_key,))
        ).payload_with(
            image_payload_data(payload),
            image_payload_mask(payload),
        )

    def matches_artifact_ref(self, artifact_ref: ArtifactSpecRef) -> bool:
        """Return whether this context carries one exact compiled artifact ref."""

        if not isinstance(artifact_ref, ArtifactSpecRef):
            raise TypeError(
                "Aligned image context lookup requires ArtifactSpecRef, got "
                f"{type(artifact_ref).__name__}."
            )
        return (
            self.output_kind == self.MAIN_FLOW_OUTPUT_KIND
            and self.output_key == artifact_ref.name
            and self.artifact_kind == artifact_ref.artifact_type.require_value()
        )

    def __post_init__(self) -> None:
        if not self.output_kind:
            raise ValueError("AlignedImageSliceContext.output_kind cannot be empty.")
        if not self.output_key:
            raise ValueError("AlignedImageSliceContext.output_key cannot be empty.")
        if not self.projection_key:
            raise ValueError("AlignedImageSliceContext.projection_key cannot be empty.")


@dataclass(slots=True)
class AlignedImageStack(ImagePayloadStackComposition):
    """Per-slice multi-image bundles aligned to one OpenHCS stack."""

    slices: tuple[Any, ...]
    slice_contexts: tuple[AlignedImageSliceContext, ...] = ()

    @property
    def composition_payloads(self) -> tuple[Any, ...]:
        return self.slices

    @property
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode:
        return ImagePayloadMetadataCompositionMode.STACK

    @property
    def projected_output_composition_mode(
        self,
    ) -> ImagePayloadMetadataCompositionMode | None:
        """Declare the outer runtime axis retained by projected output members."""
        return self.composition_metadata_mode

    def plane_axis_for_output_context(
        self,
        context: AlignedImageSliceContext,
    ) -> RuntimePlaneAxis | None:
        """An explicitly aligned stack declares its outer runtime-slice domain."""
        return RuntimePlaneAxis.RUNTIME_SLICE

    def composition_payload_metadata(
        self, metadata: ImageMetadataProjection
    ) -> ImageMetadataProjection:
        """Inner image bundles contribute provenance, not an outer slice axis."""
        metadata = super(AlignedImageStack, self).composition_payload_metadata(metadata)
        return metadata.derive_fields(
            source_provenance=metadata.read_value(
                "source_provenance"
            ).with_runtime_planes_as_contributors()
        )

    def __post_init__(self) -> None:
        self.slices = tuple(self.slices)
        self.slice_contexts = tuple(self.slice_contexts)
        if not self.slices:
            raise ValueError("AlignedImageStack.slices cannot be empty.")
        if self.slice_contexts and len(self.slice_contexts) != len(self.slices):
            raise ValueError(
                "AlignedImageStack.slice_contexts must be empty or match slices; "
                f"got {len(self.slice_contexts)} context(s) for {len(self.slices)} slice(s)."
            )

    def slice_source_spatial_adapter(
        self,
        slice_index: int,
    ) -> SourceSpatialDomainAdapter | None:
        """Return the typed source-domain adapter for one execution slice."""
        return SourceSpatialDomainAdapter.for_value(self.slices[slice_index])

    def first_slice_source_spatial_adapter(self) -> SourceSpatialDomainAdapter | None:
        """Return the typed source-domain adapter for the first execution slice."""
        return self.slice_source_spatial_adapter(0)

    def aligned_slice(self, slice_index: int, slice_count: int) -> Any:
        """Return this aligned runtime value in an outer aligned slice context."""
        if len(self.slices) != slice_count:
            raise ValueError(
                "Nested aligned image stack cardinality must exactly match the "
                f"declared outer axis: {len(self.slices)} != {slice_count}."
            )
        return self.slices[slice_index]

    def with_slices(self, slices: Sequence[Any]) -> "AlignedImageStack":
        """Replace payload slices while preserving the concrete alignment owner."""

        return type(self)(tuple(slices), self.slice_contexts)

    def projected_output_slices(
        self,
    ) -> Iterator[tuple[Any, AlignedImageSliceContext | None]]:
        """Project each output once together with its declaration-owned context."""
        contexts = self.slice_contexts or (None,) * len(self.slices)
        for payload, context in zip(self.slices, contexts, strict=True):
            for output_slice in payload_slices_for_alignment(payload):
                yield output_slice, context

    def output_values_for_artifact_specs(
        self,
        canonical_specs: tuple[ArtifactSpec, ...],
    ) -> dict[ArtifactSpecRef, Any]:
        """Bind one complete declared main-flow roster to exact slice contexts."""

        if not self.slice_contexts:
            raise ValueError(
                "Multiple canonical output specs require exact AlignedImageStack "
                "slice contexts; positional slice order is not artifact identity."
            )

        specs_by_context = {
            (spec.name, spec.artifact_type.value): spec for spec in canonical_specs
        }
        if len(specs_by_context) != len(canonical_specs):
            raise ValueError("Canonical output ABI contains duplicate named contexts.")
        resolved: dict[ArtifactSpecRef, Any] = {}
        for payload, context in zip(
            self.slices,
            self.slice_contexts,
            strict=True,
        ):
            if context.output_kind != AlignedImageSliceContext.MAIN_FLOW_OUTPUT_KIND:
                raise ValueError(
                    "Canonical AlignedImageStack contains a non-main-flow slice "
                    f"context: {context!r}."
                )
            context_key = (context.output_key, context.artifact_kind)
            spec = specs_by_context.get(context_key)
            if spec is None:
                raise ValueError(
                    "Canonical AlignedImageStack context is not declared by the "
                    f"callable ABI: {context!r}."
                )
            ref = spec.ref()
            if ref in resolved:
                raise ValueError(
                    "Canonical AlignedImageStack contains duplicate context for "
                    f"{ref!r}."
                )
            resolved[ref] = payload
        missing = tuple(
            spec.ref() for spec in canonical_specs if spec.ref() not in resolved
        )
        if missing:
            raise ValueError(
                "Canonical AlignedImageStack does not carry every declared output: "
                f"{missing!r}."
            )
        return resolved

    def output_payload(
        self,
        artifact_ref: ArtifactSpecRef,
    ) -> Any | None:
        """Return the payload carried for one exact compiled artifact ref."""

        if not self.slice_contexts:
            return None
        matches = tuple(
            payload
            for payload, context in zip(
                self.slices,
                self.slice_contexts,
                strict=True,
            )
            if context.matches_artifact_ref(artifact_ref)
        )
        if len(matches) > 1:
            raise ValueError(
                "Aligned image stack carries duplicate main-flow output context "
                f"for {artifact_ref!r}."
            )
        return matches[0] if matches else None


@dataclass(slots=True)
class ImageOutputBundle(AlignedImageStack):
    """Named main-flow image outputs sharing one invocation context."""

    @property
    def composition_payloads(self) -> tuple[Any, ...]:
        return tuple(
            context.contextualize_image_payload(payload)
            for payload, context in zip(self.slices, self.slice_contexts, strict=True)
        )

    @property
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode:
        return ImagePayloadMetadataCompositionMode.BUNDLE

    @property
    def projected_output_composition_mode(
        self,
    ) -> ImagePayloadMetadataCompositionMode | None:
        """Flatten declared inner runtime planes, retaining other named image domains."""
        if any(
            image_payload_metadata_projection(payload).read_value("plane_axis")
            is RuntimePlaneAxis.RUNTIME_SLICE
            for payload in self.slices
        ):
            return ImagePayloadMetadataCompositionMode.STACK
        if len(self.slices) == 1:
            return None
        return self.composition_metadata_mode

    def plane_axis_for_output_context(
        self,
        context: AlignedImageSliceContext,
    ) -> RuntimePlaneAxis | None:
        """Resolve a named output's original inner domain before leaf projection."""
        payloads = tuple(
            payload
            for payload, declared_context in zip(
                self.slices, self.slice_contexts, strict=True
            )
            if declared_context == context
        )
        if len(payloads) != 1:
            raise ValueError(
                "Named image output context requires exactly one original payload: "
                f"{context!r}; found {len(payloads)}."
            )
        return image_payload_metadata_projection(payloads[0]).read_value("plane_axis")

    def composition_payload_metadata(
        self, metadata: ImageMetadataProjection
    ) -> ImageMetadataProjection:
        """Named output surfaces remain source-binding planes, not runtime slices."""
        return metadata

    def __post_init__(self) -> None:
        super(ImageOutputBundle, self).__post_init__()
        if not self.slice_contexts or any(
            context.is_anonymous_main_flow for context in self.slice_contexts
        ):
            raise ValueError(
                "ImageOutputBundle requires one named context per image output."
            )


def pack_aligned_image_outputs(
    outputs: Sequence[Any],
    *,
    slice_contexts: Sequence[AlignedImageSliceContext] = (),
) -> Any:
    """Pack one or more image outputs into the single canonical return slot."""

    packed = tuple(outputs)
    if not packed:
        raise ValueError("Canonical image output packing requires at least one output.")
    contexts = tuple(slice_contexts)
    if contexts and len(contexts) != len(packed):
        raise ValueError(
            "Canonical image output contexts must match output count; "
            f"got {len(contexts)} context(s) for {len(packed)} output(s)."
        )
    if contexts:
        packed = tuple(
            context.contextualize_image_payload(output)
            for output, context in zip(packed, contexts, strict=True)
        )
    if len(packed) == 1:
        return packed[0]
    if contexts:
        return ImageOutputBundle(packed, contexts)
    return AlignedImageStack(packed)


class NestedAlignedImageStackKwargResolutionStrategy(
    AlignedImageStackKwargResolutionStrategy
):
    """Select matching slices from kwargs that are already aligned stacks."""

    value_type = AlignedImageStack

    def resolve(
        self,
        value: Any,
        resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        return resolver.resolve(
            value.aligned_slice(
                resolver.projection_axis.require_plane_index(),
                resolver.projection_axis.axis_size,
            )
        )


def compose_aligned_image_payload(
    owner_name: str,
    image_payloads: tuple[Any, ...],
    slice_contexts: Sequence[AlignedImageSliceContext] = (),
    stack_broadcast_source_indices: Sequence[int | None] = (),
    metadata_mode: ImagePayloadMetadataCompositionMode = (
        ImagePayloadMetadataCompositionMode.BUNDLE
    ),
    *,
    retain_single_input: bool = True,
) -> ImagePayloadComposition:
    """Compose one or more image payloads into an executor-ready payload."""
    if not image_payloads:
        raise ValueError(f"{owner_name} cannot compose an empty image input set.")
    broadcast_sources = tuple(stack_broadcast_source_indices)
    if broadcast_sources and len(broadcast_sources) != len(image_payloads):
        raise ValueError(
            f"{owner_name} declared {len(broadcast_sources)} stack-broadcast "
            f"source(s) for {len(image_payloads)} image payload(s)."
        )
    if not broadcast_sources:
        broadcast_sources = (None,) * len(image_payloads)
    for input_index, source_index in enumerate(broadcast_sources):
        if source_index is None:
            continue
        if type(source_index) is not int:
            raise TypeError(
                f"{owner_name} stack-broadcast source index for input "
                f"{input_index} must be an int or None, got "
                f"{type(source_index).__name__}."
            )
        if not 0 <= source_index < len(image_payloads):
            raise ValueError(
                f"{owner_name} stack-broadcast source index {source_index} for "
                f"input {input_index} is outside its {len(image_payloads)} inputs."
            )
        if source_index == input_index:
            raise ValueError(
                f"{owner_name} image input {input_index} cannot broadcast from itself."
            )
    contexts = tuple(slice_contexts)
    if contexts:
        if any(source is not None for source in broadcast_sources):
            raise ValueError(
                f"{owner_name} cannot combine explicit slice contexts with "
                "input-stack broadcast declarations."
            )
        if len(contexts) != len(image_payloads):
            raise ValueError(
                f"{owner_name} declared {len(contexts)} slice context(s) for "
                f"{len(image_payloads)} image payload(s)."
            )
        return ImagePayloadComposition(
            payload=ImageOutputBundle(
                slices=image_payloads,
                slice_contexts=contexts,
            ),
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        )
    aligned_payloads = tuple(
        payload for payload in image_payloads if isinstance(payload, AlignedImageStack)
    )
    if aligned_payloads:
        aligned_inputs = tuple(
            isinstance(payload, AlignedImageStack) for payload in image_payloads
        )
        slice_counts = tuple(len(payload.slices) for payload in aligned_payloads)
        if len(set(slice_counts)) != 1:
            raise ValueError(
                f"{owner_name} aligned image input cardinalities must match "
                f"exactly; got {slice_counts!r}."
            )
        slice_count = slice_counts[0]
        unowned_inputs = tuple(
            input_index
            for input_index, aligned in enumerate(aligned_inputs)
            if not aligned
            and (
                broadcast_sources[input_index] is None
                or not aligned_inputs[broadcast_sources[input_index]]
            )
        )
        if unowned_inputs and slice_count != 1:
            raise ValueError(
                f"{owner_name} cannot mix aligned and unaligned image payloads; "
                "unaligned inputs require an explicit aligned stack owner. "
                f"Unowned input indices: {unowned_inputs!r}."
            )
        if len(aligned_payloads) == 1 and retain_single_input:
            if len(image_payloads) == 1:
                return ImagePayloadComposition(
                    payload=aligned_payloads[0],
                    execution_mode=(
                        ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
                    ),
                )
        declared_contexts = tuple(
            payload.slice_contexts
            for payload in aligned_payloads
            if payload.slice_contexts
        )
        if declared_contexts and any(
            contexts != declared_contexts[0] for contexts in declared_contexts[1:]
        ):
            raise ValueError(
                f"{owner_name} aligned image inputs carry conflicting exact "
                f"slice contexts: {declared_contexts!r}."
            )
        return ImagePayloadComposition(
            payload=AlignedImageStack(
                slices=tuple(
                    ImagePayloadBundleContext.from_payloads(
                        tuple(
                            (
                                payload.slices[slice_index]
                                if isinstance(payload, AlignedImageStack)
                                else payload
                            )
                            for payload in image_payloads
                        ),
                        metadata_mode=metadata_mode,
                    ).compose()
                    for slice_index in range(slice_count)
                ),
                slice_contexts=(declared_contexts[0] if declared_contexts else ()),
            ),
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        )
    if len(image_payloads) == 1 and retain_single_input:
        return ImagePayloadComposition(
            payload=image_payloads[0],
            execution_mode=ImagePayloadExecutionMode.NATURAL,
        )
    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    runtime_slice_counts = tuple(
        RuntimeSliceProjection.slice_count_from_values((payload,))
        for payload in image_payloads
    )
    declared_runtime_slice_counts = tuple(
        count for count in runtime_slice_counts if count is not None
    )
    if declared_runtime_slice_counts:
        if len(set(declared_runtime_slice_counts)) != 1:
            raise ValueError(
                f"{owner_name} runtime-slice image input cardinalities must match "
                f"exactly; got {declared_runtime_slice_counts!r}."
            )
        slice_count = declared_runtime_slice_counts[0]
        unowned_inputs = tuple(
            input_index
            for input_index, count in enumerate(runtime_slice_counts)
            if count is None
            and (
                broadcast_sources[input_index] is None
                or runtime_slice_counts[broadcast_sources[input_index]] is None
            )
        )
        if unowned_inputs and slice_count != 1:
            raise ValueError(
                f"{owner_name} cannot mix runtime-slice-aligned and unaligned "
                "image payloads; unaligned inputs require an explicit "
                "runtime-slice owner. "
                f"Unowned input indices: {unowned_inputs!r}."
            )
        return ImagePayloadComposition(
            payload=AlignedImageStack(
                slices=tuple(
                    ImagePayloadBundleContext.from_payloads(
                        tuple(
                            (
                                RuntimeSliceProjection.value_for_slice(
                                    payload,
                                    RuntimePlaneAxisValueProjection.from_selected_plane(
                                        axis=RuntimePlaneAxis.RUNTIME_SLICE,
                                        plane_index=slice_index,
                                        axis_size=slice_count,
                                    ),
                                )
                                if runtime_slice_counts[input_index] is not None
                                else payload
                            )
                            for input_index, payload in enumerate(image_payloads)
                        ),
                        metadata_mode=metadata_mode,
                    ).compose()
                    for slice_index in range(slice_count)
                )
            ),
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        )
    return ImagePayloadComposition(
        payload=ImagePayloadBundleContext.from_payloads(
            image_payloads,
            metadata_mode=metadata_mode,
        ).compose(),
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )


def payload_slices_for_alignment(payload: Any) -> tuple[Any, ...]:
    """Return slices declared by a nominal runtime-alignment owner."""
    if isinstance(payload, AlignedImageStack):
        return payload.slices
    if isinstance(payload, RuntimeSliceAlignedValueSet):
        return tuple(
            payload.value_for_slice(index) for index in range(payload.slice_count)
        )
    if isinstance(payload, ImagePayloadMetadataCarrier):
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        slice_count = RuntimeSliceProjection.slice_count_from_values((payload,))
        if slice_count is None:
            return (payload,)
        return tuple(
            RuntimeSliceProjection.value_for_slice(
                payload,
                RuntimePlaneAxisValueProjection.from_selected_plane(
                    axis=RuntimePlaneAxis.RUNTIME_SLICE,
                    plane_index=index,
                    axis_size=slice_count,
                ),
            )
            for index in range(slice_count)
        )
    if isinstance(payload, ObjectLabelValue):
        slice_count = payload.runtime_slice_plane_count()
        if slice_count is None:
            return (payload,)
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return tuple(
            RuntimeSliceProjection.value_for_slice(
                payload,
                RuntimePlaneAxisValueProjection.from_selected_plane(
                    axis=RuntimePlaneAxis.RUNTIME_SLICE,
                    plane_index=index,
                    axis_size=slice_count,
                ),
            )
            for index in range(slice_count)
        )
    return (payload,)


def flatten_aligned_image_payload_slices(payload: Any) -> tuple[Any, ...]:
    """Derive scalar image payloads from the nominal aligned-output owner."""
    if isinstance(payload, AlignedImageStack):
        return tuple(
            output_slice for output_slice, _context in payload.projected_output_slices()
        )
    return payload_slices_for_alignment(payload)


def aligned_image_stack_kwargs(
    kwargs: Mapping[str, Any],
    slice_index: int,
    slice_count: int,
    reference_payload: Any | None = None,
) -> dict[str, Any]:
    """Slice runtime-array kwargs alongside an aligned image stack."""
    resolver = AlignedImageStackKwargResolver(
        projection_axis=RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            plane_index=slice_index,
            axis_size=slice_count,
        ),
        reference_payload=reference_payload,
    )
    return {name: resolver.resolve(value) for name, value in kwargs.items()}


def payload_slice_count(payload: Any) -> int:
    """Return the number of aligned slices represented by one payload."""
    return len(payload_slices_for_alignment(payload))
