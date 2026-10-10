"""Generic aligned image-payload composition for multi-source runtime inputs."""

from __future__ import annotations

from _thread import LockType
from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from dataclasses import InitVar, dataclass, field, fields, replace
from enum import Enum
from threading import Lock
from typing import Any, ClassVar, Mapping, TYPE_CHECKING

import numpy as np
from arraybridge import ArrayGeometry

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
    runtime_slice_stack_geometry,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadSliceProjector,
    ImagePayloadMetadataCarrier,
    ImagePayloadMetadataCompositionMode,
    ImageMaskDomain,
    image_payload_data,
    image_payload_geometry,
    image_payload_mask,
    image_payload_metadata,
    project_image_mask_to_data_domain,
    preserved_image_plane_projection,
    with_image_payload_data,
)
from openhcs.core.runtime_array_values import RuntimeArrayData, RuntimeArrayPayload
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.core.runtime_object_labels import ObjectLabelRepresentation
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValueSet
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    SourceSpatialDomainAdapter,
)

if TYPE_CHECKING:
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.steps.function_output_manifest import ProducedOutputSemantics
    from openhcs.core.source_workspace_projection import (
        VirtualWorkspaceSourceProjection,
        VirtualWorkspacePathLookup,
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
                image_payload_metadata(value),
                value_name="Image payload",
            ),
        )

    @classmethod
    def domain_from_metadata(
        cls,
        metadata: ImagePayloadMetadata,
        *,
        fill_value: Any = 0,
        source_domain: SourceSpatialDomain | None = None,
        value_name: str,
    ) -> SourceSpatialDomain:
        domain = metadata.source_spatial_domain
        if source_domain is not None:
            domain = domain.with_missing_from(source_domain)
        return (
            domain.with_missing_from(SourceSpatialDomain(origin_yx=(0, 0)))
            .with_fill_value(fill_value)
            .with_value_name(value_name)
        )

    @property
    def spatial_axes_yx(self) -> tuple[int, int]:
        axes = image_payload_metadata(self.value).spatial_axes_yx(self.value)
        if axes is None:
            raise ValueError(
                "Source-spatial image payload metadata does not declare two "
                f"spatial axes for shape {tuple(np.shape(self.array))!r}."
            )
        return axes

    @property
    def spatial_shape_yx(self) -> tuple[int, int]:
        shape = image_payload_metadata(self.value).spatial_shape_yx(self.value)
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
        metadata = image_payload_metadata(payload)
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
        metadata: ImagePayloadMetadata,
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
        target_domain = replace(
            self.domain,
            origin_yx=target.payload_domain.origin_yx,
            source_shape_yx=target.payload_domain.source_shape_yx,
        )
        metadata = replace(
            image_payload_metadata(materialized),
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
        target_domain = replace(
            self.domain,
            origin_yx=target.payload_domain.origin_yx,
            source_shape_yx=target.payload_domain.source_shape_yx,
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
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjectionStrategy

        return RuntimeSliceProjectionStrategy.aligned_kwarg_value(value, self)

    def resolve_source_spatial_value(self, value: Any) -> Any:
        """Project a nominal value into the declared reference payload domain."""
        if self.reference_payload is None:
            return value
        metadata = image_payload_metadata(self.reference_payload)
        source_shape = metadata.source_spatial_domain.source_shape_yx
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


class ImagePayloadStackComposition(ABC):
    """Compose pixels, masks and provenance on one declared leading axis."""

    @property
    @abstractmethod
    def composition_payloads(self) -> tuple[Any, ...]: ...

    @property
    @abstractmethod
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode: ...

    @staticmethod
    def validate_main_flow_cohort(
        producer_records: Sequence[ProducedOutputSemantics] | None,
    ) -> None:
        """One input cohort has one declared whole-image composition domain."""
        if producer_records and len(
            {record.main_flow_plane_axis for record in producer_records}
        ) != 1:
            raise ValueError(
                "One main-flow cohort cannot combine different declared image axes."
            )

    @staticmethod
    def keeps_single_member_whole(
        payload: RuntimeArrayData,
        *,
        declared_plane_axis: RuntimePlaneAxis | None,
    ) -> bool:
        """Whether a one-member cohort is passed on without a new leading axis.

        Only a member that already spans the cohort axis stays whole: a
        persisted whole image (volume), or a member saved with its declared
        plane axis. A member that declares no plane axis is composed on the
        runtime-slice axis exactly as it is in a cohort of several, so the
        rank a callable receives never depends on how many files matched.
        """
        metadata = image_payload_metadata(payload)
        return metadata.persists_whole_image() or (
            declared_plane_axis is not None
            and declared_plane_axis is metadata.plane_axis
        )

    @staticmethod
    def from_loaded_images(
        payloads: Sequence[RuntimeArrayData],
        *,
        producer_records: Sequence[ProducedOutputSemantics] | None,
        execution_plan: CompiledStepPlan,
        source_projection: VirtualWorkspaceSourceProjection | None,
        workspace_source_lookups: Sequence[VirtualWorkspacePathLookup],
    ) -> RuntimeArrayData:
        """Compose a selected admissible input cohort in its declared image domain."""
        if len(payloads) == 1 and ImagePayloadStackComposition.keeps_single_member_whole(
            payloads[0],
            declared_plane_axis=(
                producer_records[0].main_flow_plane_axis
                if producer_records and len(producer_records) == 1
                else None
            ),
        ):
            main_data_stack = ImagePayloadStackComposition.copy_whole_image(
                payloads[0],
                memory_type=execution_plan.input_memory_type,
                device_id=execution_plan.device_id_for(execution_plan.input_memory_type),
            )
        else:
            metadata_mode = ImagePayloadMetadataCompositionMode.STACK
            if producer_records:
                declared_axis = producer_records[0].main_flow_plane_axis
                # Scalar occurrences of one declared output reconstruct its
                # runtime axis; distinct output contexts introduce a binding axis.
                metadata_mode = (
                    ImagePayloadMetadataCompositionMode.BUNDLE
                    if declared_axis is None
                    and len(
                        {record.output_context for record in producer_records}
                    ) > 1
                    else ImagePayloadMetadataCompositionMode.for_plane_axis(
                        declared_axis or RuntimePlaneAxis.RUNTIME_SLICE
                    )
                )
            if source_projection is not None and workspace_source_lookups:
                metadata_mode = source_projection.payload_composition_mode(
                    workspace_source_lookups
                )
            if metadata_mode is ImagePayloadMetadataCompositionMode.STACK:
                main_data_stack = stack_image_payloads(
                    payloads, metadata_mode=metadata_mode,
                    memory_type=execution_plan.input_memory_type,
                    device_id=execution_plan.device_id_for(execution_plan.input_memory_type),
                )
            elif metadata_mode is ImagePayloadMetadataCompositionMode.BUNDLE:
                main_data_stack = ImagePayloadBundleContext.from_payloads(
                    tuple(payloads), metadata_mode=metadata_mode,
                ).compose()
        return main_data_stack

    @staticmethod
    def copy_whole_image(
        value: RuntimeArrayData,
        *,
        memory_type: str,
        device_id: int | None,
    ) -> RuntimeArrayData:
        """Copy pixels, mask and metadata without adding a composition axis."""
        if isinstance(value, ImagePayloadStackComposition):
            return value.copy_input_cohort(
                memory_type=memory_type, device_id=device_id,
            )
        copied_data = stack_runtime_slices(
            (image_payload_data(value),), memory_type, device_id,
        )[0]
        mask = image_payload_mask(value)
        copied_mask = (
            None if mask is None
            else stack_runtime_slices((mask,), memory_type, device_id)[0]
        )
        return image_payload_metadata(value).replace_fields().payload_with(
            copied_data, copied_mask,
        )

    def copy_input_cohort(
        self, *, memory_type: str, device_id: int | None,
    ) -> RuntimeArrayData:
        """Copy the dense image domain owned by this composition."""
        return self.copy_whole_image(
            self.compose(), memory_type=memory_type, device_id=device_id,
        )

    @staticmethod
    def with_saved_output_context(
        stack_payload: RuntimeArrayData,
        payloads: Sequence[RuntimeArrayData],
        metadata: Sequence[ImagePayloadMetadata],
        *,
        single_output_plane_axis: RuntimePlaneAxis | None,
    ) -> RuntimeArrayData:
        """Attach saved member context without replacing the independent buffer."""
        data = image_payload_data(stack_payload)
        current_intensity = image_payload_metadata(stack_payload)
        if (
            len(payloads) == 1
            and single_output_plane_axis is metadata[0].plane_axis
            and np.shape(data) == np.shape(image_payload_data(payloads[0]))
        ):
            member = metadata[0].with_current_intensity_from(current_intensity).payload_with(
                data, image_payload_mask(stack_payload),
            )
            if ImagePayloadStackComposition.keeps_single_member_whole(
                member, declared_plane_axis=single_output_plane_axis,
            ):
                return member
            # Cache the cohort the next step composes from this one saved member.
            return stack_image_payloads(
                (member,), metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
            )
        if np.shape(data)[:1] != (len(payloads),):
            raise ValueError(
                "Output stack must match its declared output slice count: "
                f"stack shape {np.shape(data)!r}, slice count {len(payloads)}."
            )
        mode = (
            ImagePayloadMetadataCompositionMode.for_plane_axis(
                image_payload_metadata(stack_payload).plane_axis,
            )
            if isinstance(stack_payload, ImagePayloadMetadataCarrier)
            else ImagePayloadMetadataCompositionMode.STACK
        )
        output_metadata = ImagePayloadMetadata.compose(
            tuple(payloads), mode=mode, source_metadata=tuple(
                record.with_current_intensity_from(current_intensity, plane_index=index)
                for index, record in enumerate(metadata)
            ),
        )
        return output_metadata.payload_with(
            data, _stack_image_payload_mask(tuple(payloads), data),
        )

    def composition_source_metadata(
        self, payloads: Sequence[Any] | None = None,
    ) -> tuple[ImagePayloadMetadata, ...]:
        return tuple(
            self.composition_payload_metadata(image_payload_metadata(payload))
            for payload in (self.composition_payloads if payloads is None else payloads)
        )

    def composition_payload_metadata(
        self, metadata: ImagePayloadMetadata
    ) -> ImagePayloadMetadata:
        """Preserve each input's declared provenance unless the axis owner projects it."""
        return metadata

    @staticmethod
    def composition_memory_domain(
        payloads: tuple[RuntimeArrayData, ...], *,
        memory_type: str | None = None, device_id: int | None = None,
    ) -> tuple[str, int | None]:
        """Resolve one composition destination through the original memory owner."""
        if memory_type is not None:
            return memory_type, device_id
        memory_type = detect_memory_type(payloads[0])
        return memory_type, MemoryType(memory_type).device_id_of(payloads[0])

    def compose(
        self, *, memory_type: str | None = None, device_id: int | None = None,
    ) -> Any:
        # Resolve the destination from the original carrier before reconciliation.
        memory_type, device_id = self.composition_memory_domain(
            tuple(image_payload_data(payload) for payload in self.composition_payloads),
            memory_type=memory_type, device_id=device_id,
        )
        payloads = ImagePayloadMetadata.intensity_coherent_payloads(self.composition_payloads)
        composed = self.compose_unmasked(
            tuple(image_payload_data(payload) for payload in payloads),
            memory_type=memory_type, device_id=device_id,
        )
        metadata = ImagePayloadMetadata.compose(
            payloads,
            mode=self.composition_metadata_mode,
            source_metadata=self.composition_source_metadata(payloads),
        )
        return metadata.payload_with(composed, self.compose_mask(composed, metadata))

    def compose_unmasked(
        self, payloads: tuple[RuntimeArrayData, ...], *,
        memory_type: str | None = None, device_id: int | None = None,
    ) -> RuntimeArrayData:
        memory_type, device_id = self.composition_memory_domain(
            payloads, memory_type=memory_type, device_id=device_id,
        )
        return stack_runtime_slices(
            payloads, memory_type, device_id,
        )

    def compose_mask(self, composed: Any, metadata: ImagePayloadMetadata) -> Any | None:
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
    memory_type: str | None = None,
    device_id: int | None = None,
) -> Any:
    """Stack image payloads in their declared memory domain with full context."""

    return ImagePayloadStackContext(image_payloads, metadata_mode).compose(
        memory_type=memory_type, device_id=device_id,
    )


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
            image_payload_metadata(payload)
            .mask_domain(slice_domain)
            .broadcast_to_data(mask)
            for payload, slice_domain, mask in zip(
                payloads, output_slice_domains, resolved_masks, strict=True
            )
        )
    return stack_runtime_slices(
        resolved_masks,
        detect_memory_type(stack),
        MemoryType(detect_memory_type(stack)).device_id_of(stack),
    )


def _complete_image_payload_mask(
    payload: Any,
    payload_data: RuntimeArrayData,
    mask: RuntimeArrayData | None,
) -> RuntimeArrayData:
    mask_domain = image_payload_metadata(payload).mask_domain(payload_data)
    if mask is not None:
        if not mask_domain.accepts(tuple(np.shape(mask))):
            raise ValueError(
                "Image payload mask must match the selected output slice "
                f"domain; got mask {tuple(np.shape(mask))!r} for slice "
                f"{tuple(np.shape(payload_data))!r}."
            )
        return project_image_mask_to_data_domain(
            mask, payload_data, metadata=image_payload_metadata(payload),
        )
    data = image_payload_data(payload_data)
    return MemoryType(detect_memory_type(data)).ones_like(
        data, shape=mask_domain.default_mask_shape(), dtype=bool,
    )


def unstack_image_payload_context(
    payload: Any,
    slices: Sequence[Any],
    *,
    default_plane_axis: RuntimePlaneAxis | None = None,
) -> list[Any]:
    """Attach one source plane of payload context to each unstacked image slice."""
    mask = image_payload_mask(payload)
    metadata = image_payload_metadata(payload)
    if mask is None and not metadata.has_values:
        return list(slices)
    if metadata.plane_axis is None and default_plane_axis is not None:
        metadata = replace(metadata, plane_axis=default_plane_axis)
    projector = ImagePayloadSliceProjector(mask=mask, metadata=metadata)
    return projector.payloads_for_slices(slices)


@dataclass(frozen=True, slots=True)
class ImagePayloadComposition:
    """Resolved image payload plus its execution mode."""

    payload: Any
    execution_mode: ImagePayloadExecutionMode

    @property
    def plane_axis(self) -> RuntimePlaneAxis | None:
        """Return the invocation axis, distinct from a bundle's inner source axis."""
        if isinstance(self.payload, AlignedImageStack):
            return RuntimePlaneAxis.RUNTIME_SLICE
        return image_payload_metadata(self.payload).plane_axis

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
                metadata.plane_axis,
                metadata.source_image_names,
                tuple(np.shape(image_payload_data(payload))),
            )
            for index, (payload, metadata) in enumerate(
                zip(self.payloads, self.source_metadata, strict=True)
            )
            if metadata.plane_axis is not None
        )
        if declared_axes:
            raise ValueError(
                "Same-slice image bundles require every payload plane axis to be "
                f"projected before composition; got {declared_axes!r}."
            )

    @property
    def source_metadata(self) -> tuple[ImagePayloadMetadata, ...]:
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
        metadata: ImagePayloadMetadata,
    ) -> Any | None:
        masks = self.present_masks
        if not masks:
            return None
        shared_spatial_shape = metadata.mask_domain(composed).shared_spatial_mask_shape
        if shared_spatial_shape is not None and all(
            tuple(np.shape(mask)) == shared_spatial_shape for mask in masks
        ):
            return self.combined_mask(composed)
        resolved_masks = tuple(
            _complete_image_payload_mask(payload, data, mask)
            for payload, data, mask in zip(
                self.payloads,
                self.data_payloads,
                self.masks,
                strict=True,
            )
        )
        shapes = tuple(image_payload_geometry(mask).shape for mask in resolved_masks)
        if any(shape != shapes[0] for shape in shapes[1:]):
            resolved_masks = tuple(
                metadata.for_leading_source_plane(index)
                .mask_domain(composed[index])
                .broadcast_to_data(mask)
                for index, mask in enumerate(resolved_masks)
            )
        memory_type = detect_memory_type(image_payload_data(composed))
        memory_type_owner = MemoryType(memory_type)
        stacked = stack_runtime_slices(
            resolved_masks,
            memory_type,
            memory_type_owner.device_id_of(image_payload_data(composed)),
        )
        return memory_type_owner.astype(stacked, bool)

    def combined_mask(self, composed: Any) -> RuntimeArrayData | None:
        masks = self.present_masks
        if not masks:
            return None
        mask_shapes = tuple(tuple(np.shape(mask)) for mask in masks)
        if any(shape != mask_shapes[0] for shape in mask_shapes[1:]):
            raise ValueError(
                "Image bundle mask intersection requires one exact declared "
                f"spatial mask shape; got {mask_shapes!r}."
            )
        data = image_payload_data(composed)
        memory_type = MemoryType(detect_memory_type(data))
        device_id = memory_type.device_id_of(data)
        prepared = tuple(
            memory_type.astype(
                MemoryType(detect_memory_type(mask)).convert_to(mask, memory_type, device_id),
                bool,
            )
            for mask in masks
        )
        combined = prepared[0]
        for mask in prepared[1:]:
            combined = memory_type.logical_and(
                combined,
                mask,
            )
        return combined

    def compose_unmasked(
        self,
        payloads: tuple[RuntimeArrayData, ...],
        *, memory_type: str | None = None, device_id: int | None = None,
    ) -> RuntimeArrayData:
        """Compose image payload arrays without mask/metadata wrapping."""
        memory_type, device_id = self.composition_memory_domain(
            payloads, memory_type=memory_type, device_id=device_id,
        )
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
            return super(ImagePayloadBundleContext, self).compose_unmasked(
                payloads, memory_type=memory_type, device_id=device_id,
            )
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
        target = MemoryType(memory_type)
        prepared_payloads = tuple(
            convert_memory(
                data=payload,
                source_type=detect_memory_type(payload),
                target_type=memory_type,
                gpu_id=device_id,
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
            for payload, axis in zip(prepared_payloads, channel_axes, strict=True)
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
            for payload, axis in zip(prepared_payloads, channel_axes, strict=True)
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
                else target.broadcast_to(
                    target.reshape(
                        payload,
                        (*payload.shape[:channel_axis], 1, *payload.shape[channel_axis:]),
                    ),
                    (*payload.shape[:channel_axis], channel_count, *payload.shape[channel_axis:]),
                )
            )
            for payload, axis in zip(prepared_payloads, channel_axes, strict=True)
        )
        return target.stack_arrays(list(promoted), device_id)


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
        metadata = image_payload_metadata(payload)
        return metadata.with_source_provenance(
            metadata.source_provenance.with_derived_source_image_names(
                (self.output_key,)
            )
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
class ImagePayloadSliceStack(
    ImagePayloadStackComposition, RuntimeArrayPayload, ImagePayloadMetadataCarrier,
):
    """Shared slice storage, projection, and publication for image stacks."""

    slices: tuple[Any, ...]
    slice_contexts: tuple[AlignedImageSliceContext, ...] = ()
    @classmethod
    def from_output_slices(
        cls,
        slices: Sequence[Any],
        *,
        memory_type: str,
        plane_axis: RuntimePlaneAxis,
    ) -> "ProducedImageStack":
        """Admit a produced literal image stack without allocating its pixels."""
        return ProducedImageStack(
            tuple(slices), memory_type=memory_type, plane_axis=plane_axis,
        )

    @property
    def metadata(self) -> ImagePayloadMetadata:
        return ImagePayloadMetadata.compose(
            self.composition_payloads,
            mode=self.composition_metadata_mode,
            source_metadata=self.composition_source_metadata(),
        )

    @property
    def shape(self) -> tuple[int, ...]:
        return runtime_slice_stack_geometry(
            tuple(image_payload_geometry(payload) for payload in self.composition_payloads)
        ).shape

    @property
    def ndim(self) -> int:
        return len(self.shape)

    @property
    def dtype(self) -> Any:
        return image_payload_data(self.compose()).dtype

    def __array__(self, dtype: Any | None = None, copy: bool | None = None) -> Any:
        data = np.asarray(self.array_payload_data(), dtype=dtype)
        return data.copy() if copy else data

    def __getitem__(self, key: Any) -> Any:
        return self.array_payload_data()[key]

    def __len__(self) -> int:
        return len(self.slices)

    def image_data(self) -> Any:
        return self.array_payload_data()

    def image_geometry(self) -> ArrayGeometry:
        return ArrayGeometry(self.shape)

    def image_mask(self) -> Any | None:
        return image_payload_mask(self.compose())

    def array_payload_data(self) -> Any:
        return image_payload_data(self.compose())

    def with_data(self, data: Any) -> Any:
        return self.metadata.payload_with(data, image_payload_mask(self.compose()))

    @property
    def composition_payloads(self) -> tuple[Any, ...]:
        return self.slices

    @property
    def projected_output_composition_mode(self) -> ImagePayloadMetadataCompositionMode | None:
        """Declare the outer runtime axis retained by projected output members."""
        return self.composition_metadata_mode

    @property
    def runtime_slice_count(self) -> int | None:
        return len(self.slices)

    def plane_axis_for_output_context(
        self, context: AlignedImageSliceContext,
    ) -> RuntimePlaneAxis | None:
        """An explicitly aligned stack declares its outer runtime-slice domain."""
        return RuntimePlaneAxis.RUNTIME_SLICE

    def __post_init__(self) -> None:
        self.slices = tuple(self.slices)
        self.slice_contexts = tuple(self.slice_contexts)
        if not self.slices:
            raise ValueError(f"{type(self).__name__}.slices cannot be empty.")
        if self.slice_contexts and len(self.slice_contexts) != len(self.slices):
            raise ValueError(
                f"{type(self).__name__}.slice_contexts must be empty or match slices; "
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

    def with_slices(self, slices: Sequence[Any]) -> "ImagePayloadSliceStack":
        """Replace payload slices while preserving the concrete alignment owner."""

        return type(self)(tuple(slices), self.slice_contexts)

    def copy_input_cohort(
        self, *, memory_type: str, device_id: int | None,
    ) -> "ImagePayloadSliceStack":
        """Retain aligned member domains while admitting independent buffers."""
        return self.with_slices(
            tuple(
                self.copy_whole_image(
                    payload, memory_type=memory_type, device_id=device_id,
                )
                for payload in self.slices
            )
        )

    def projected_output_slices(
        self,
    ) -> Iterator[tuple[Any, AlignedImageSliceContext | None]]:
        """Project each output once together with its declaration-owned context."""
        contexts = self.slice_contexts or (None,) * len(self.slices)
        for payload, context in zip(self.slices, contexts, strict=True):
            if image_payload_metadata(payload).persists_whole_image():
                yield payload, context
            else:
                for output_slice in payload_slices_for_alignment(payload):
                    yield output_slice, context

    def copy_projected_output_stack(
        self,
        projected_outputs: Sequence[tuple[Any, AlignedImageSliceContext | None]],
        *,
        memory_type: str,
        device_id: int | None,
    ) -> RuntimeArrayData | None:
        """Prepare an independent output buffer in this owner's declared domain."""
        payloads = tuple(payload for payload, _context in projected_outputs)
        metadata_mode = self.projected_output_composition_mode
        if metadata_mode is None:
            return self.copy_whole_image(
                payloads[0], memory_type=memory_type, device_id=device_id,
            )
        data = tuple(image_payload_data(payload) for payload in payloads)
        declared_axes = {
            self.plane_axis_for_output_context(context)
            for _payload, context in projected_outputs
        }
        if len(declared_axes) != 1 or len({tuple(np.shape(item)) for item in data}) != 1:
            return None
        if metadata_mode is ImagePayloadMetadataCompositionMode.BUNDLE:
            return ImagePayloadBundleContext.from_payloads(
                payloads, metadata_mode=metadata_mode,
            ).compose()
        return stack_image_payloads(
            payloads, metadata_mode=metadata_mode,
            memory_type=memory_type, device_id=device_id,
        )

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
class AlignedImageStack(ImagePayloadSliceStack):
    """Per-runtime-slice bundles of separately bound image inputs or outputs."""

    @property
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode:
        return ImagePayloadMetadataCompositionMode.STACK

    def composition_payload_metadata(
        self, metadata: ImagePayloadMetadata
    ) -> ImagePayloadMetadata:
        """Inner image bundles contribute provenance, not an outer slice axis."""
        metadata = super(AlignedImageStack, self).composition_payload_metadata(metadata)
        return metadata.with_source_provenance(
            metadata.source_provenance.with_runtime_planes_as_contributors()
        )


@dataclass(slots=True, kw_only=True)
class ProducedImageStack(ImagePayloadSliceStack):
    """Borrowed produced image slices with one canonical dense realization.

    Produced pixels retain their literal values and heterogeneous numeric dtype
    promotion, unlike input bundles which reconcile intensity domains. Producer
    references may change pixels before realization, matching borrowed PURE3D
    publication. After realization scalar views refer to the canonical buffer.
    """

    memory_type: str
    plane_axis: RuntimePlaneAxis
    source_metadata: InitVar[ImagePayloadMetadata | None] = None
    _metadata: ImagePayloadMetadata = field(init=False, repr=False)
    _composed_payload: RuntimeArrayData | None = field(default=None, init=False, repr=False)
    _realization_lock: LockType = field(
        default_factory=Lock, init=False, repr=False, compare=False,
    )

    def __post_init__(self, source_metadata: ImagePayloadMetadata | None) -> None:
        super(ProducedImageStack, self).__post_init__()
        MemoryType(self.memory_type)
        data_geometry = runtime_slice_stack_geometry(
            tuple(image_payload_data(payload) for payload in self.slices)
        )
        masks = tuple(image_payload_mask(payload) for payload in self.slices)
        present_masks = tuple(mask for mask in masks if mask is not None)
        if present_masks and len(present_masks) != len(masks):
            raise ValueError("Cannot aggregate a mix of masked and unmasked image payloads.")
        self._metadata = (
            ImagePayloadMetadata.compose(
                self.slices,
                mode=ImagePayloadMetadataCompositionMode.for_plane_axis(self.plane_axis),
            )
            if source_metadata is None else source_metadata
        )
        if self._metadata.plane_axis is not self.plane_axis:
            raise ValueError("Produced image metadata must retain its declared plane axis.")
        shared_mask = (
            self._shared_image_mask(present_masks, data_geometry) if present_masks else None
        )
        mask_geometry = (
            image_payload_geometry(shared_mask)
            if shared_mask is not None else (
                runtime_slice_stack_geometry(present_masks) if present_masks else None
            )
        )
        if mask_geometry is not None and not self._metadata.mask_domain(
            data_geometry
        ).accepts(mask_geometry.shape):
            raise ValueError(
                "MaskedImagePayload.mask shape must match the image spatial "
                f"domain; got mask {mask_geometry.shape!r} for image {data_geometry.shape!r}."
            )

    @property
    def metadata(self) -> ImagePayloadMetadata:
        return self._metadata

    @property
    def composition_metadata_mode(self) -> ImagePayloadMetadataCompositionMode:
        return ImagePayloadMetadataCompositionMode.for_plane_axis(self.plane_axis)

    @property
    def dtype(self) -> Any:
        return np.result_type(
            *(
                MemoryType(detect_memory_type(image_payload_data(payload)))
                .canonical_dtype_name(image_payload_data(payload).dtype)
                for payload in self.slices
            )
        )

    def plane_axis_for_output_context(
        self, context: AlignedImageSliceContext,
    ) -> RuntimePlaneAxis:
        return self.plane_axis

    @property
    def runtime_slice_count(self) -> int | None:
        if self.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE:
            return len(self.slices)
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return RuntimeSliceProjection.slice_count_from_values(self.slices)

    def image_memory_type(self) -> str:
        return self.memory_type

    def with_metadata(self, metadata: ImagePayloadMetadata) -> Any:
        if (
            self._composed_payload is not None
            or metadata.plane_axis is not self.plane_axis
            or metadata.source_channel_axis != self._metadata.source_channel_axis
            or metadata.source_spatial_domain != self._metadata.source_spatial_domain
        ):
            return super(ProducedImageStack, self).with_metadata(metadata)
        slices = tuple(
            metadata.for_leading_source_plane(index).payload_with(
                image_payload_data(payload), image_payload_mask(payload),
            )
            for index, payload in enumerate(self.slices)
        )
        return type(self)(
            slices, self.slice_contexts, memory_type=self.memory_type,
            plane_axis=self.plane_axis, source_metadata=metadata,
        )

    def normalize_intensity_payload(
        self, *, dtype: Any = None, channel_index: int = 0,
    ) -> Any:
        if self._metadata.normalization_dtype(self.dtype, dtype) is None:
            return self
        return self._metadata.normalize_intensity_payload(
            self.compose(), dtype=dtype, channel_index=channel_index,
        )

    def _shared_image_mask(
        self, masks: tuple[Any, ...], data_geometry: ArrayGeometry,
    ) -> Any | None:
        first = masks[0]
        if all(mask is first for mask in masks) and self._metadata.mask_domain(
            data_geometry
        ).accepts(image_payload_geometry(first).shape):
            return first
        return None

    def image_mask(self) -> Any | None:
        if self._composed_payload is not None:
            return image_payload_mask(self._composed_payload)
        masks = tuple(image_payload_mask(payload) for payload in self.slices)
        if masks[0] is None:
            return None
        shared = self._shared_image_mask(masks, self.image_geometry())
        return shared if shared is not None else image_payload_mask(self.compose())

    def _materialized_image_mask(self) -> Any | None:
        masks = tuple(image_payload_mask(payload) for payload in self.slices)
        if masks[0] is None:
            return None
        shared = self._shared_image_mask(masks, self.image_geometry())
        return shared if shared is not None else stack_runtime_slices(
            masks, self.memory_type, 0,
        )

    def __getstate__(self) -> dict[str, Any]:
        """Transport one pixel representation, never dense data plus slice copies."""
        with self._realization_lock:
            state = {
                declaration.name: getattr(self, declaration.name)
                for declaration in fields(self)
            }
            del state["_realization_lock"]
            if self._composed_payload is not None:
                del state["slices"]
            return state

    def __setstate__(self, state: dict[str, Any]) -> None:
        for name, value in state.items():
            setattr(self, name, value)
        self._realization_lock = Lock()
        if self._composed_payload is not None:
            self._retain_composed_slices()

    def _retain_composed_slices(self) -> None:
        data = image_payload_data(self._composed_payload)
        mask = image_payload_mask(self._composed_payload)
        projector = ImagePayloadSliceProjector(mask, self._metadata)
        self.slices = tuple(
            projector.payload_for_slice(data[index], index)
            for index in range(data.shape[0])
        )

    def with_slices(self, slices: Sequence[Any]) -> "ProducedImageStack":
        return type(self)(
            tuple(slices), self.slice_contexts,
            memory_type=self.memory_type, plane_axis=self.plane_axis,
        )

    def copy_input_cohort(
        self, *, memory_type: str, device_id: int | None,
    ) -> "ProducedImageStack":
        """Snapshot literal produced pixels directly into canonical storage.

        Input isolation and dense realization share one allocation. Copying
        each borrowed member first would make placement stack those independent
        copies into a second buffer, including a second copy of every mask.
        """
        data = stack_runtime_slices(
            tuple(image_payload_data(payload) for payload in self.slices),
            memory_type, device_id,
        )
        masks = tuple(image_payload_mask(payload) for payload in self.slices)
        mask = None
        if masks[0] is not None:
            shared = self._shared_image_mask(masks, self.image_geometry())
            mask = (
                stack_runtime_slices(masks, memory_type, device_id)
                if shared is None else stack_runtime_slices(
                    (shared,), memory_type, device_id,
                )[0]
            )
        metadata = self._metadata.replace_fields()
        copied = type(self)(
            self.slices, self.slice_contexts, memory_type=memory_type,
            plane_axis=self.plane_axis, source_metadata=metadata,
        )
        copied._composed_payload = metadata.payload_with(data, mask)
        copied._retain_composed_slices()
        return copied

    def compose(
        self, *, memory_type: str | None = None, device_id: int | None = None,
    ) -> Any:
        with self._realization_lock:
            if self._composed_payload is None:
                data = stack_runtime_slices(
                    tuple(image_payload_data(payload) for payload in self.slices),
                    self.memory_type, 0,
                )
                self._composed_payload = self._metadata.payload_with(
                    data, self._materialized_image_mask(),
                )
                self._retain_composed_slices()
        if memory_type is None:
            return self._composed_payload
        target = MemoryType(memory_type)
        data = image_payload_data(self._composed_payload)
        source = MemoryType(detect_memory_type(data))
        if source is target and source.device_id_of(data) == device_id:
            return self._composed_payload
        mask = image_payload_mask(self._composed_payload)
        return self._metadata.payload_with(
            source.convert_to(data, target, device_id),
            None if mask is None else MemoryType(detect_memory_type(mask)).convert_to(
                mask, target, device_id,
            ),
        )


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
    def projected_output_composition_mode(self) -> ImagePayloadMetadataCompositionMode | None:
        """Flatten declared inner runtime planes, retaining other named image domains."""
        if any(
            image_payload_metadata(payload).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
            for payload in self.slices
        ):
            return ImagePayloadMetadataCompositionMode.STACK
        if len(self.slices) == 1:
            return None
        return self.composition_metadata_mode

    def plane_axis_for_output_context(
        self, context: AlignedImageSliceContext,
    ) -> RuntimePlaneAxis | None:
        """Resolve a named output's original inner domain before leaf projection."""
        payloads = tuple(
            payload for payload, declared_context in zip(self.slices, self.slice_contexts, strict=True)
            if declared_context == context
        )
        if len(payloads) != 1:
            raise ValueError(
                "Named image output context requires exactly one original payload: "
                f"{context!r}; found {len(payloads)}."
            )
        return image_payload_metadata(payloads[0]).plane_axis

    def composition_payload_metadata(
        self, metadata: ImagePayloadMetadata
    ) -> ImagePayloadMetadata:
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
    if isinstance(payload, ImagePayloadSliceStack):
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
    if isinstance(payload, ImagePayloadSliceStack):
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
