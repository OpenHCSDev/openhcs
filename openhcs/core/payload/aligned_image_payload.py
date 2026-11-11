"""Generic aligned image-payload composition for multi-source runtime inputs."""

from __future__ import annotations

from metaclass_registry import AutoRegisterMeta

from openhcs.core.payload.runtime_plane_projection import NoPlaneAxis
from openhcs.core.payload.runtime_plane_projection import RuntimeSlicePlaneAxis, SourceBindingPlaneAxis

from _thread import LockType
from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from dataclasses import InitVar, dataclass, field, fields
from threading import Lock
from typing import Any, ClassVar, Mapping

import numpy as np
from arraybridge import ArrayGeometry


from openhcs.core.artifacts.plans import ArtifactOutputPlan, ArtifactSpecRef
from openhcs.core.memory import (
    MemoryType,
    convert_memory,
    detect_memory_type,
    stack_runtime_slices,
    runtime_slice_stack_geometry,
)
from openhcs.core.payload.runtime_image_values import ImagePayload, ImagePayloadMetadata, ImagePayloadSliceProjector, ImagePayloadSourceSpatialDomainAdapter, project_image_mask_to_data_domain

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from openhcs.core.payload.runtime_image_values import ImageMaskDomain
from openhcs.core.payload.runtime_array_values import RuntimeArrayData, array_geometry
from openhcs.core.payload.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.payload.runtime_slice_projection import preserved_image_plane_projection
from openhcs.core.source.source_image_provenance import SourceImageProvenance
from openhcs.core.source.source_spatial_domain import (
    SourceSpatialDomainAdapter,
)
from openhcs.core.axes.axis_declarations import ColourAxis
from openhcs.core.payload.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.payload.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.payload.runtime_image_values import RuntimeSliceProjectionDeclarationError


class ImagePayloadExecutionMode(ABC, metaclass=AutoRegisterMeta):
    """How a runtime executor should interpret a resolved image payload."""

    __registry_key__ = "key"
    __skip_if_no_key__ = True

    key: ClassVar[str | None] = None
    per_plane: ClassVar[bool] = False
    """The processing contract may split the payload into planes."""
    whole_stack: ClassVar[bool] = False
    """The payload is one whole stack handed to one call."""

    @classmethod
    @abstractmethod
    def execute(
        cls,
        contract: type["ProcessingContract"],
        call: "ContractCall",
        image: Any,
        kwargs: dict[str, Any],
    ) -> Any:
        """Execute ``call.func`` on ``image`` in this mode."""

    @classmethod
    def batch_request(
        cls, request: "RuntimeBatchInvocationRequest",
    ) -> "RuntimeBatchInvocationRequest | None":
        """Project a request into a batch executor's image domain, or ``None``."""
        return request

    @classmethod
    def executable_payload(cls, payload: Any) -> Any:
        """Return the payload a measurement callable receives in this mode."""

        return RuntimeSliceProjection.full_stack_value(payload)

    @classmethod
    def for_payload_scoped_labels(
        cls, runtime_slice_count: int | None,
    ) -> type[ImagePayloadExecutionMode]:
        """Return the mode for labels whose domain is the whole payload."""
        del runtime_slice_count
        return FullStackExecution

    @classmethod
    def for_plane_scoped_labels(
        cls, projection: "RuntimePlaneAxisValueProjection | None",
    ) -> type[ImagePayloadExecutionMode]:
        """Return the mode for labels that still carry an unprojected plane axis."""
        del projection
        return cls


class NaturalExecution(ImagePayloadExecutionMode):
    """The callable's processing contract decides how the payload executes."""

    key = "natural"
    per_plane = True

    @classmethod
    def execute(cls, contract, call, image, kwargs):
        return contract.execute(call, image, kwargs)


class FullStackExecution(ImagePayloadExecutionMode):
    """One call on the whole stack, whatever the contract."""

    key = "full_stack"
    whole_stack = True

    @classmethod
    def execute(cls, contract, call, image, kwargs):
        return contract.execute_whole_stack(call, image, kwargs)

    @classmethod
    def for_plane_scoped_labels(cls, projection):
        raise ValueError(
            "Slice-aligned object measurement cannot execute a full-stack image "
            "with an unprojected object-label plane domain: "
            f"{projection!r}."
        )


class AlignedStackExecution(ImagePayloadExecutionMode):
    """One call per runtime slice of an aligned multi-image stack."""

    key = "aligned_multi_image_stack"

    @classmethod
    def executable_payload(cls, payload: Any) -> Any:
        return payload

    @classmethod
    def for_payload_scoped_labels(cls, runtime_slice_count):
        return cls if runtime_slice_count == 1 else FullStackExecution

    @classmethod
    def batch_request(cls, request):
        from dataclasses import replace

        from openhcs.core.payload.aligned_image_payload import (
            AlignedImageStack,
            aligned_image_stack_kwargs,
        )

        if not isinstance(request.image, AlignedImageStack):
            raise TypeError(
                "Aligned runtime batch execution requires AlignedImageStack, got "
                f"{type(request.image).__name__}."
            )
        projection = RuntimePlaneAxisValueProjection.require_runtime_slice_projection(
            request.plane_projection,
            "Aligned runtime batch execution requires a compiled runtime-slice "
            "projection.",
        )
        if projection.selects_one_plane:
            raise ValueError(
                "Aligned runtime batch execution received an image after its "
                "runtime-slice projection was already selected."
            )
        if projection.axis_size != len(request.image.slices):
            raise ValueError(
                "Aligned runtime batch image cardinality conflicts with its "
                f"compiled projection: {len(request.image.slices)} != "
                f"{projection.axis_size}."
            )
        if projection.axis_size != 1:
            return None
        projected_image = RuntimeSliceProjection.value_for_slice(
            request.image,
            projection.selected_plane(0),
        )
        return replace(
            request,
            image=projected_image,
            kwargs=aligned_image_stack_kwargs(
                request.kwargs,
                0,
                1,
                reference_payload=projected_image,
            ),
            execution_mode=FullStackExecution,
            plane_projection=None,
        )

    @classmethod
    def execute(cls, contract, call, image, kwargs):
        from openhcs.core.payload.aligned_image_payload import (
            AlignedImageStack,
            aligned_image_stack_kwargs,
        )
        from openhcs.core.callable.processing_contracts import (
            Pure2DAuxiliaryOutputAggregator,
            Pure2DSliceResultBatch,
        )
        from openhcs.core.callable.runtime_batch_contracts import (
            Pure2DSliceBatchExecutor,
            RuntimePure2DSliceBatchRequest,
        )

        callable_contract = call.callable_contract
        owner = (
            f"Callable {callable_contract.module_name!r}/"
            f"{callable_contract.function_name!r}"
        )
        if not isinstance(image, AlignedImageStack):
            raise TypeError(
                f"{owner} requires AlignedImageStack for aligned multi-image "
                f"stack execution, got {type(image).__name__}."
            )
        projection = call.plane_projection
        if projection is None:
            raise RuntimeSliceProjectionDeclarationError(
                f"{owner} requires a compiled runtime-slice projection for "
                "aligned multi-image stack execution."
            )
        projection.axis.require_runtime_slices(
            f"{owner} aligned image execution requires "
            f"RuntimeSlicePlaneAxis, got {projection.axis!r}.",
            error=RuntimeSliceProjectionDeclarationError,
        )
        if projection.selects_one_plane:
            raise RuntimeSliceProjectionDeclarationError(
                f"{owner} received an AlignedImageStack after the compiled "
                "runtime-slice projection already selected plane "
                f"{projection.plane_index}."
            )
        if projection.axis_size != len(image.slices):
            raise RuntimeSliceProjectionDeclarationError(
                f"{owner} aligned image cardinality conflicts with its compiled "
                f"runtime-slice projection: {len(image.slices)} != "
                f"{projection.axis_size}."
            )
        if contract.whole_stack_only:
            slice_plane_axes = tuple(
                slice_payload.metadata.plane_axis for slice_payload in image.slices
            )
            if not all(
                plane_axis.one_plane_per_source_binding
                for plane_axis in slice_plane_axes
            ):
                raise ValueError(
                    f"{owner} with whole-stack contract {contract.key!r} requires "
                    "every aligned image slice to declare "
                    f"SourceBindingPlaneAxis; got {slice_plane_axes!r}."
                )

        def execute_aligned_stack_slice(
            slice_func, slice_payload, slice_kwargs, slice_index, slice_count,
        ):
            return call.invoke(
                slice_payload,
                aligned_image_stack_kwargs(
                    slice_kwargs,
                    slice_index,
                    slice_count,
                    reference_payload=slice_payload,
                ),
                func=slice_func,
            )

        slice_results = Pure2DSliceBatchExecutor.from_executors(call.batch_executors)(
            RuntimePure2DSliceBatchRequest(
                func=call.func,
                slices_2d=tuple(
                    RuntimeSliceProjection.value_for_slice(
                        image,
                        projection.selected_plane(slice_index),
                    )
                    for slice_index in range(projection.axis_size)
                ),
                kwargs=kwargs,
                execute_slice=execute_aligned_stack_slice,
                signature=call.signature,
            )
        )
        result_batch = Pure2DSliceResultBatch.from_results(slice_results)
        canonical_specs = callable_contract.canonical_return_output_specs.specs
        trailing_specs = callable_contract.trailing_return_output_specs.specs
        function_name = callable_contract.function_name
        if len(result_batch.auxiliary_groups) != len(trailing_specs):
            raise ValueError(
                f"{function_name} returned "
                f"{len(result_batch.auxiliary_groups)} trailing output position(s); "
                f"the compiled CallableContract declares {len(trailing_specs)}."
            )
        memory_type = detect_memory_type(image.slices[0].data)
        if canonical_specs:
            if all(
                isinstance(output, AlignedImageStack)
                for output in result_batch.main_outputs
            ):
                aligned_main_output = Pure2DAuxiliaryOutputAggregator.aggregate(
                    result_batch.main_outputs,
                    memory_type,
                    plane_axis=RuntimeSlicePlaneAxis,
                )
                if not isinstance(aligned_main_output, AlignedImageStack):
                    raise TypeError(
                        f"{function_name} must preserve aligned canonical image "
                        "outputs as AlignedImageStack, got "
                        f"{type(aligned_main_output).__name__}."
                    )
                if len(aligned_main_output.slices) != len(canonical_specs):
                    raise ValueError(
                        f"{function_name} produced "
                        f"{len(aligned_main_output.slices)} aligned main-flow "
                        f"value(s) for {len(canonical_specs)} declared output "
                        "spec(s)."
                    )
                stacked_main_output = (
                    aligned_main_output.slices[0]
                    if len(canonical_specs) == 1
                    else aligned_main_output
                )
            elif len(canonical_specs) == 1:
                stacked_main_output = Pure2DAuxiliaryOutputAggregator.aggregate(
                    result_batch.main_outputs,
                    memory_type,
                    plane_axis=RuntimeSlicePlaneAxis,
                )
            elif len(canonical_specs) == len(result_batch.main_outputs):
                stacked_main_output = AlignedImageStack(
                    tuple(result_batch.main_outputs)
                )
            else:
                raise ValueError(
                    f"{function_name} produced "
                    f"{len(result_batch.main_outputs)} aligned main-flow value(s) "
                    f"for {len(canonical_specs)} declared output spec(s)."
                )
            if len(canonical_specs) > 1 and not isinstance(
                stacked_main_output, AlignedImageStack
            ):
                raise TypeError(
                    f"{function_name} must aggregate multiple declared canonical "
                    "image outputs into AlignedImageStack, got "
                    f"{type(stacked_main_output).__name__}."
                )
        else:
            stacked_main_output = RuntimeSliceAlignedValues(
                slices=tuple(result_batch.main_outputs)
            )
        if not result_batch.auxiliary_groups:
            return stacked_main_output
        return (
            stacked_main_output,
            *(
                Pure2DAuxiliaryOutputAggregator.aggregate(
                    values,
                    memory_type,
                    plane_axis=RuntimeSlicePlaneAxis,
                )
                for values in result_batch.auxiliary_groups
            ),
        )


@dataclass(frozen=True, slots=True)
class AlignedImageStackKwargResolver:
    """Materialize one kwarg for a specific aligned image-stack slice."""

    projection_axis: "RuntimePlaneAxisValueProjection"
    reference_payload: Any | None = None

    def resolve(self, value: Any) -> Any:

        return RuntimeSliceProjection.aligned_value(value, self)

    def resolve_source_spatial_value(self, value: Any) -> Any:
        """Project a nominal value into the declared reference payload domain."""
        if self.reference_payload is None:
            return value
        metadata = ImagePayload.of(self.reference_payload).metadata
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
    def composition_metadata_mode(self) -> type[RuntimePlaneAxis]: ...

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
    def from_loaded_images(
        payloads: Sequence[RuntimeArrayData],
        *,
        producer_records: Sequence[ProducedOutputSemantics] | None,
        execution_plan: CompiledStepPlan,
        source_projection: VirtualWorkspaceSourceProjection | None,
        workspace_source_lookups: Sequence[VirtualWorkspacePathLookup],
    ) -> RuntimeArrayData:
        """Compose a selected admissible input cohort in its declared image domain."""
        if len(payloads) == 1 and payloads[0].keeps_whole_as_single_member(
            declared_plane_axis=(
                producer_records[0].main_flow_plane_axis
                if producer_records and len(producer_records) == 1
                else NoPlaneAxis
            ),
        ):
            main_data_stack = payloads[0].copied(
                memory_type=execution_plan.input_memory_type,
                device_id=execution_plan.device_id_for(execution_plan.input_memory_type),
            )
        else:
            metadata_mode = RuntimeSlicePlaneAxis
            if producer_records:
                declared_axis = producer_records[0].main_flow_plane_axis
                # Scalar occurrences of one declared output reconstruct its
                # runtime axis; distinct output contexts introduce a binding axis.
                metadata_mode = (
                    SourceBindingPlaneAxis
                    if declared_axis.unstacked
                    and len(
                        {record.output_context for record in producer_records}
                    ) > 1
                    else declared_axis.axis_when_stacked()
                )
            if source_projection is not None and workspace_source_lookups:
                metadata_mode = source_projection.payload_composition_mode(
                    workspace_source_lookups
                )
            if metadata_mode.one_plane_per_runtime_slice:
                main_data_stack = stack_image_payloads(
                    payloads, metadata_mode=metadata_mode,
                    memory_type=execution_plan.input_memory_type,
                    device_id=execution_plan.device_id_for(execution_plan.input_memory_type),
                )
            elif metadata_mode.one_plane_per_source_binding:
                main_data_stack = ImagePayloadBundleContext.from_payloads(
                    tuple(payloads), metadata_mode=metadata_mode,
                ).compose()
        return main_data_stack

    @staticmethod
    def with_saved_output_context(
        stack_payload: RuntimeArrayData,
        payloads: Sequence[RuntimeArrayData],
        metadata: Sequence[ImagePayloadMetadata],
        *,
        single_output_plane_axis: type[RuntimePlaneAxis],
    ) -> RuntimeArrayData:
        """Attach saved member context without replacing the independent buffer."""
        data = stack_payload.data
        current_intensity = stack_payload.metadata
        if (
            len(payloads) == 1
            and single_output_plane_axis is metadata[0].plane_axis
            and np.shape(data) == np.shape(payloads[0].data)
        ):
            member = metadata[0].with_current_intensity_from(current_intensity).payload_with(
                data, stack_payload.mask,
            )
            if member.keeps_whole_as_single_member(
                declared_plane_axis=single_output_plane_axis,
            ):
                return member
            # Cache the cohort the next step composes from this one saved member.
            return stack_image_payloads(
                (member,), metadata_mode=RuntimeSlicePlaneAxis,
            )
        if np.shape(data)[:1] != (len(payloads),):
            raise ValueError(
                "Output stack must match its declared output slice count: "
                f"stack shape {np.shape(data)!r}, slice count {len(payloads)}."
            )
        mode = stack_payload.metadata.plane_axis.axis_when_stacked()
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
            self.composition_payload_metadata(payload.metadata)
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
        """Resolve where a composition is placed: explicitly, else beside its first payload."""
        if memory_type is not None:
            return memory_type, device_id
        memory_type = detect_memory_type(payloads[0])
        return memory_type, MemoryType(memory_type).device_id_of(payloads[0])

    def compose(
        self, *, memory_type: str | None = None, device_id: int | None = None,
    ) -> Any:
        # Resolve the destination from the input payloads before reconciling intensity.
        memory_type, device_id = self.composition_memory_domain(
            tuple(payload.data for payload in self.composition_payloads),
            memory_type=memory_type, device_id=device_id,
        )
        payloads = ImagePayloadMetadata.intensity_coherent_payloads(self.composition_payloads)
        composed = self.compose_unmasked(
            tuple(payload.data for payload in payloads),
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

    payloads: Sequence[ImagePayload]
    metadata_mode: type[RuntimePlaneAxis]

    def __post_init__(self) -> None:
        # Stack members arrive as payloads or as bare producer arrays.
        self.payloads = tuple(ImagePayload.of(payload) for payload in self.payloads)
        if not self.payloads:
            raise ValueError("Cannot stack an empty image payload sequence.")

    @property
    def composition_payloads(self) -> tuple[Any, ...]:
        return tuple(self.payloads)

    @property
    def composition_metadata_mode(self) -> type[RuntimePlaneAxis]:
        return self.metadata_mode


def stack_image_payloads(
    image_payloads: Sequence[Any],
    *,
    metadata_mode: type[RuntimePlaneAxis],
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
    masks = tuple(payload.mask for payload in image_payloads)
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
            payload.metadata
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
    mask_domain = payload.metadata.mask_domain(payload_data)
    if mask is not None:
        if not mask_domain.accepts(tuple(np.shape(mask))):
            raise ValueError(
                "Image payload mask must match the selected output slice "
                f"domain; got mask {tuple(np.shape(mask))!r} for slice "
                f"{tuple(np.shape(payload_data))!r}."
            )
        return project_image_mask_to_data_domain(
            mask, payload_data, metadata=payload.metadata,
        )
    return MemoryType(detect_memory_type(payload_data)).ones_like(
        payload_data, shape=mask_domain.default_mask_shape(), dtype=bool,
    )


@dataclass(frozen=True, slots=True)
class ImagePayloadComposition:
    """Resolved image payload plus its execution mode."""

    payload: Any
    execution_mode: type[ImagePayloadExecutionMode]

    @property
    def plane_axis(self) -> type[RuntimePlaneAxis]:
        """Return the invocation axis, distinct from a bundle's inner source axis."""
        return self.payload.invocation_plane_axis

    def preserved_plane_projection(
        self,
        projector: RuntimePlaneAxisProjector,
        *,
        source_aliases: tuple[str, ...] = (),
    ) -> RuntimePlaneAxisValueProjection | None:
        """Return the complete projection owned by the composed payload axis."""

        axis = self.plane_axis
        if axis.unstacked:
            return None
        return preserved_image_plane_projection(
            self.payload,
            projector,
            source_aliases,
        )


@dataclass(slots=True)
class ImagePayloadBundleContext(ImagePayloadStackContext):
    """Compose same-slice image bundle data, masks, and metadata together."""

    metadata_mode: type[RuntimePlaneAxis] = (
        SourceBindingPlaneAxis
    )

    def __post_init__(self) -> None:
        super(ImagePayloadBundleContext, self).__post_init__()
        declared_axes = tuple(
            (
                index,
                metadata.plane_axis,
                metadata.source_image_names,
                tuple(np.shape(payload.data)),
            )
            for index, (payload, metadata) in enumerate(
                zip(self.payloads, self.source_metadata, strict=True)
            )
            if metadata.plane_axis.leads_data
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
        return tuple(payload.data for payload in self.payloads)

    @property
    def masks(self) -> tuple[RuntimeArrayData | None, ...]:
        return tuple(payload.mask for payload in self.payloads)

    @property
    def present_masks(self) -> tuple[RuntimeArrayData, ...]:
        return tuple(mask for mask in self.masks if mask is not None)

    @classmethod
    def from_payloads(
        cls,
        payloads: tuple[RuntimeArrayData, ...],
        *,
        metadata_mode: type[RuntimePlaneAxis] = (
            SourceBindingPlaneAxis
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
        shapes = tuple(array_geometry(mask).shape for mask in resolved_masks)
        if any(shape != shapes[0] for shape in shapes[1:]):
            resolved_masks = tuple(
                metadata.for_leading_source_plane(index)
                .mask_domain(composed[index])
                .broadcast_to_data(mask)
                for index, mask in enumerate(resolved_masks)
            )
        memory_type = detect_memory_type(composed)
        memory_type_owner = MemoryType(memory_type)
        stacked = stack_runtime_slices(
            resolved_masks,
            memory_type,
            memory_type_owner.device_id_of(composed),
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
        data = composed
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
            metadata.axis_index(ColourAxis, payload)
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
        metadata = payload.metadata
        return metadata.with_source_provenance(
            metadata.source_provenance.with_derived_source_image_names(
                (self.output_key,)
            )
        ).payload_with(
            payload.data,
            payload.mask,
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
            and self.artifact_kind == artifact_ref.artifact_type.value
        )

    def __post_init__(self) -> None:
        if not self.output_kind:
            raise ValueError("AlignedImageSliceContext.output_kind cannot be empty.")
        if not self.output_key:
            raise ValueError("AlignedImageSliceContext.output_key cannot be empty.")
        if not self.projection_key:
            raise ValueError("AlignedImageSliceContext.projection_key cannot be empty.")


@dataclass(slots=True)
class ImagePayloadSliceStack(ImagePayloadStackComposition, ImagePayload):
    """Shared slice storage, projection, and publication for image stacks."""

    slices: tuple[Any, ...]
    slice_contexts: tuple[AlignedImageSliceContext, ...] = ()
    @classmethod
    def from_output_slices(
        cls,
        slices: Sequence[Any],
        *,
        memory_type: str,
        plane_axis: type[RuntimePlaneAxis],
    ) -> "ProducedImageStack":
        """Wrap produced image slices as a stack without allocating its pixels."""
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
            tuple(array_geometry(payload) for payload in self.composition_payloads)
        ).shape

    @property
    def ndim(self) -> int:
        return len(self.shape)

    @property
    def dtype(self) -> Any:
        return self.compose().data.dtype

    def __array__(self, dtype: Any | None = None, copy: bool | None = None) -> Any:
        data = np.asarray(self.array_payload_data(), dtype=dtype)
        return data.copy() if copy else data

    def __getitem__(self, key: Any) -> Any:
        return self.array_payload_data()[key]

    def __len__(self) -> int:
        return len(self.slices)

    @property
    def data(self) -> Any:
        return self.compose().data

    @property
    def geometry(self) -> ArrayGeometry:
        return ArrayGeometry(self.shape)

    @property
    def mask(self) -> Any | None:
        return self.compose().mask

    def array_payload_data(self) -> Any:
        return self.compose().data

    def with_data(self, data: Any) -> Any:
        return self.metadata.payload_with(data, self.compose().mask)

    @property
    def composition_payloads(self) -> tuple[Any, ...]:
        return self.slices

    @property
    def projected_output_composition_mode(self) -> type[RuntimePlaneAxis]:
        """Declare the outer runtime axis retained by projected output members."""
        return self.composition_metadata_mode

    def runtime_slice_count(self) -> int | None:
        return len(self.slices)

    def alignment_slices(self) -> tuple[Any, ...]:
        return self.slices

    def map_slices(self, transform: Any) -> "ImagePayloadSliceStack":
        return self.with_slices(tuple(transform(image_slice) for image_slice in self.slices))

    def stored_slices(self) -> tuple[Any, ...]:
        return self.slices

    def output_slices(self) -> tuple[Any, ...]:
        return tuple(output for output, _context in self.projected_output_slices())

    def full_stack_value(self) -> Any:
        return self.compose()

    def value_for_slice(self, context: RuntimePlaneAxisValueProjection) -> Any:
        if context.axis is self.composition_metadata_mode:
            return self.aligned_slice(
                context.require_plane_index(),
                context.axis_size,
            )

        projected_slices = tuple(
            RuntimeSliceProjection.value_for_slice(image_slice, context)
            for image_slice in self.slices
        )
        if all(
            projected is image_slice
            for projected, image_slice in zip(projected_slices, self.slices, strict=True)
        ):
            return self
        return self.with_slices(projected_slices)

    def plane_axis_for_output_context(
        self, context: AlignedImageSliceContext,
    ) -> type[RuntimePlaneAxis]:
        """An explicitly aligned stack declares its outer runtime-slice domain."""
        return RuntimeSlicePlaneAxis

    @property
    def owns_output_surfaces(self) -> bool:
        """Each slice is a separately declared output surface."""
        return True

    def main_output_slices(
        self, unstack: Any,
    ) -> tuple[tuple[Any, AlignedImageSliceContext | None], ...]:
        del unstack
        return tuple(self.projected_output_slices())

    def output_stack_copy(
        self,
        projected_outputs: Sequence[tuple[Any, AlignedImageSliceContext | None]],
        *,
        memory_type: str,
        device_id: int | None,
    ) -> RuntimeArrayData | None:
        return self.copy_projected_output_stack(
            projected_outputs, memory_type=memory_type, device_id=device_id,
        )

    def __post_init__(self) -> None:
        # Producers hand over bare arrays and payloads alike; members are payloads.
        self.slices = tuple(ImagePayload.of(image_slice) for image_slice in self.slices)
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

    def copied(
        self, *, memory_type: str, device_id: int | None,
    ) -> "ImagePayloadSliceStack":
        """Retain aligned member domains while copying them into independent buffers."""
        return self.with_slices(
            tuple(
                payload.copied(memory_type=memory_type, device_id=device_id)
                for payload in self.slices
            )
        )

    def projected_output_slices(
        self,
    ) -> Iterator[tuple[Any, AlignedImageSliceContext | None]]:
        """Project each output once together with its declaration-owned context."""
        contexts = self.slice_contexts or (None,) * len(self.slices)
        for payload, context in zip(self.slices, contexts, strict=True):
            if payload.metadata.persists_whole_image():
                yield payload, context
            else:
                for output_slice in payload.alignment_slices():
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
        if metadata_mode.unstacked:
            return payloads[0].copied(memory_type=memory_type, device_id=device_id)
        data = tuple(payload.data for payload in payloads)
        declared_axes = {
            self.plane_axis_for_output_context(context)
            for _payload, context in projected_outputs
        }
        if len(declared_axes) != 1 or len({tuple(np.shape(item)) for item in data}) != 1:
            return None
        if metadata_mode.one_plane_per_source_binding:
            return ImagePayloadBundleContext.from_payloads(
                payloads, metadata_mode=metadata_mode,
            ).compose()
        return stack_image_payloads(
            payloads, metadata_mode=metadata_mode,
            memory_type=memory_type, device_id=device_id,
        )

    def output_values_for_artifact_specs(
        self,
        declared_specs: tuple[ArtifactSpec, ...],
    ) -> dict[ArtifactSpecRef, Any]:
        """Bind one complete declared main-flow roster to exact slice contexts."""

        if not self.slice_contexts:
            raise ValueError(
                "Multiple declared output specs require exact AlignedImageStack "
                "slice contexts; positional slice order is not artifact identity."
            )

        specs_by_context = {
            (spec.name, spec.artifact_type.value): spec for spec in declared_specs
        }
        if len(specs_by_context) != len(declared_specs):
            raise ValueError("Declared output specs contain duplicate named contexts.")
        resolved: dict[ArtifactSpecRef, Any] = {}
        for payload, context in zip(
            self.slices,
            self.slice_contexts,
            strict=True,
        ):
            if context.output_kind != AlignedImageSliceContext.MAIN_FLOW_OUTPUT_KIND:
                raise ValueError(
                    "Declared-output AlignedImageStack contains a non-main-flow slice "
                    f"context: {context!r}."
                )
            context_key = (context.output_key, context.artifact_kind)
            spec = specs_by_context.get(context_key)
            if spec is None:
                raise ValueError(
                    "Declared-output AlignedImageStack context is not declared by the "
                    f"callable ABI: {context!r}."
                )
            ref = spec.ref()
            if ref in resolved:
                raise ValueError(
                    "Declared-output AlignedImageStack contains duplicate context for "
                    f"{ref!r}."
                )
            resolved[ref] = payload
        missing = tuple(
            spec.ref() for spec in declared_specs if spec.ref() not in resolved
        )
        if missing:
            raise ValueError(
                "Declared-output AlignedImageStack does not carry every declared output: "
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
    def composition_metadata_mode(self) -> type[RuntimePlaneAxis]:
        return RuntimeSlicePlaneAxis

    @property
    def invocation_plane_axis(self) -> type[RuntimePlaneAxis]:
        """An aligned stack is invoked once per outer runtime slice."""
        return RuntimeSlicePlaneAxis

    def slice_source_provenances(self) -> tuple[SourceImageProvenance, ...]:
        return tuple(value.scalar_source_provenance() for value in self.slices)

    def scalar_source_provenance(self) -> SourceImageProvenance:
        """Collapse the inner image bundle's source topology into one slice's sources."""
        metadata = tuple(value.metadata for value in self.slices)
        provenances = tuple(
            (
                fields.source_provenance.for_source_plane(0)
                if fields.plane_axis.unstacked
                and fields.source_provenance.source_plane_count == 1
                else fields.source_provenance
            )
            for fields in metadata
        )
        provenance = SourceImageProvenance.bundle(
            provenances,
            scalar_sources=tuple(fields.source_provenance for fields in metadata),
            preserve_single_topology=(
                len(metadata) == 1
                and metadata[0].plane_axis.one_plane_per_source_binding
            ),
        )
        return (
            provenance.with_runtime_planes_as_contributors()
            .with_common_scalar_identity_from_planes()
        )

    @property
    def keeps_own_source_context(self) -> bool:
        """Each aligned member already carries its own source context."""
        return True

    def contextualize_image_output(
        self,
        output: ImagePayload,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> ImagePayload:
        """Aligned multi-source inputs are their outputs' source context already."""
        del plane_projection
        return output

    def aligned_value(self, resolver: AlignedImageStackKwargResolver) -> Any:
        """Bind this stack's slice for the resolver's outer aligned slice."""
        return resolver.resolve(
            self.aligned_slice(
                resolver.projection_axis.require_plane_index(),
                resolver.projection_axis.axis_size,
            )
        )

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
    """Borrowed produced image slices, composed once into one dense buffer.

    Produced pixels retain their literal values and heterogeneous numeric dtype
    promotion, unlike input bundles which reconcile intensity domains. Producer
    references may change pixels before realization, matching borrowed PURE3D
    publication. After composition the slices are views of that buffer.
    """

    memory_type: str
    plane_axis: type[RuntimePlaneAxis]
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
            tuple(payload.data for payload in self.slices)
        )
        masks = tuple(payload.mask for payload in self.slices)
        present_masks = tuple(mask for mask in masks if mask is not None)
        if present_masks and len(present_masks) != len(masks):
            raise ValueError("Cannot aggregate a mix of masked and unmasked image payloads.")
        self._metadata = (
            ImagePayloadMetadata.compose(
                self.slices,
                mode=self.plane_axis,
            )
            if source_metadata is None else source_metadata
        )
        if self._metadata.plane_axis is not self.plane_axis:
            raise ValueError("Produced image metadata must retain its declared plane axis.")
        shared_mask = (
            self._shared_image_mask(present_masks, data_geometry) if present_masks else None
        )
        mask_geometry = (
            array_geometry(shared_mask)
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
    def composition_metadata_mode(self) -> type[RuntimePlaneAxis]:
        return self.plane_axis

    @property
    def dtype(self) -> Any:
        return np.result_type(
            *(
                MemoryType(detect_memory_type(payload.data))
                .canonical_dtype_name(payload.data.dtype)
                for payload in self.slices
            )
        )

    def plane_axis_for_output_context(
        self, context: AlignedImageSliceContext,
    ) -> type[RuntimePlaneAxis]:
        return self.plane_axis

    def runtime_slice_count(self) -> int | None:
        if self.plane_axis.one_plane_per_runtime_slice:
            return len(self.slices)

        return RuntimeSliceProjection.slice_count_from_values(self.slices)

    def with_metadata(self, metadata: ImagePayloadMetadata) -> Any:
        if (
            self._composed_payload is not None
            or metadata.plane_axis is not self.plane_axis
            or metadata.axes != self._metadata.axes
            or metadata.source_spatial_domain != self._metadata.source_spatial_domain
        ):
            return super(ProducedImageStack, self).with_metadata(metadata)
        slices = tuple(
            metadata.for_leading_source_plane(index).payload_with(
                payload.data, payload.mask,
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
        ).accepts(array_geometry(first).shape):
            return first
        return None

    @property
    def mask(self) -> Any | None:
        if self._composed_payload is not None:
            return self._composed_payload.mask
        masks = tuple(payload.mask for payload in self.slices)
        if masks[0] is None:
            return None
        shared = self._shared_image_mask(masks, self.geometry)
        return shared if shared is not None else self.compose().mask

    def _materialized_image_mask(self) -> Any | None:
        masks = tuple(payload.mask for payload in self.slices)
        if masks[0] is None:
            return None
        shared = self._shared_image_mask(masks, self.geometry)
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
        data = self._composed_payload.data
        mask = self._composed_payload.mask
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

    def copied(
        self, *, memory_type: str, device_id: int | None,
    ) -> "ProducedImageStack":
        """Snapshot produced pixels directly into one dense buffer.

        Input isolation and dense realization share one allocation. Copying
        each borrowed member first would make placement stack those independent
        copies into a second buffer, including a second copy of every mask.
        """
        data = stack_runtime_slices(
            tuple(payload.data for payload in self.slices),
            memory_type, device_id,
        )
        masks = tuple(payload.mask for payload in self.slices)
        mask = None
        if masks[0] is not None:
            shared = self._shared_image_mask(masks, self.geometry)
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
                    tuple(payload.data for payload in self.slices),
                    self.memory_type, 0,
                )
                self._composed_payload = self._metadata.payload_with(
                    data, self._materialized_image_mask(),
                )
                self._retain_composed_slices()
        if memory_type is None:
            return self._composed_payload
        target = MemoryType(memory_type)
        data = self._composed_payload.data
        source = MemoryType(detect_memory_type(data))
        if source is target and source.device_id_of(data) == device_id:
            return self._composed_payload
        mask = self._composed_payload.mask
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
    def composition_metadata_mode(self) -> type[RuntimePlaneAxis]:
        return SourceBindingPlaneAxis

    @property
    def projected_output_composition_mode(self) -> type[RuntimePlaneAxis]:
        """Flatten declared inner runtime planes, retaining other named image domains."""
        if any(
            payload.metadata.plane_axis.one_plane_per_runtime_slice
            for payload in self.slices
        ):
            return RuntimeSlicePlaneAxis
        if len(self.slices) == 1:
            return NoPlaneAxis
        return self.composition_metadata_mode

    def plane_axis_for_output_context(
        self, context: AlignedImageSliceContext,
    ) -> type[RuntimePlaneAxis]:
        """Resolve a named output's own inner plane axis before slice projection."""
        payloads = tuple(
            payload for payload, declared_context in zip(self.slices, self.slice_contexts, strict=True)
            if declared_context == context
        )
        if len(payloads) != 1:
            raise ValueError(
                "Named image output context requires exactly one payload: "
                f"{context!r}; found {len(payloads)}."
            )
        return payloads[0].metadata.plane_axis

    def composition_payload_metadata(
        self, metadata: ImagePayloadMetadata
    ) -> ImagePayloadMetadata:
        """Named output surfaces remain source-binding planes, not runtime slices."""
        return metadata

    def inner_runtime_slice_count(self) -> int | None:
        """Return the runtime-slice count the named outputs themselves declare."""

        return RuntimeSliceProjection.slice_count_from_values(self.slices)

    def runtime_slice_count(self) -> int | None:
        inner_slice_count = self.inner_runtime_slice_count()
        return len(self.slices) if inner_slice_count is None else inner_slice_count

    def value_for_slice(self, context: RuntimePlaneAxisValueProjection) -> Any:
        """Project each named output through its shared declared runtime axis."""
        if (
            context.axis.one_plane_per_runtime_slice
            and self.inner_runtime_slice_count() is None
        ):
            return self.aligned_slice(context.require_plane_index(), context.axis_size)

        projected_outputs = tuple(
            RuntimeSliceProjection.value_for_slice(output, context)
            for output in self.slices
        )
        if all(
            projected is output
            for projected, output in zip(projected_outputs, self.slices, strict=True)
        ):
            return self
        return self.with_slices(projected_outputs)

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
    """Pack one or more image outputs into the callable's single return value."""

    packed = tuple(ImagePayload.of(output) for output in outputs)
    if not packed:
        raise ValueError("Image output packing requires at least one output.")
    contexts = tuple(slice_contexts)
    if contexts and len(contexts) != len(packed):
        raise ValueError(
            "Image output contexts must match output count; "
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
    metadata_mode: type[RuntimePlaneAxis] = (
        SourceBindingPlaneAxis
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
            execution_mode=AlignedStackExecution,
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
                        AlignedStackExecution
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
            execution_mode=AlignedStackExecution,
        )
    if len(image_payloads) == 1 and retain_single_input:
        return ImagePayloadComposition(
            payload=image_payloads[0],
            execution_mode=NaturalExecution,
        )

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
                                        axis=RuntimeSlicePlaneAxis,
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
            execution_mode=AlignedStackExecution,
        )
    return ImagePayloadComposition(
        payload=ImagePayloadBundleContext.from_payloads(
            image_payloads,
            metadata_mode=metadata_mode,
        ).compose(),
        execution_mode=FullStackExecution,
    )


def aligned_image_stack_kwargs(
    kwargs: Mapping[str, Any],
    slice_index: int,
    slice_count: int,
    reference_payload: Any | None = None,
) -> dict[str, Any]:
    """Slice runtime-array kwargs alongside an aligned image stack."""
    resolver = AlignedImageStackKwargResolver(
        projection_axis=RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=RuntimeSlicePlaneAxis,
            plane_index=slice_index,
            axis_size=slice_count,
        ),
        reference_payload=reference_payload,
    )
    return {name: resolver.resolve(value) for name, value in kwargs.items()}
