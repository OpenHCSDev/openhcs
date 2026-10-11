"""How a runtime executor interprets a resolved image payload.

A lightweight family: declaration-only consumers (callable contracts,
function references, agent DTOs) import it without the runtime payload
modules, which each mode imports when it executes.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Any, ClassVar

from metaclass_registry import AutoRegisterMeta

if TYPE_CHECKING:
    from openhcs.core.processing_contracts import ContractCall, ProcessingContract
    from openhcs.core.runtime_batch_contracts import RuntimeBatchInvocationRequest
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection


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
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

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

        from openhcs.core.aligned_image_payload import (
            AlignedImageStack,
            aligned_image_stack_kwargs,
        )
        from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        if not isinstance(request.image, AlignedImageStack):
            raise TypeError(
                "Aligned runtime batch execution requires AlignedImageStack, got "
                f"{type(request.image).__name__}."
            )
        projection = request.plane_projection
        if projection is None or projection.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            raise ValueError(
                "Aligned runtime batch execution requires a compiled runtime-slice "
                "projection."
            )
        if projection.plane_index is not None:
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
        from openhcs.core.aligned_image_payload import (
            AlignedImageStack,
            aligned_image_stack_kwargs,
        )
        from openhcs.core.memory import detect_memory_type
        from openhcs.core.processing_contracts import (
            Pure2DAuxiliaryOutputAggregator,
            Pure2DSliceResultBatch,
        )
        from openhcs.core.runtime_batch_contracts import (
            Pure2DSliceBatchExecutor,
            RuntimePure2DSliceBatchRequest,
        )
        from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
        from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
        from openhcs.core.runtime_slice_projection import (
            RuntimeSliceProjection,
            RuntimeSliceProjectionDeclarationError,
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
        if projection.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            raise RuntimeSliceProjectionDeclarationError(
                f"{owner} aligned image execution requires "
                f"RuntimePlaneAxis.RUNTIME_SLICE, got {projection.axis!r}."
            )
        if projection.plane_index is not None:
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
            if any(
                plane_axis is not RuntimePlaneAxis.SOURCE_BINDING
                for plane_axis in slice_plane_axes
            ):
                raise ValueError(
                    f"{owner} with whole-stack contract {contract.key!r} requires "
                    "every aligned image slice to declare "
                    f"RuntimePlaneAxis.SOURCE_BINDING; got {slice_plane_axes!r}."
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
                    plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
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
                    plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
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
                    plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
                )
                for values in result_batch.auxiliary_groups
            ),
        )
