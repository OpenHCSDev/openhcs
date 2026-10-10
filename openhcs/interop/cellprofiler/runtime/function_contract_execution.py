"""CellProfiler runtime callable contract execution."""

from __future__ import annotations

import inspect
import time
from collections.abc import Callable, Mapping

from openhcs.core.callable_contract import CallableContract
from openhcs.core.image_payload_execution_mode import ImagePayloadExecutionMode
from openhcs.core.measurement_dialect import executing_measurement_dialect
from openhcs.core.memory import detect_memory_type, stack_slices
from openhcs.core.processing_contracts import (
    ContractCall,
    PlaneSplit,
    ProcessingContract,
    Pure2DAuxiliaryOutputAggregator,
    Pure2DInputSlicer,
    Pure2DSliceResultBatch,
    RuntimeCallablePolicy,
    SignatureFilteredKwargs,
)
from openhcs.core.runtime_array_values import array_geometry
from openhcs.core.runtime_batch_contracts import (
    RuntimeBatchInvocationRequest,
    SliceIndexRuntimeParameter,
)
from openhcs.core.runtime_image_values import ImagePayload, owned_runtime_value
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import (
    RuntimeSliceProjection,
    RuntimeSliceProjectionDeclarationError,
)
from openhcs.core.steps.function_runtime import (
    RuntimeCallableArgument,
    RuntimeCallableKwargs,
    RuntimeFunctionOutput,
)
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_DIALECT,
)
from openhcs.interop.cellprofiler.runtime.runtime_profile import (
    CellProfilerRuntimeProfileLogger,
)

# The compiled raw target is resolved before contract execution.
_CELLPROFILER_RUNTIME_CALLABLE_POLICY = RuntimeCallablePolicy(
    kwarg_policy=SignatureFilteredKwargs,
)


class CellProfilerContractCall(ContractCall):
    """CellProfiler modules: compiled ABI, compiled plane projection, profiling."""

    def __init__(
        self,
        callable_contract: CallableContract,
        func: Callable[..., RuntimeFunctionOutput],
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> None:
        self.func = func
        self.plane_projection = plane_projection
        self._callable_contract = callable_contract

    @property
    def callable_contract(self) -> CallableContract:
        return self._callable_contract

    @property
    def parameters(self) -> Mapping[str, inspect.Parameter]:
        return self.callable_contract.canonical_signature.parameters

    @property
    def signature(self) -> inspect.Signature | None:
        return self.callable_contract.raw_runtime_signature

    @property
    def _owner(self) -> str:
        return (
            f"CellProfiler module {self.callable_contract.module_name!r} callable "
            f"{self.callable_contract.function_name!r}"
        )

    def invoke(self, value, kwargs, *, func=None):
        return _CELLPROFILER_RUNTIME_CALLABLE_POLICY.contract_invocation(
            self.callable_contract,
            self.func if func is None else func,
            value,
            kwargs,
        ).call()

    def invoke_unbound(self, value, kwargs):
        return self.invoke(value, kwargs)

    def full_stack_inputs(self, image, kwargs):
        projection_started_at = time.perf_counter()
        projected_image = RuntimeSliceProjection.full_stack_value(image)
        projected_kwargs = RuntimeSliceProjection.full_stack_kwargs(kwargs)
        label_value = projected_kwargs.get("labels")
        CellProfilerRuntimeProfileLogger.log_module_profile(
            "cp_full_stack_project_domains",
            time.perf_counter() - projection_started_at,
            function=self.callable_contract.function_name,
            image_shape=array_geometry(projected_image).shape,
            labels_shape=(
                array_geometry(label_value).shape if label_value is not None else None
            ),
        )
        return projected_image, projected_kwargs

    def validate_full_stack_kwargs(self, contract, kwargs):
        if not contract.whole_stack_only:
            return
        aligned_names = tuple(
            name
            for name, value in kwargs.items()
            if isinstance(value, RuntimeSliceAlignedValues)
        )
        if aligned_names:
            raise ValueError(
                f"{self._owner} has whole-stack contract {contract.key!r} but "
                f"received runtime-slice-aligned kwargs {list(aligned_names)}. "
                "Whole-stack callables consume whole-stack values; bind "
                "object-label special inputs as dense stack arrays or use a "
                "plane-local processing contract."
            )

    def stack_reduction_output(self, result):
        result_2d = ImagePayload.of(result)
        stacked = stack_slices(
            [result_2d.data], detect_memory_type(result_2d.data), 0,
        )
        return result_2d.metadata.payload_with(stacked, mask=result_2d.mask)

    def plane_split(self, image, kwargs):
        memory_type = owned_runtime_value(image).memory_type
        if memory_type != "numpy":
            return None
        projection = self.plane_projection
        if projection is None:
            declared_kwarg_slice_count = RuntimeSliceProjection.slice_count_from_values(
                kwargs.values()
            )
            if declared_kwarg_slice_count is not None:
                declared_kwarg_names = tuple(
                    name
                    for name, value in kwargs.items()
                    if RuntimeSliceProjection.slice_count_from_values((value,))
                    is not None
                )
                raise RuntimeSliceProjectionDeclarationError(
                    f"{self._owner} with a per-plane contract has kwargs declaring "
                    "a runtime-slice axis of size "
                    f"{declared_kwarg_slice_count} through {declared_kwarg_names!r}, "
                    "but the image invocation has no declared plane projection. "
                    "Kwargs cannot create image-axis execution semantics."
                )
            return None
        declared_plane_axis = image.metadata.plane_axis
        if declared_plane_axis is not projection.axis:
            raise RuntimeSliceProjectionDeclarationError(
                f"{self._owner} with a per-plane contract has an image payload "
                "plane axis that conflicts with the compiled projection: "
                f"{declared_plane_axis!r} != {projection.axis.value!r}."
            )
        prepare_started_at = time.perf_counter()
        slices = tuple(
            Pure2DInputSlicer.strategy_for_value(image).slice_value(image, memory_type)
        )
        if len(slices) != projection.axis_size:
            raise RuntimeSliceProjectionDeclarationError(
                f"{self._owner} with a per-plane contract has an image payload "
                "slice count that conflicts with the compiled projection: "
                f"{len(slices)} != {projection.axis_size}."
            )
        CellProfilerRuntimeProfileLogger.log_module_profile(
            "cp_pure_2d_prepare_slices",
            time.perf_counter() - prepare_started_at,
            function=self.callable_contract.function_name,
            slices=len(slices),
        )
        return PlaneSplit(
            slices=slices,
            plane_axis=projection.axis,
            memory_type=memory_type,
            kwargs=dict(kwargs),
        )

    def slice_kwargs(self, split, kwargs, slice_index, slice_count):
        if self.plane_projection.axis_size != slice_count:
            raise ValueError(
                f"{self._owner} per-plane slice batch cardinality conflicts with "
                "its declared plane axis: "
                f"{slice_count} != {self.plane_projection.axis_size}."
            )
        sliced_kwargs = RuntimeSliceProjection.kwargs_for_slice(
            kwargs,
            self.plane_projection.selected_plane(slice_index),
        )
        if (
            SliceIndexRuntimeParameter
            in self.callable_contract.runtime_bound_parameter_types
        ):
            sliced_kwargs = dict(sliced_kwargs)
            sliced_kwargs[SliceIndexRuntimeParameter.require_parameter_name()] = (
                slice_index
            )
        return sliced_kwargs

    def aggregate_slices(self, split: PlaneSplit, batch: Pure2DSliceResultBatch):
        canonical_specs = self.callable_contract.canonical_return_output_specs.specs
        trailing_specs = self.callable_contract.trailing_return_output_specs.specs
        if len(batch.auxiliary_groups) != len(trailing_specs):
            raise ValueError(
                f"{self.callable_contract.function_name} returned "
                f"{len(batch.auxiliary_groups)} trailing output position(s); "
                f"the compiled CallableContract declares {len(trailing_specs)}."
            )
        stacked_main_output = (
            Pure2DAuxiliaryOutputAggregator.aggregate(
                batch.main_outputs,
                split.memory_type,
                plane_axis=split.plane_axis,
            )
            if canonical_specs
            else RuntimeSliceAlignedValues(slices=tuple(batch.main_outputs))
        )
        if not batch.auxiliary_groups:
            return stacked_main_output
        return (
            stacked_main_output,
            *(
                Pure2DAuxiliaryOutputAggregator.aggregate(
                    values,
                    split.memory_type,
                    plane_axis=split.plane_axis,
                )
                for values in batch.auxiliary_groups
            ),
        )


class CellProfilerFunctionContractExecutor:
    """Run a resolved CellProfiler callable under its contract and mode."""

    def execute(
        self,
        callable_contract: CallableContract,
        func: Callable[..., RuntimeFunctionOutput],
        image: RuntimeCallableArgument,
        kwargs: RuntimeCallableKwargs,
        *,
        execution_mode: type[ImagePayloadExecutionMode],
        plane_projection: RuntimePlaneAxisValueProjection | None = None,
    ) -> RuntimeCallableArgument:
        if not isinstance(callable_contract, CallableContract):
            raise TypeError(
                "CellProfilerFunctionContractExecutor.execute requires a compiled "
                f"CallableContract, got {type(callable_contract).__name__}."
            )
        if not callable(func):
            raise TypeError(
                "CellProfilerFunctionContractExecutor.execute requires a resolved "
                f"raw callable, got {type(func).__name__}."
            )
        compiled_raw_func = callable_contract.resolve_canonical_raw_callable()
        if func is not compiled_raw_func:
            raise ValueError(
                "CellProfilerFunctionContractExecutor.execute received a raw "
                f"callable that does not match compiled contract "
                f"{callable_contract.module_name!r}/"
                f"{callable_contract.function_name!r}."
            )
        if not (
            isinstance(execution_mode, type)
            and issubclass(execution_mode, ImagePayloadExecutionMode)
        ):
            raise TypeError(
                "CellProfilerFunctionContractExecutor.execute requires an "
                "ImagePayloadExecutionMode family member, got "
                f"{execution_mode!r}."
            )
        processing_contract: type[ProcessingContract] = (
            callable_contract.require_processing_contract()
        )
        call = CellProfilerContractCall(
            callable_contract,
            callable_contract.resolve_raw_runtime_callable(),
            plane_projection,
        )
        execute_started_at = time.perf_counter()
        with executing_measurement_dialect(
            CELLPROFILER_MEASUREMENT_DIALECT
        ):
            result = execution_mode.execute(
                processing_contract, call, image, dict(kwargs)
            )
        CellProfilerRuntimeProfileLogger.log_module_profile(
            "cp_executor_execute",
            time.perf_counter() - execute_started_at,
            function=callable_contract.function_name,
            mode=execution_mode.key,
        )
        return callable_contract.contextualize_returned_canonical_output(
            result,
            plane_projection=call.plane_projection,
        )


def _execute_runtime_batch_invocation(
    callable_contract: CallableContract,
    func: Callable[..., RuntimeFunctionOutput],
    request: RuntimeBatchInvocationRequest,
) -> RuntimeCallableArgument:
    """Execute one invocation from a core runtime batch request."""
    return _CELLPROFILER_FUNCTION_CONTRACT_EXECUTOR.execute(
        callable_contract,
        func,
        request.image,
        request.kwargs,
        execution_mode=request.execution_mode,
        plane_projection=request.plane_projection,
    )


_CELLPROFILER_FUNCTION_CONTRACT_EXECUTOR = CellProfilerFunctionContractExecutor()
