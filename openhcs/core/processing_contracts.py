"""Processing contracts: how one callable executes over an image stack.

A contract is a nominal class in the ``ProcessingContract`` family; its
``execute`` owns the algorithm, written over a ``ContractCall`` that supplies
the invocation environment (library registry wrappers, CellProfiler modules).
The plane slicers, slice-output aggregators and the callable invocation
policy used by those algorithms live here too.
"""

from __future__ import annotations

import inspect
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Mapping, MutableMapping
from dataclasses import dataclass, field
from functools import lru_cache
from typing import TYPE_CHECKING, Any, ClassVar

import numpy as np
from arraybridge import SliceBySliceRuntimeParameter
from metaclass_registry import AutoRegisterMeta
from python_introspect import RuntimeParameterDeclarationABC

from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    ImagePayloadSliceStack,
    ProducedImageStack,
)
from openhcs.core.measurement_row_materialization import (
    ConcatenatedColumnarRows,
    MeasurementRowsAxisProjection,
)
from openhcs.core.memory import stack_runtime_slices, unstack_runtime_slices
from openhcs.core.runtime_array_values import RuntimeArrayPayload
from openhcs.core.runtime_batch_contracts import (
    Pure2DSliceBatchExecutor,
    RuntimeBatchInvocationRequest,
    RuntimePure2DSliceBatchRequest,
)
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload,
    ImagePayload,
    MaskedImagePayload,
    PlainImagePayload,
    image_metadata_of,
    owned_runtime_value,
)
from openhcs.core.runtime_object_label_aggregation import (
    ObjectLabelPure2DSliceAggregator,
)
from openhcs.core.runtime_object_labels import ObjectLabelPayload, ObjectLabelSet
from openhcs.core.runtime_output_matching import (
    RuntimeOutputBundle,
    runtime_output_tuple,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_relationships import DirectedObjectRelationshipPayload
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.runtime_spatial_grid import SpatialGrid
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.variable_component_stack_requirement import (
    AlwaysRequiresVariableComponentStack,
    SemanticControlVariableComponentStackRequirement,
    VariableComponentStackRequirement,
)

if TYPE_CHECKING:
    from openhcs.core.callable_contract import CallableContract

PURE2D_VALUE_TYPE_REGISTRY_KEY = "value_type"


# ---------------------------------------------------------------------------
# Callable invocation policy
# ---------------------------------------------------------------------------


class RuntimeCallableView(ABC):
    """Which callable object a runtime invocation calls."""

    @classmethod
    @abstractmethod
    def resolve(cls, func: Callable[..., Any]) -> Callable[..., Any]:
        """Return the callable object selected by this view."""


class DecoratedCallableView(RuntimeCallableView):
    """Call the decorated callable as given."""

    @classmethod
    def resolve(cls, func: Callable[..., Any]) -> Callable[..., Any]:
        return func


class RawCallableView(RuntimeCallableView):
    """Call the raw runtime callable behind the decorated one."""

    @classmethod
    def resolve(cls, func: Callable[..., Any]) -> Callable[..., Any]:
        from openhcs.core.callable_contract import CallableContract

        return CallableContract.from_callable(func).resolve_raw_runtime_callable()


class RuntimeInvocationKwargPolicy(ABC):
    """Which keyword arguments a runtime invocation passes."""

    @classmethod
    @abstractmethod
    def accepted_kwargs(
        cls,
        func: Callable[..., Any],
        kwargs: Mapping[str, Any],
        *,
        signature: inspect.Signature | None = None,
    ) -> dict[str, Any]:
        """Return kwargs accepted by ``func`` under this policy."""


class PassThroughKwargs(RuntimeInvocationKwargPolicy):
    """Pass every keyword argument."""

    @classmethod
    def accepted_kwargs(
        cls,
        func: Callable[..., Any],
        kwargs: Mapping[str, Any],
        *,
        signature: inspect.Signature | None = None,
    ) -> dict[str, Any]:
        del func, signature
        return dict(kwargs)


class SignatureFilteredKwargs(RuntimeInvocationKwargPolicy):
    """Pass only the keyword arguments the callable's signature declares."""

    @classmethod
    def accepted_kwargs(
        cls,
        func: Callable[..., Any],
        kwargs: Mapping[str, Any],
        *,
        signature: inspect.Signature | None = None,
    ) -> dict[str, Any]:
        from openhcs.core.callable_contract import CallableMetadata

        parameters = (
            CallableMetadata.callable_signature(func) if signature is None else signature
        ).parameters
        if any(
            parameter.kind is inspect.Parameter.VAR_KEYWORD
            for parameter in parameters.values()
        ):
            return dict(kwargs)
        return {name: value for name, value in kwargs.items() if name in parameters}


@dataclass(frozen=True, slots=True)
class RuntimeCallableInvocation:
    """Typed runtime invocation boundary for processing-contract callables."""

    func: Callable[..., Any]
    args: tuple[Any, ...] = ()
    kwargs: Mapping[str, Any] = field(default_factory=dict)
    callable_view: type[RuntimeCallableView] = DecoratedCallableView
    kwarg_policy: type[RuntimeInvocationKwargPolicy] = PassThroughKwargs
    signature: inspect.Signature | None = None

    def call(self) -> Any:
        target = self.callable_view.resolve(self.func)
        return target(
            *self.args,
            **self.kwarg_policy.accepted_kwargs(
                target, self.kwargs, signature=self.signature
            ),
        )


@dataclass(frozen=True, slots=True)
class RuntimeCallablePolicy:
    """Reusable runtime callable invocation semantics."""

    callable_view: type[RuntimeCallableView] = DecoratedCallableView
    kwarg_policy: type[RuntimeInvocationKwargPolicy] = PassThroughKwargs

    def contract_invocation(
        self,
        contract: "CallableContract",
        func: Callable[..., Any],
        image: Any,
        kwargs: Mapping[str, Any],
    ) -> RuntimeCallableInvocation:
        """Bind the prepared main-image carrier and actual raw execution ABI."""
        return self.invocation(
            func,
            (contract.raw_main_flow_call_argument(image),),
            kwargs,
            signature=contract.raw_runtime_signature,
        )

    def invocation(
        self,
        func: Callable[..., Any],
        args: tuple[Any, ...],
        kwargs: Mapping[str, Any],
        *,
        signature: inspect.Signature | None = None,
    ) -> RuntimeCallableInvocation:
        return RuntimeCallableInvocation(
            func=func,
            args=args,
            kwargs=kwargs,
            callable_view=self.callable_view,
            kwarg_policy=self.kwarg_policy,
            signature=signature,
        )


@dataclass(frozen=True, slots=True)
class Pure2DSliceResultBatch:
    """Typed decomposition of per-slice PURE_2D outputs."""

    main_outputs: list[Any]
    auxiliary_groups: tuple[list[Any], ...] = ()

    @classmethod
    def from_results(cls, results: Iterable[Any]) -> "Pure2DSliceResultBatch":
        collected = [runtime_output_tuple(result) for result in results]
        if not collected:
            raise ValueError("PURE_2D execution cannot aggregate zero slice results.")

        first_result = collected[0]
        if not isinstance(first_result, tuple):
            return cls(main_outputs=collected)

        tuple_length = len(first_result)
        if tuple_length == 0:
            raise ValueError("PURE_2D slice result tuples cannot be empty.")

        main_outputs: list[Any] = []
        auxiliary_groups = [list() for _ in range(tuple_length - 1)]
        for result in collected:
            if not isinstance(result, tuple):
                raise TypeError(
                    "PURE_2D execution cannot mix tuple and non-tuple slice results."
                )
            if len(result) != tuple_length:
                raise ValueError(
                    "PURE_2D execution requires all tuple slice results to have the "
                    "same arity."
                )
            main_outputs.append(result[0])
            for index, value in enumerate(result[1:]):
                auxiliary_groups[index].append(value)

        return cls(main_outputs=main_outputs, auxiliary_groups=tuple(auxiliary_groups))


def contextualize_main_image_output(source_image: Any, result: Any) -> Any:
    """Preserve source image context when plain array callables return plain arrays."""
    if isinstance(result, RuntimeOutputBundle):
        return result
    if isinstance(result, tuple):
        if not result:
            return result
        return (
            contextualize_main_image_output(source_image, result[0]),
            *result[1:],
        )
    if isinstance(result, RuntimeArrayPayload):
        return result
    if not isinstance(result, np.ndarray):
        return result
    source_image = owned_runtime_value(source_image)
    if not isinstance(source_image, ImagePayload) or (
        source_image.mask is None
        and not source_image.metadata.has_values
    ):
        return result
    return source_image.with_pixels(result)


class Pure2DRegisteredStrategyFamily(ABC):
    """Shared cached registry-family mechanics for PURE_2D strategy ABCs."""

    __registry__: ClassVar[Mapping[Any, type["Pure2DRegisteredStrategyFamily"]]]
    value_type: ClassVar[type[Any] | None] = None
    include_in_family: ClassVar[bool] = True

    @classmethod
    @abstractmethod
    def family_root(cls) -> type["Pure2DRegisteredStrategyFamily"]:
        """Return the concrete AutoRegisterMeta root for this strategy family."""

    @classmethod
    @lru_cache(maxsize=None)
    def registered_families(cls) -> tuple[type["Pure2DRegisteredStrategyFamily"], ...]:
        root_type = cls.family_root()
        family_types: list[type[Pure2DRegisteredStrategyFamily]] = []
        for strategy_type in root_type.__registry__.values():
            for candidate_type in strategy_type.mro():
                if (
                    candidate_type is root_type
                    or not isinstance(candidate_type, type)
                    or not issubclass(candidate_type, root_type)
                    or not candidate_type.include_in_family
                    or candidate_type in family_types
                ):
                    continue
                family_types.append(candidate_type)
        return tuple(family_types)

    @classmethod
    @lru_cache(maxsize=None)
    def registered_strategies(cls) -> tuple["Pure2DRegisteredStrategyFamily", ...]:
        """Return cached nominal strategy instances."""
        return tuple(strategy_type() for strategy_type in cls.registered_families())

    @classmethod
    def nearest_registered_strategy(
        cls,
        strategy_type: type[Any],
        *,
        supports: Callable[[Any], bool],
        distance: Callable[[Any], int],
    ) -> Any | None:
        """Return the nearest registered strategy satisfying ``supports``."""
        candidates = [
            strategy
            for strategy in cls.registered_strategies()
            if isinstance(strategy, strategy_type) and supports(strategy)
        ]
        if not candidates:
            return None
        return min(candidates, key=distance)

    @classmethod
    @lru_cache(maxsize=None)
    def accepted_value_types(cls) -> tuple[type[Any], ...]:
        """Return nominal value types owned by this registered family."""
        root_type = cls.family_root()
        return tuple(
            strategy_type.value_type
            for strategy_type in root_type.__registry__.values()
            if (strategy_type.value_type is not None and issubclass(strategy_type, cls))
        )

    def type_distance(self, value: Any) -> int:
        """Return nearest nominal MRO distance for this strategy family."""
        declared_types = self.accepted_value_types()
        if not declared_types:
            return len(object.__mro__)
        return min(
            type(value).mro().index(declared_type)
            for declared_type in declared_types
            if isinstance(value, declared_type)
        )


class Pure2DInputSlicer(Pure2DRegisteredStrategyFamily, metaclass=AutoRegisterMeta):
    """Unstack a PURE_2D main-flow input into nominal per-slice values."""

    __registry_key__ = PURE2D_VALUE_TYPE_REGISTRY_KEY
    __registry__: ClassVar[dict[Any, type["Pure2DInputSlicer"]]] = {}

    @classmethod
    def family_root(cls) -> type["Pure2DInputSlicer"]:
        return Pure2DInputSlicer

    @classmethod
    def strategy_for_value(cls, value: Any) -> "Pure2DInputSlicer":
        """Select the nearest registered slicer for a PURE_2D input value."""
        slicer = cls.nearest_registered_strategy(
            Pure2DInputSlicer,
            supports=lambda strategy: strategy.supports(value),
            distance=lambda strategy: strategy.type_distance(value),
        )
        if slicer is None:
            raise TypeError(
                "PURE_2D execution requires a registered input slicer for "
                f"{type(value).__name__}."
            )
        return slicer

    def supports(self, value: Any) -> bool:
        accepted_types = self.accepted_value_types()
        return bool(accepted_types) and isinstance(value, accepted_types)

    @abstractmethod
    def slice_value(self, value: Any, memory_type: str) -> tuple[Any, ...]:
        """Return nominal per-slice values for one PURE_2D input."""

    @abstractmethod
    def is_single_plane_value(self, value: Any) -> bool:
        """Return whether this value should bypass slice/restack execution."""


class NumPyPure2DInputSlicer(Pure2DInputSlicer):
    """Treat an unannotated ndarray as one image plane."""

    value_type = np.ndarray

    def is_single_plane_value(self, value: np.ndarray) -> bool:
        del value
        return True

    def slice_value(self, value: np.ndarray, memory_type: str) -> tuple[Any, ...]:
        del memory_type
        return (value,)


class ImagePayloadPure2DInputSlicer(Pure2DInputSlicer):
    """Slice image payloads while preserving per-slice image context."""

    value_type = None

    def is_single_plane_value(self, value: Any) -> bool:
        return value.metadata.plane_axis is None

    def slice_value(self, value: Any, memory_type: str) -> tuple[Any, ...]:
        data = value.data
        if self.is_single_plane_value(value):
            return (value,)
        metadata = value.metadata
        slices = unstack_runtime_slices(
            data,
            memory_type,
            0,
            expected_count=metadata.source_provenance.source_plane_count or None,
        )
        return tuple(
            value.slice_payload(slice_data, slice_index)
            for slice_index, slice_data in enumerate(slices)
        )


class ProducedImageStackPure2DInputSlicer(ImagePayloadPure2DInputSlicer):
    """Project literal image leaves through their existing declared axis owner."""

    value_type = ProducedImageStack

    def slice_value(self, value: ProducedImageStack, memory_type: str) -> tuple[Any, ...]:
        del memory_type
        return tuple(
            RuntimeSliceProjection.value_for_slice(
                value,
                RuntimePlaneAxisValueProjection.from_selected_plane(
                    axis=value.plane_axis,
                    source_aliases=value.metadata.source_image_names,
                    plane_index=index,
                    axis_size=len(value.slices),
                ),
            )
            for index in range(len(value.slices))
        )


class MaskedImagePayloadPure2DInputSlicer(ImagePayloadPure2DInputSlicer):
    """Register masked image payloads for PURE_2D input slicing."""

    value_type = MaskedImagePayload


class PlainImagePayloadPure2DInputSlicer(ImagePayloadPure2DInputSlicer):
    """Slice bare pixels wrapped at the boundary like any image payload."""

    value_type = PlainImagePayload


class ImageMetadataPayloadPure2DInputSlicer(ImagePayloadPure2DInputSlicer):
    """Register image metadata payloads for PURE_2D input slicing."""

    value_type = ImageMetadataPayload


class Pure2DAuxiliaryOutputAggregator(
    Pure2DRegisteredStrategyFamily,
    metaclass=AutoRegisterMeta,
):
    """Aggregate one auxiliary PURE_2D output position across slices."""

    __registry_key__ = PURE2D_VALUE_TYPE_REGISTRY_KEY
    __registry__: ClassVar[dict[Any, type["Pure2DAuxiliaryOutputAggregator"]]] = {}

    @classmethod
    def family_root(cls) -> type["Pure2DAuxiliaryOutputAggregator"]:
        return Pure2DAuxiliaryOutputAggregator

    @classmethod
    def aggregate(
        cls,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis = RuntimePlaneAxis.RUNTIME_SLICE,
    ) -> Any:
        if not values:
            raise ValueError("PURE_2D auxiliary aggregation requires output values.")
        aggregator = cls.nearest_registered_strategy(
            Pure2DAuxiliaryOutputAggregator,
            supports=lambda strategy: strategy.supports(values),
            distance=lambda strategy: strategy.type_distance(values),
        )
        if aggregator is not None:
            return aggregator.aggregate_values(
                values,
                memory_type,
                plane_axis=plane_axis,
            )
        if len(values) == 1:
            return values[0]
        raise TypeError(
            "PURE_2D auxiliary outputs spanning multiple slices require a "
            "registered nominal aggregator, got "
            f"{type(values[0]).__name__}."
        )

    def supports(self, values: list[Any]) -> bool:
        accepted_types = self.accepted_value_types()
        return bool(accepted_types) and all(
            isinstance(value, accepted_types) for value in values
        )

    def owns_mixed_values(self, values: list[Any]) -> bool:
        return False

    def type_distance(self, values: list[Any]) -> int:
        declared_types = self.accepted_value_types()
        if not declared_types:
            return len(object.__mro__)
        return max(
            min(
                type(value).mro().index(declared_type)
                for declared_type in declared_types
                if isinstance(value, declared_type)
            )
            for value in values
        )

    @abstractmethod
    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> Any:
        """Aggregate compatible per-slice auxiliary values."""


class DirectedRelationshipPure2DOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Aggregate directed relationships over one declared PURE_2D plane axis."""

    value_type = DirectedObjectRelationshipPayload

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> DirectedObjectRelationshipPayload:
        del memory_type, plane_axis
        return DirectedObjectRelationshipPayload(
            source_ids=tuple(
                source_id for value in values for source_id in value.source_ids
            ),
            target_ids=tuple(
                target_id for value in values for target_id in value.target_ids
            ),
            slice_indices=tuple(
                slice_index
                for slice_index, value in enumerate(values)
                for _target_id in value.target_ids
            ),
            slice_count=len(values),
        )


class SpatialGridPure2DOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Preserve one declared spatial grid for each PURE_2D runtime slice."""

    value_type = SpatialGrid

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> RuntimeSliceAlignedValues[SpatialGrid]:
        del memory_type, plane_axis
        return RuntimeSliceAlignedValues(tuple(values))


class AlignedImageStackPure2DOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Transpose aligned image surfaces into declared output-plane stacks."""

    value_type = AlignedImageStack

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> AlignedImageStack:
        aligned_values = tuple(values)
        first = aligned_values[0]
        output_count = len(first.slices)
        if any(len(value.slices) != output_count for value in aligned_values):
            raise ValueError(
                "Aligned main outputs must expose the same image surface count "
                "across every PURE_2D slice."
            )
        return first.with_slices(
            tuple(
                Pure2DAuxiliaryOutputAggregator.aggregate(
                    [value.slices[index] for value in aligned_values],
                    memory_type,
                    plane_axis=plane_axis,
                )
                for index in range(output_count)
            )
        )


class RuntimeArrayPure2DAuxiliaryOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Stack nominal runtime array payloads through their concrete array data."""

    value_type = None
    include_in_family = False

    def supports(self, values: list[Any]) -> bool:
        return super().supports(values) or self.owns_mixed_values(values)

    def owns_mixed_values(self, values: list[Any]) -> bool:
        accepted_types = self.accepted_value_types()
        return (
            bool(accepted_types)
            and any(isinstance(value, accepted_types) for value in values)
            and all(self._accepts_mixed_value(value) for value in values)
        )

    def type_distance(self, values: list[Any]) -> int:
        if super().supports(values):
            return super().type_distance(values)
        if self.owns_mixed_values(values):
            return 0
        return super().type_distance(values)

    def _accepts_mixed_value(self, value: Any) -> bool:
        return isinstance(value, np.ndarray)

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> Any:
        del values, memory_type, plane_axis
        raise NotImplementedError(
            "Concrete runtime-array aggregators must implement aggregate_values."
        )

    def stack_array_slices(self, values: list[Any], memory_type: str) -> Any:
        """Stack an explicitly collected dense runtime-slice sequence."""

        return stack_runtime_slices(values, memory_type, 0)


class ImagePayloadPure2DAuxiliaryOutputAggregator(
    RuntimeArrayPure2DAuxiliaryOutputAggregator
):
    """Stack image payload slices and reattach composed runtime image context."""

    value_type = ImagePayload
    include_in_family = True

    def _accepts_mixed_value(self, value: Any) -> bool:
        accepted_types = self.accepted_value_types()
        return (
            bool(accepted_types) and isinstance(value, accepted_types)
        ) or super()._accepts_mixed_value(value)

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> Any:
        return ImagePayloadSliceStack.from_output_slices(
            values, memory_type=memory_type, plane_axis=plane_axis,
        )


class MaskedImagePayloadPure2DAuxiliaryOutputAggregator(
    ImagePayloadPure2DAuxiliaryOutputAggregator
):
    """Register masked image payloads for PURE_2D auxiliary aggregation."""

    value_type = MaskedImagePayload


class ImageMetadataPayloadPure2DAuxiliaryOutputAggregator(
    ImagePayloadPure2DAuxiliaryOutputAggregator
):
    """Register image metadata payloads for PURE_2D auxiliary aggregation."""

    value_type = ImageMetadataPayload


class ObjectLabelPayloadPure2DAuxiliaryOutputAggregator(
    RuntimeArrayPure2DAuxiliaryOutputAggregator
):
    """Delegate object-label slice aggregation to the runtime-value authority."""

    value_type = ObjectLabelPayload
    include_in_family = True

    def _accepts_mixed_value(self, value: Any) -> bool:
        return isinstance(value, self.value_type)

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> Any:
        return ObjectLabelPure2DSliceAggregator.aggregate(
            values,
            memory_type,
            plane_axis=plane_axis,
        )


class ObjectLabelSetPure2DAuxiliaryOutputAggregator(
    ObjectLabelPayloadPure2DAuxiliaryOutputAggregator
):
    """Register native object-label values for PURE_2D auxiliary aggregation."""

    value_type = ObjectLabelSet


class NumPyPure2DAuxiliaryOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Stack ndarray outputs from an explicitly declared PURE_2D slice batch."""

    value_type = np.ndarray

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> Any:
        return ImagePayloadSliceStack.from_output_slices(
            values, memory_type=memory_type, plane_axis=plane_axis,
        )


class ColumnarRowsPure2DAuxiliaryOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Stamp nominal columnar measurement rows with their PURE_2D slice identity."""

    value_type = ColumnarRows

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> ColumnarRows:
        del memory_type, plane_axis
        if len(values) == 1:
            return self.slice_projected_rows(values[0], 0)
        return ConcatenatedColumnarRows(
            tuple(
                self.slice_projected_rows(value, slice_index)
                for slice_index, value in enumerate(values)
            )
        )

    @staticmethod
    def slice_projected_rows(rows: ColumnarRows, slice_index: int) -> ColumnarRows:
        if not isinstance(rows, ColumnarRows):
            raise TypeError(
                "ColumnarRowsPure2DAuxiliaryOutputAggregator requires ColumnarRows, "
                f"got {type(rows).__name__}."
            )
        projected_rows = MeasurementRowsAxisProjection.from_rows(
            rows
        ).project_runtime_slice_index(slice_index)
        if not isinstance(projected_rows, ColumnarRows):
            raise TypeError(
                "ColumnarRows axis projection must return ColumnarRows, got "
                f"{type(projected_rows).__name__}."
            )
        return projected_rows


class FlatSequencePure2DAuxiliaryOutputAggregator(Pure2DAuxiliaryOutputAggregator):
    """Concatenate explicitly sequence-valued tuple/list auxiliary outputs."""

    value_type = None

    def supports(self, values: list[Any]) -> bool:
        return super().supports(values) and not any(
            isinstance(item, (np.ndarray, ColumnarRows))
            for value in values
            for item in value
        )

    def aggregate_values(
        self,
        values: list[Any],
        memory_type: str,
        *,
        plane_axis: RuntimePlaneAxis,
    ) -> Any:
        del memory_type, plane_axis
        flattened: list[Any] = []
        for value in values:
            flattened.extend(value)
        return flattened


class ListPure2DAuxiliaryOutputAggregator(FlatSequencePure2DAuxiliaryOutputAggregator):
    """Register list auxiliary outputs for PURE_2D sequence aggregation."""

    value_type = list


class TuplePure2DAuxiliaryOutputAggregator(FlatSequencePure2DAuxiliaryOutputAggregator):
    """Register tuple auxiliary outputs for PURE_2D sequence aggregation."""

    value_type = tuple




# ---------------------------------------------------------------------------
# The contract family
# ---------------------------------------------------------------------------


@dataclass(slots=True)
class PlaneSplit:
    """A main-flow value split into the planes of its declared plane axis."""

    slices: tuple[Any, ...]
    plane_axis: RuntimePlaneAxis
    memory_type: str
    kwargs: dict[str, Any]
    source_aliases: tuple[str, ...] = ()


class ContractCall(ABC):
    """The environment one processing-contract invocation runs in.

    A contract's ``execute`` is written over these primitives; an environment
    (library registry wrappers, CellProfiler modules) decides how the callable
    is bound and how a value splits into planes, never which contract runs.
    """

    func: Callable[..., Any]
    plane_projection: RuntimePlaneAxisValueProjection | None = None

    @property
    @abstractmethod
    def callable_contract(self) -> "CallableContract":
        """The compiled callable contract of ``func``."""

    @property
    @abstractmethod
    def parameters(self) -> Mapping[str, inspect.Parameter]:
        """Parameters whose defaults select semantic controls."""

    @property
    def signature(self) -> inspect.Signature | None:
        """Signature batch requests read callable defaults from."""
        return None

    @property
    def batch_executors(self) -> Mapping[Any, Callable[..., Any]]:
        """Batch executors the callable declares."""
        return self.callable_contract.runtime_batch_executors

    @abstractmethod
    def invoke(
        self,
        value: Any,
        kwargs: Mapping[str, Any],
        *,
        func: Callable[..., Any] | None = None,
    ) -> Any:
        """Call once with the main flow bound to the callable's ABI."""

    @abstractmethod
    def invoke_unbound(self, value: Any, kwargs: Mapping[str, Any]) -> Any:
        """Call once with the value as the stack holds it."""

    def full_stack_inputs(
        self, image: Any, kwargs: Mapping[str, Any],
    ) -> tuple[Any, Mapping[str, Any]]:
        """Return the image and kwargs a whole-stack call receives."""
        return image, kwargs

    def validate_full_stack_kwargs(
        self, contract: type["ProcessingContract"], kwargs: Mapping[str, Any],
    ) -> None:
        """Reject whole-stack kwargs this environment cannot hand ``contract``."""

    def whole_output(self, image: Any, result: Any) -> Any:
        """Return one unsplit call's output in this environment."""
        return result

    def stack_reduction_output(self, result: Any) -> Any:
        """Return a stack-reducing call's output in this environment."""
        return result

    @abstractmethod
    def plane_split(self, image: Any, kwargs: Mapping[str, Any]) -> PlaneSplit | None:
        """Split the image into planes, or ``None`` to call it unsplit."""

    def unsplit(self, image: Any, kwargs: Mapping[str, Any]) -> Any:
        """Call a per-plane callable once on a value that does not split."""
        return self.whole_output(image, self.invoke(image, kwargs))

    @abstractmethod
    def slice_kwargs(
        self,
        split: PlaneSplit,
        kwargs: Mapping[str, Any],
        slice_index: int,
        slice_count: int,
    ) -> Mapping[str, Any]:
        """Project kwargs onto one plane of ``split``."""

    @abstractmethod
    def aggregate_slices(
        self, split: PlaneSplit, batch: "Pure2DSliceResultBatch",
    ) -> Any:
        """Restack per-plane results."""


@dataclass(frozen=True, slots=True)
class ContractProbe:
    """How a callable behaved on a stack probe and on a plane probe."""

    works_on_stack: bool
    works_on_plane: bool
    stack_result_rank: int | None
    spatial_rank: int


class ProcessingContract(ABC, metaclass=AutoRegisterMeta):
    """How one callable executes over its main-flow image stack."""

    __registry_key__ = "key"
    __skip_if_no_key__ = True

    key: ClassVar[str | None] = None
    """Boundary spelling (function cache, catalog, documentation)."""
    collapses_input_plane_axis: ClassVar[bool] = False
    whole_stack_only: ClassVar[bool] = False
    """The callable consumes whole stacks and never per-plane values."""

    @classmethod
    def for_key(cls, key: str) -> type["ProcessingContract"]:
        """Return the contract a boundary spelling names."""
        try:
            return cls.__registry__[key]
        except KeyError as exc:
            raise ValueError(
                f"Unknown processing contract {key!r}; declared: "
                f"{tuple(cls.__registry__)!r}."
            ) from exc

    @classmethod
    def for_probe(cls, probe: ContractProbe) -> type["ProcessingContract"] | None:
        """Return the contract whose declaration explains a probe outcome."""
        explaining = tuple(
            contract for contract in cls.__registry__.values()
            if contract.explains_probe(probe)
        )
        if len(explaining) > 1:
            raise AssertionError(
                f"Processing contracts {explaining!r} all explain {probe!r}."
            )
        return explaining[0] if explaining else None

    @classmethod
    def semantic_control_parameter_types(
        cls,
    ) -> tuple[type[RuntimeParameterDeclarationABC], ...]:
        """Return semantic controls declared by any contract in the family."""
        return tuple(
            dict.fromkeys(
                parameter_type
                for contract in ProcessingContract.__registry__.values()
                for parameter_type in contract.runtime_parameter_types()
                if parameter_type.is_semantic_control
            )
        )

    @classmethod
    @abstractmethod
    def explains_probe(cls, probe: ContractProbe) -> bool:
        """Whether a callable that behaved like ``probe`` follows this contract."""

    @classmethod
    def supports_measurement_image_batch(
        cls, request: RuntimeBatchInvocationRequest,
    ) -> bool:
        """Whether the request already occupies this callable's image domain."""
        return True

    @classmethod
    def runtime_parameter_types(
        cls,
    ) -> tuple[type[RuntimeParameterDeclarationABC], ...]:
        """Return runtime control parameter declarations owned by this contract."""
        return ()

    @classmethod
    def injected_runtime_parameter_types(
        cls,
    ) -> tuple[type[RuntimeParameterDeclarationABC], ...]:
        """Return contract controls that belong on the public wrapper signature."""
        return ()

    @classmethod
    def execution_parameter_names(cls) -> frozenset[str]:
        """Runtime controls that should remain present for contract execution."""
        return frozenset(
            parameter_type.require_parameter_name()
            for parameter_type in cls.runtime_parameter_types()
            if parameter_type.preserve_for_execution
        )

    @classmethod
    def injected_semantic_control_parameter_names(cls) -> frozenset[str]:
        """Semantic controls that this contract may inject into public callables."""
        return frozenset(
            parameter_type.require_parameter_name()
            for parameter_type in cls.injected_runtime_parameter_types()
            if parameter_type.is_semantic_control
        )

    @classmethod
    def main_flow_output_source_payload(cls, source_payload: Any) -> Any:
        """Return source context projected through this contract's output domain."""
        return source_payload

    @classmethod
    def main_flow_call_argument(
        cls, callable_contract: "CallableContract", source_payload: Any,
    ) -> Any:
        """Expose the raw ABI when this contract needs no earlier plane slicing."""
        return callable_contract.runtime_main_flow_call_argument(source_payload)

    @classmethod
    def consume_semantic_controls(
        cls,
        kwargs: MutableMapping[str, Any],
        *,
        func: Callable[..., Any] | None = None,
        parameters: Mapping[str, inspect.Parameter] | None = None,
    ) -> dict[str, Any]:
        """Consume and return semantic selectors owned by this contract."""
        if parameters is None:
            from openhcs.core.callable_contract import CallableMetadata

            parameters = (
                {} if func is None
                else CallableMetadata.callable_signature(func).parameters
            )
        values: dict[str, Any] = {}
        for parameter_type in cls.runtime_parameter_types():
            if not parameter_type.is_semantic_control:
                continue
            name = parameter_type.require_parameter_name()
            if name in kwargs:
                values[name] = kwargs.pop(name)
                continue
            parameter = parameters.get(name)
            if (
                parameter is not None
                and parameter.default is not inspect.Parameter.empty
            ):
                values[name] = parameter.default
                continue
            values[name] = parameter_type.validated_parameter().default
        return values

    @classmethod
    def variable_component_stack_requirement(
        cls,
    ) -> VariableComponentStackRequirement | None:
        """Return the stack-axis requirement this contract declares."""
        return None

    @classmethod
    @abstractmethod
    def execute(
        cls, call: ContractCall, image: Any, kwargs: dict[str, Any],
    ) -> Any:
        """Execute ``call.func`` on ``image`` under this contract."""

    @classmethod
    def execute_whole_stack(
        cls, call: ContractCall, image: Any, kwargs: dict[str, Any],
    ) -> Any:
        """Call once on the whole stack."""
        projected_image, projected_kwargs = call.full_stack_inputs(image, kwargs)
        call.validate_full_stack_kwargs(cls, projected_kwargs)
        return call.whole_output(image, call.invoke(projected_image, projected_kwargs))


class WholeStackInputContract(ProcessingContract):
    """A contract whose callable needs a real stack along the variable axes."""

    @classmethod
    def variable_component_stack_requirement(
        cls,
    ) -> VariableComponentStackRequirement:
        return AlwaysRequiresVariableComponentStack()


class Pure3DContract(WholeStackInputContract):
    """Execute a callable once with full image-domain semantics."""

    key = "pure_3d"
    whole_stack_only = True

    @classmethod
    def explains_probe(cls, probe: ContractProbe) -> bool:
        return probe.works_on_stack and not probe.works_on_plane

    @classmethod
    def execute(cls, call: ContractCall, image: Any, kwargs: dict[str, Any]) -> Any:
        return cls.execute_whole_stack(call, image, kwargs)


class Pure2DContract(ProcessingContract):
    """Execute a callable on each plane of the declared plane axis."""

    key = "pure_2d"

    @classmethod
    def explains_probe(cls, probe: ContractProbe) -> bool:
        return probe.works_on_plane and not probe.works_on_stack

    @classmethod
    def supports_measurement_image_batch(
        cls, request: RuntimeBatchInvocationRequest,
    ) -> bool:
        """Leave preserved per-plane domains to the plane slicer."""
        return (
            not request.execution_mode.per_plane
            or request.plane_projection is None
            or request.plane_projection.plane_index is not None
        )

    @classmethod
    def main_flow_call_argument(
        cls, callable_contract: "CallableContract", source_payload: Any,
    ) -> Any:
        """Retain plane context only for the declared contract execution wrapper."""
        if callable_contract.raw_processing_function is not None:
            return source_payload
        return super().main_flow_call_argument(callable_contract, source_payload)

    @classmethod
    def execute(cls, call: ContractCall, image: Any, kwargs: dict[str, Any]) -> Any:
        return cls.execute_per_plane(call, image, kwargs)

    @classmethod
    def execute_per_plane(
        cls, call: ContractCall, image: Any, kwargs: dict[str, Any],
    ) -> Any:
        """Call once per plane and restack the results."""
        split = call.plane_split(image, kwargs)
        if split is None:
            return call.unsplit(image, kwargs)

        def execute_slice(
            slice_func: Callable[..., Any],
            slice_value: Any,
            slice_kwargs: Mapping[str, Any],
            slice_index: int,
            slice_count: int,
        ) -> Any:
            return contextualize_main_image_output(
                slice_value,
                call.invoke(
                    slice_value,
                    call.slice_kwargs(split, slice_kwargs, slice_index, slice_count),
                    func=slice_func,
                ),
            )

        results = Pure2DSliceBatchExecutor.from_executors(call.batch_executors)(
            RuntimePure2DSliceBatchRequest(
                func=call.func,
                slices_2d=split.slices,
                kwargs=split.kwargs,
                execute_slice=execute_slice,
                signature=call.signature,
            )
        )
        return call.aggregate_slices(split, Pure2DSliceResultBatch.from_results(results))


class FlexibleContract(Pure2DContract, Pure3DContract):
    """Per plane when its slice-by-slice control is on, else the whole stack."""

    key = "flexible"
    whole_stack_only = False

    @classmethod
    def explains_probe(cls, probe: ContractProbe) -> bool:
        return (
            probe.works_on_stack
            and probe.works_on_plane
            and probe.stack_result_rank != probe.spatial_rank
        )

    @classmethod
    def supports_measurement_image_batch(
        cls, request: RuntimeBatchInvocationRequest,
    ) -> bool:
        controls = cls.consume_semantic_controls(dict(request.kwargs), func=request.func)
        return (
            not any(bool(value) for value in controls.values())
            or super().supports_measurement_image_batch(request)
        )

    @classmethod
    def runtime_parameter_types(
        cls,
    ) -> tuple[type[RuntimeParameterDeclarationABC], ...]:
        return (SliceBySliceRuntimeParameter,)

    @classmethod
    def injected_runtime_parameter_types(
        cls,
    ) -> tuple[type[RuntimeParameterDeclarationABC], ...]:
        return cls.runtime_parameter_types()

    @classmethod
    def variable_component_stack_requirement(
        cls,
    ) -> VariableComponentStackRequirement:
        return SemanticControlVariableComponentStackRequirement(
            cls.runtime_parameter_types()
        )

    @classmethod
    def execute(cls, call: ContractCall, image: Any, kwargs: dict[str, Any]) -> Any:
        semantic_controls = cls.consume_semantic_controls(
            kwargs, parameters=call.parameters
        )
        kwargs.update(semantic_controls)
        if any(bool(value) for value in semantic_controls.values()):
            return cls.execute_per_plane(call, image, kwargs)
        return cls.execute_whole_stack(call, image, kwargs)


class VolumetricToSliceContract(WholeStackInputContract):
    """Call once on the whole stack; the result has no plane axis."""

    key = "volumetric_to_slice"
    collapses_input_plane_axis = True

    @classmethod
    def explains_probe(cls, probe: ContractProbe) -> bool:
        return (
            probe.works_on_stack
            and probe.works_on_plane
            and probe.stack_result_rank == probe.spatial_rank
        )

    @classmethod
    def main_flow_output_source_payload(cls, source_payload: Any) -> Any:
        """Consume the declared leading plane axis while preserving provenance."""
        metadata = image_metadata_of(source_payload)
        if not metadata.has_values:
            return source_payload
        if metadata.plane_axis is None:
            raise ValueError(
                "VOLUMETRIC_TO_SLICE output requires a declared input plane axis."
            )
        return metadata.collapse_leading_plane_axis().attach_to(source_payload)

    @classmethod
    def execute(cls, call: ContractCall, image: Any, kwargs: dict[str, Any]) -> Any:
        result = call.stack_reduction_output(call.invoke_unbound(image, kwargs))
        return contextualize_main_image_output(
            cls.main_flow_output_source_payload(image),
            result,
        )


class LibraryContractCall(ContractCall):
    """Registry wrappers: the callable's own contract binds its main flow."""

    def __init__(self, func: Callable[..., Any], args: tuple[Any, ...]) -> None:
        from openhcs.core.callable_contract import CallableContract

        self.func = func
        self.args = tuple(args)
        self._callable_contract = CallableContract.from_callable(func)

    @property
    def callable_contract(self) -> "CallableContract":
        return self._callable_contract

    @property
    def parameters(self) -> Mapping[str, inspect.Parameter]:
        from openhcs.core.callable_contract import CallableMetadata

        return CallableMetadata.callable_signature(self.func).parameters

    @property
    def batch_executors(self) -> Mapping[Any, Callable[..., Any]]:
        from openhcs.core.runtime_batch_contracts import (
            runtime_batch_executors_from_callable,
        )

        return runtime_batch_executors_from_callable(self.func)

    def invoke(
        self,
        value: Any,
        kwargs: Mapping[str, Any],
        *,
        func: Callable[..., Any] | None = None,
    ) -> Any:
        return RuntimeCallablePolicy().invocation(
            self.func if func is None else func,
            (self.callable_contract.runtime_main_flow_call_argument(value), *self.args),
            kwargs,
        ).call()

    def invoke_unbound(self, value: Any, kwargs: Mapping[str, Any]) -> Any:
        return RuntimeCallablePolicy().invocation(
            self.func, (value, *self.args), kwargs,
        ).call()

    def whole_output(self, image: Any, result: Any) -> Any:
        return contextualize_main_image_output(image, result)

    def _positional_parameters(self) -> tuple[inspect.Parameter, ...]:
        return tuple(
            parameter
            for parameter in tuple(inspect.signature(self.func).parameters.values())[1:]
            if parameter.kind
            in {
                inspect.Parameter.POSITIONAL_ONLY,
                inspect.Parameter.POSITIONAL_OR_KEYWORD,
            }
        )

    def _consumes_full_label_stack(self, kwargs: Mapping[str, Any]) -> bool:
        """Whether the callable measures labels over their whole stack."""
        from openhcs.core.pipeline.function_contracts import (
            object_label_input_execution_mode_from_callable,
        )

        if not object_label_input_execution_mode_from_callable(
            self.func
        ).preserves_full_stack(image_stack_required=False):
            return False
        positional = (
            dict(zip((p.name for p in self._positional_parameters()), self.args))
            if self.args else {}
        )
        return {**positional, **kwargs}.get("labels") is not None

    def plane_split(self, image: Any, kwargs: Mapping[str, Any]) -> PlaneSplit | None:
        from arraybridge import MemoryContractAttribute

        output_memory_type = MemoryContractAttribute.OUTPUT.read(self.func)
        input_memory_type = MemoryContractAttribute.INPUT.read(
            self.func,
            output_memory_type,
        )
        slicer = Pure2DInputSlicer.strategy_for_value(image)
        if self._consumes_full_label_stack(kwargs):
            return None
        if slicer.is_single_plane_value(image):
            return None
        input_metadata = image.metadata
        plane_axis = input_metadata.plane_axis
        if plane_axis is None:
            raise ValueError(
                "PURE_2D multi-plane execution requires the input payload to "
                "declare its runtime plane axis."
            )
        kwargs = dict(kwargs)
        if self.args:
            positional_parameters = self._positional_parameters()
            if len(self.args) > len(positional_parameters):
                raise TypeError(
                    f"{self.func.__name__} expected at "
                    f"most {len(positional_parameters)} positional argument(s) after "
                    f"image, got {len(self.args)}."
                )
            for parameter, value in zip(positional_parameters, self.args):
                kwargs.setdefault(parameter.name, value)
            self.args = self.args[len(positional_parameters):]
        return PlaneSplit(
            slices=tuple(slicer.slice_value(image, input_memory_type)),
            plane_axis=plane_axis,
            memory_type=output_memory_type,
            kwargs=kwargs,
            source_aliases=input_metadata.source_image_names,
        )

    def unsplit(self, image: Any, kwargs: Mapping[str, Any]) -> Any:
        if self._consumes_full_label_stack(kwargs):
            return self.invoke_unbound(image, kwargs)
        return super().unsplit(image, kwargs)

    def slice_kwargs(
        self,
        split: PlaneSplit,
        kwargs: Mapping[str, Any],
        slice_index: int,
        slice_count: int,
    ) -> Mapping[str, Any]:
        return RuntimeSliceProjection.kwargs_for_slice(
            kwargs,
            RuntimePlaneAxisValueProjection.from_selected_plane(
                axis=split.plane_axis,
                source_aliases=split.source_aliases,
                plane_index=slice_index,
                axis_size=slice_count,
            ),
        )

    def aggregate_slices(
        self, split: PlaneSplit, batch: "Pure2DSliceResultBatch",
    ) -> Any:
        stacked_main_output = Pure2DAuxiliaryOutputAggregator.aggregate(
            batch.main_outputs,
            split.memory_type,
            plane_axis=split.plane_axis,
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
