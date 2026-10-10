"""Runtime batch execution contracts shared by compiler and pipeline decorators."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Hashable, Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
import inspect
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar, Generic, TypeVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.callable_contract import CallableContract, CallableMetadata, KeywordRuntimeParameter
from openhcs.core.function_reference import FunctionReference
from openhcs.core.runtime_adapters import RuntimeImageExecutionContext
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisValueProjection,
)

if TYPE_CHECKING:
    from openhcs.core.processing_contracts import ProcessingContract
    from openhcs.core.runtime_stores import RuntimeArtifactBatch
    from openhcs.core.context.processing_context import ProcessingContext


F = TypeVar("F", bound=Callable)
RuntimeSliceDataT = TypeVar("RuntimeSliceDataT")
RuntimeSliceResultT = TypeVar("RuntimeSliceResultT")
RuntimeKwargValueT = TypeVar("RuntimeKwargValueT")


class SliceIndexRuntimeParameter(KeywordRuntimeParameter):
    """Runtime-supplied pure-2D plane index parameter."""

    parameter_name = "slice_index"
    annotation_type = int | None
    parameter_default = None


class RuntimePlaneAxisValueProjectionParameter(KeywordRuntimeParameter):
    """Runtime-supplied exact image plane-axis projection."""

    parameter_name = "runtime_plane_projection"
    annotation_type = RuntimePlaneAxisValueProjection | None
    parameter_default = None


def runtime_callable_defaults(
    func: Callable[..., object], *, signature: inspect.Signature | None = None,
) -> Mapping[str, object]:
    """Return callable defaults visible to runtime batch executors."""
    try:
        callable_signature = CallableMetadata.callable_signature(func) if signature is None else signature
    except (TypeError, ValueError) as exc:
        raise TypeError(
            f"Runtime batch function {func!r} must expose an inspectable signature."
        ) from exc
    defaults: dict[str, object] = {}
    for parameter in callable_signature.parameters.values():
        if parameter.default is inspect.Parameter.empty:
            continue
        if parameter.kind in {
            inspect.Parameter.POSITIONAL_ONLY,
            inspect.Parameter.VAR_POSITIONAL,
            inspect.Parameter.VAR_KEYWORD,
        }:
            continue
        defaults[parameter.name] = parameter.default
    return MappingProxyType(defaults)


@dataclass(frozen=True, slots=True, kw_only=True)
class RuntimeBatchInvocationRequest(RuntimeImageExecutionContext):
    """One invocation inside a nominal runtime batch."""

    func: Callable[..., object]
    image: object
    kwargs: Mapping[str, object]
    batch_index: int
    batch_count: int
    semantic_group_key: tuple[Hashable, ...] | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "kwargs",
            MappingProxyType(
                {
                    **runtime_callable_defaults(self.func),
                    **dict(self.kwargs),
                }
            ),
        )

    def batch_executor_request(
        self, *, processing_contract: "type[ProcessingContract]",
    ) -> "RuntimeBatchInvocationRequest | None":
        """Return a request projected into the batch executor's image domain.

        A batch executor may inspect image pixels before it delegates the actual
        call, so it must see the same image domain as the callable. The
        contract decides whether the request already occupies that domain; the
        execution mode projects it there, or returns ``None`` to leave it to
        the ordinary contract executor.
        """

        if not processing_contract.supports_measurement_image_batch(self):
            return None
        return self.execution_mode.batch_request(self)


class RuntimeBatchExecutionDomain(str, Enum):
    """Nominal domains where one callable can batch equivalent invocations."""

    PURE_2D_SLICES = "pure_2d_slices"
    MEASUREMENT_IMAGES = "measurement_images"
    ARTIFACT_PARTITIONS = "artifact_partitions"


@dataclass(frozen=True, slots=True)
class RuntimeArtifactPartitionBatchRequest:
    """Parent-admitted artifact batch mapped through existing worker resources.

    The declared executor owns partition eligibility and global reductions.
    ProcessingContext stays in the parent and is never part of worker requests.
    """

    func: Callable[..., object]
    artifact_batch: RuntimeArtifactBatch
    kwargs: Mapping[str, object]
    runtime_context: ProcessingContext | None
    map_partition_invocations: Callable[
        [Callable[[object], object], Sequence[object]], tuple[object, ...]
    ]

    @classmethod
    def from_contract(
        cls,
        contract: CallableContract,
        *,
        artifact_batch: RuntimeArtifactBatch,
        kwargs: Mapping[str, object],
        runtime_context: ProcessingContext | None,
        map_partition_invocations: Callable[
            [Callable[[object], object], Sequence[object]], tuple[object, ...]
        ],
    ) -> RuntimeArtifactPartitionBatchRequest:
        """Bind the raw plate ABI through the existing wrapper-control owner.

        Plate wrappers project Enableable controls before invoking their raw
        processing function. Partition executors enter that same raw boundary;
        compiler admission continues to own whether the invocation is enabled.
        """
        from python_introspect import Enableable
        from openhcs.core.processing_contracts import SignatureFilteredKwargs

        raw_callable = contract.resolve_raw_runtime_callable()
        kwargs = SignatureFilteredKwargs.accepted_kwargs(
            raw_callable,
            Enableable.without_parameter(kwargs),
            signature=contract.raw_runtime_signature,
        )
        return cls(
            func=raw_callable,
            artifact_batch=artifact_batch,
            kwargs=kwargs,
            runtime_context=runtime_context,
            map_partition_invocations=map_partition_invocations,
        )


class RuntimeBatchCallableMetadataField(str, Enum):
    """Callable metadata fields owned by runtime batch contracts."""

    EXECUTORS = "__openhcs_runtime_batch_executors__"

    def owner_label(self, func: Callable) -> str:
        """Return a compact field label for validation errors."""
        return f"{func}.{self.value}"


RUNTIME_BATCH_EXECUTORS_ATTR = RuntimeBatchCallableMetadataField.EXECUTORS.value


@dataclass(frozen=True, slots=True)
class RuntimePure2DSliceBatchRequest(
    Generic[RuntimeSliceDataT, RuntimeSliceResultT, RuntimeKwargValueT],
):
    """Nominal request for equivalent pure-2D slice invocations."""

    func: Callable[..., RuntimeSliceResultT]
    slices_2d: tuple[RuntimeSliceDataT, ...]
    kwargs: Mapping[str, RuntimeKwargValueT]
    execute_slice: Callable[
        [
            Callable[..., RuntimeSliceResultT],
            RuntimeSliceDataT,
            Mapping[str, RuntimeKwargValueT],
            int,
            int,
        ],
        RuntimeSliceResultT,
    ]
    signature: inspect.Signature | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "kwargs",
            MappingProxyType(
                {
                    **runtime_callable_defaults(self.func, signature=self.signature),
                    **dict(self.kwargs),
                }
            ),
        )

    @property
    def slice_count(self) -> int:
        """Number of slice invocations in this batch."""
        return len(self.slices_2d)

    def execute_one(self, slice_index: int) -> RuntimeSliceResultT:
        """Execute one slice through the runtime-owned invocation path."""
        return self.execute_one_with_kwargs(slice_index, self.kwargs)

    def execute_each(self) -> list[RuntimeSliceResultT]:
        """Execute every slice of this batch, one invocation per slice."""
        return [self.execute_one(slice_index) for slice_index in range(self.slice_count)]

    def execute_one_with_kwargs(
        self,
        slice_index: int,
        kwargs: Mapping[str, RuntimeKwargValueT],
    ) -> RuntimeSliceResultT:
        """Execute one slice through the callable's declared runtime contract."""
        return self.execute_slice(
            self.func,
            self.slices_2d[slice_index],
            kwargs,
            slice_index,
            self.slice_count,
        )


class RuntimeBatchExecutor(ABC, metaclass=AutoRegisterMeta):
    """Nominal callable object for reusable runtime batch execution policies."""

    __registry_key__ = "executor_name"
    __skip_if_no_key__ = True
    executor_name: ClassVar[str | None] = None

    @abstractmethod
    def __call__(
        self,
        request: RuntimePure2DSliceBatchRequest[
            RuntimeSliceDataT,
            RuntimeSliceResultT,
            RuntimeKwargValueT,
        ],
    ) -> list[RuntimeSliceResultT]:
        """Execute one runtime batch domain."""


@dataclass(frozen=True, slots=True)
class RuntimeBatchCallableFamily:
    """Callable plus its raw processing ancestor for inherited batch contracts."""

    func: Callable | FunctionReference
    raw_processing_function: Callable | FunctionReference | None = None

    def __post_init__(self) -> None:
        if self.raw_processing_function is not None and not (
            callable(self.raw_processing_function)
            or isinstance(self.raw_processing_function, FunctionReference)
        ):
            raise TypeError(
                "raw_processing_function must be callable or FunctionReference "
                "when inheriting runtime "
                "batch executors, got "
                f"{type(self.raw_processing_function).__name__}."
            )

    def executors(self) -> Mapping[RuntimeBatchExecutionDomain, Callable]:
        """Return batch executors declared by the wrapper family."""
        declared_callable = (
            self.func.resolve()
            if isinstance(self.func, FunctionReference)
            else self.func
        )
        batch_executors = dict(runtime_batch_executors_from_callable(declared_callable))
        if self.raw_processing_function is not None:
            raw_callable = (
                self.raw_processing_function.resolve()
                if isinstance(self.raw_processing_function, FunctionReference)
                else self.raw_processing_function
            )
            inherited = runtime_batch_executors_from_callable(
                raw_callable
            )
            for domain, executor in inherited.items():
                if domain not in batch_executors:
                    batch_executors[domain] = executor
        return MappingProxyType(batch_executors)


class Pure2DSliceBatchExecutor(RuntimeBatchExecutor):
    """Base contract for equivalent pure-2D slice batch execution."""

    @classmethod
    def from_executors(
        cls, executors: Mapping[RuntimeBatchExecutionDomain, Callable] | None,
    ) -> Callable:
        """Honor a declared pure-2D executor before the nominal serial default."""
        declared = None if executors is None else executors.get(RuntimeBatchExecutionDomain.PURE_2D_SLICES)
        return declared if callable(declared) else cls.default_executor()

    @classmethod
    def default_executor(cls) -> "Pure2DSliceBatchExecutor":
        """Return the single-thread default pure-2D batch executor."""
        return SerialPure2DSliceBatchExecutor()


class ParallelPure2DSliceBatchExecutor(Pure2DSliceBatchExecutor):
    """Explicit thread-backed executor for independent pure-2D slice batches."""

    executor_name = "parallel_pure_2d_slices"

    def __call__(
        self,
        request: RuntimePure2DSliceBatchRequest[
            RuntimeSliceDataT,
            RuntimeSliceResultT,
            RuntimeKwargValueT,
        ],
    ) -> list[RuntimeSliceResultT]:
        raise RuntimeError(
            "ParallelPure2DSliceBatchExecutor is disabled for single-thread runtime "
            "benchmarking. Use a process-level batching contract instead."
        )


class SerialPure2DSliceBatchExecutor(Pure2DSliceBatchExecutor):
    """Default single-process, single-thread pure-2D batch executor."""

    executor_name = "serial_pure_2d_slices"

    def __call__(
        self,
        request: RuntimePure2DSliceBatchRequest[
            RuntimeSliceDataT,
            RuntimeSliceResultT,
            RuntimeKwargValueT,
        ],
    ) -> list[RuntimeSliceResultT]:
        return request.execute_each()


def runtime_batch_executors_from_callable(
    func: Callable,
) -> Mapping[RuntimeBatchExecutionDomain, Callable]:
    """Return declared batch executors keyed by runtime batch domain."""
    executors_field = RuntimeBatchCallableMetadataField.EXECUTORS
    try:
        namespace = vars(func)
    except TypeError:
        declared = {}
    else:
        if executors_field.value in namespace:
            declared = namespace[executors_field.value]
        else:
            declared = {}
    if declared is None:
        declared = {}
    if not isinstance(declared, Mapping):
        raise TypeError(f"{executors_field.owner_label(func)} must be a mapping.")
    batch_executors: dict[RuntimeBatchExecutionDomain, Callable] = {}
    for raw_domain, executor in declared.items():
        domain = (
            raw_domain
            if isinstance(raw_domain, RuntimeBatchExecutionDomain)
            else RuntimeBatchExecutionDomain(str(raw_domain))
        )
        if not callable(executor):
            raise TypeError(
                f"{executors_field.owner_label(func)}[{domain.value!r}] must "
                f"be callable, got {type(executor).__name__}."
            )
        batch_executors[domain] = executor
    return MappingProxyType(batch_executors)


def runtime_batch_executor(
    domain: RuntimeBatchExecutionDomain,
    executor: Callable,
) -> Callable[[F], F]:
    """Declare a callable-owned batch executor for one runtime batch domain."""
    if not isinstance(domain, RuntimeBatchExecutionDomain):
        raise TypeError(
            "runtime_batch_executor domain must be RuntimeBatchExecutionDomain, "
            f"got {type(domain).__name__}."
        )
    if not callable(executor):
        raise TypeError(
            "runtime_batch_executor executor must be callable, "
            f"got {type(executor).__name__}."
        )

    def decorator(func: F) -> F:
        batch_executors = dict(runtime_batch_executors_from_callable(func))
        batch_executors[domain] = executor
        try:
            namespace = vars(func)
        except TypeError as exc:
            raise TypeError(
                f"{func!r} cannot carry runtime batch executor metadata."
            ) from exc
        namespace[RuntimeBatchCallableMetadataField.EXECUTORS.value] = MappingProxyType(
            batch_executors
        )
        return func

    return decorator


def pure_2d_batch_executor(executor: Callable) -> Callable[[F], F]:
    """Declare a batch executor for equivalent pure-2D slice invocations."""
    return runtime_batch_executor(
        RuntimeBatchExecutionDomain.PURE_2D_SLICES,
        executor,
    )


def measurement_image_batch_executor(executor: Callable) -> Callable[[F], F]:
    """Declare a batch executor for equivalent measurement-image invocations."""
    return runtime_batch_executor(
        RuntimeBatchExecutionDomain.MEASUREMENT_IMAGES,
        executor,
    )
