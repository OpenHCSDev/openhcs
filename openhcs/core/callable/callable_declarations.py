from __future__ import annotations

import inspect
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from enum import Enum
from threading import Lock
from typing import Any, ClassVar

from metaclass_registry.caches import IdentityBoundProcessCache
from python_introspect import RuntimeParameterDeclarationABC



class CallableContractRuntimeCache(IdentityBoundProcessCache):
    """Retain executable callables for their exact compiled declaration owners."""

    resolution_lock = Lock()


@dataclass(frozen=True, slots=True)
class CallableImportIdentity:
    """Stable top-level import identity for one callable declaration."""

    module_name: str
    function_name: str

    def __post_init__(self) -> None:
        for field_name, value in (
            ("module_name", self.module_name),
            ("function_name", self.function_name),
        ):
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"CallableImportIdentity.{field_name} must be a non-empty string."
                )

    @classmethod
    def from_callable(cls, func: Callable[..., object]) -> CallableImportIdentity:
        """Return the import identity declared by a resolved callable object."""

        if not callable(func):
            raise TypeError(
                "Callable import identity requires a callable object, got "
                f"{type(func).__name__}."
            )
        return cls(
            module_name=func.__module__,
            function_name=func.__name__,
        )

    @property
    def import_path(self) -> str:
        """Return the complete import path for this callable."""

        return f"{self.module_name}.{self.function_name}"


class KeywordRuntimeParameter(RuntimeParameterDeclarationABC):
    """Reusable declaration for one runtime-owned keyword-only parameter."""

    parameter_name: ClassVar[str | None] = None
    annotation_type: ClassVar[Any] = inspect.Parameter.empty
    parameter_default: ClassVar[Any] = inspect.Parameter.empty

    @classmethod
    def require_parameter_name(cls) -> str:
        """Return the non-empty callable parameter name declared by the leaf."""

        parameter_name = cls.parameter_name
        if not isinstance(parameter_name, str) or not parameter_name.strip():
            raise ValueError(f"{cls.__name__} must declare parameter_name.")
        return parameter_name

    @classmethod
    def default_value(cls) -> Any:
        """Return the declared callable default."""

        return cls.parameter_default

    @classmethod
    def parameter(cls) -> inspect.Parameter:
        """Return the keyword-only signature parameter for this declaration."""

        return inspect.Parameter(
            cls.require_parameter_name(),
            inspect.Parameter.KEYWORD_ONLY,
            default=cls.default_value(),
            annotation=cls.annotation_type,
        )


class FunctionStepExecutionScope(str, Enum):
    """Lifecycle scope for one compiled FunctionStep callable."""

    AXIS = "axis"
    PLATE = "plate"

    def context_owns_outputs(self, *, metadata_writer: bool) -> bool:
        """Return whether one compiled context owns this invocation's outputs."""
        return self is FunctionStepExecutionScope.AXIS or metadata_writer

    @property
    def requires_parent_runtime_observation(self) -> bool:
        """Return whether worker records must survive for parent-side execution."""

        return self is FunctionStepExecutionScope.PLATE

    @classmethod
    def require_uniform(
        cls,
        contracts: Iterable["CallableContract"],
    ) -> FunctionStepExecutionScope:
        """Return the one execution scope shared by all callable contracts."""
        scopes = tuple(contract.execution_scope for contract in contracts)
        if not scopes:
            return cls.AXIS
        first = scopes[0]
        if any(scope is not first for scope in scopes[1:]):
            raise ValueError(
                "FunctionStep callable pattern has mixed execution scopes; "
                "all invocation contracts must declare one uniform scope."
            )
        return first


class ImagePayloadConsumption(str, Enum):
    """How a callable consumes its primary image payload."""

    def __new__(cls, value: str, retain_single_input: bool):
        member = str.__new__(cls, value)
        member._value_ = value
        member._retain_single_input = retain_single_input
        return member

    NATURAL = ("natural", True)
    COMPOSED = ("composed", False)

    def compose_image_payload(
        self,
        owner_name: str,
        image_payloads: tuple[Any, ...],
        *,
        slice_contexts: Sequence[AlignedImageSliceContext] = (),
        stack_broadcast_source_indices: Sequence[int | None] = (),
    ) -> ImagePayloadComposition:
        """Admit primary sources to the original alignment/bundle algorithm."""

        from openhcs.core.payload.aligned_image_payload import compose_aligned_image_payload

        return compose_aligned_image_payload(
            owner_name,
            image_payloads,
            slice_contexts=slice_contexts,
            stack_broadcast_source_indices=stack_broadcast_source_indices,
            retain_single_input=self._retain_single_input,
        )
