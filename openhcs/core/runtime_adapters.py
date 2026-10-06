"""Typed runtime adapter injection contracts for callable execution."""

from __future__ import annotations

import inspect
from collections.abc import Callable, Mapping, MutableMapping
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, TypeVar

from python_introspect import add_parameter_exclusions

from openhcs.constants.constants import Backend, VariableComponents
from openhcs.core.artifact_key_selection import (
    ArtifactOutputPolicy,
    NativeReturnArtifactOutputPolicy,
)
from openhcs.core.aligned_image_payload import (
    ImagePayloadExecutionMode,
)
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ArtifactSpecRef,
)
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.function_patterns import (
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
)
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    NamedSourceBinding,
)
from openhcs.core.source_binding_selection import (
    SourceUniverseRequest,
)
from openhcs.core.source_load_plan import SourceLoadPlan
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisValueProjection,
    RuntimePlaneProjection,
)

if TYPE_CHECKING:
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.runtime_stores import RuntimeArtifactInput


_F = TypeVar("_F", bound=Callable[..., Any])


@dataclass(frozen=True, slots=True, kw_only=True)
class RuntimeImageExecutionContext:
    """Source provenance and execution mode for an image-like invocation."""

    source_image_name: str | None
    execution_mode: ImagePayloadExecutionMode = ImagePayloadExecutionMode.NATURAL
    plane_projection: RuntimePlaneAxisValueProjection | None = None


@dataclass(frozen=True, slots=True, kw_only=True)
class RuntimeAdapterRequest:
    """Runtime data needed to build an invocation-scoped adapter."""

    context: "ProcessingContext"
    callable_contract: "CallableContract | None" = None
    source_payload: object | None = None
    artifact_inputs: Mapping[
        "InvocationArtifactInputProjectionKey",
        "InvocationArtifactInputEdgePlan",
    ] = field(default_factory=dict)
    artifact_outputs: Mapping[ArtifactSpecRef, ArtifactOutputPlan] = field(
        default_factory=dict
    )
    source_binding_plan: CompiledSourceBindingPlan = CompiledSourceBindingPlan.empty()
    group_key: str | None = None
    axis_scope: RuntimeExecutionAxisScope
    plane_projection: RuntimePlaneProjection = field(
        default_factory=RuntimePlaneProjection.stack
    )
    variable_components: tuple[VariableComponents, ...] = ()
    source_load_plan: SourceLoadPlan = field(default_factory=SourceLoadPlan)

    def __post_init__(self) -> None:
        for key, edge in self.artifact_inputs.items():
            if not isinstance(key, InvocationArtifactInputProjectionKey):
                raise TypeError(
                    "Runtime adapter input maps require "
                    "InvocationArtifactInputProjectionKey keys, got "
                    f"{type(key).__name__}."
                )
            if not isinstance(edge, InvocationArtifactInputEdgePlan):
                raise TypeError(
                    "Runtime adapter input maps require "
                    "InvocationArtifactInputEdgePlan values, got "
                    f"{type(edge).__name__} for {key!r}."
                )
            if key != edge.key:
                raise ValueError(
                    f"Runtime adapter input key {key!r} conflicts with compiled "
                    f"edge key {edge.key!r}."
                )
        ArtifactOutputPlan.require_exact_map(
            self.artifact_outputs,
            boundary="Runtime adapter output",
        )

    def source_binding_for_artifact_ref(
        self,
        ref: ArtifactSpecRef,
    ) -> NamedSourceBinding:
        """Return the exact source binding compiled for one artifact input."""

        binding = self.source_binding_plan.binding_for_artifact_ref(ref)
        if binding is None:
            raise ValueError(
                "Runtime adapter source artifact has no exact compiled source "
                f"binding for {ref!r}."
            )
        return binding

    def require_callable_contract(self) -> "CallableContract":
        """Return the exact compiled callable contract for this invocation."""

        from openhcs.core.callable_contract import CallableContract

        contract = self.callable_contract
        if not isinstance(contract, CallableContract):
            raise TypeError(
                "RuntimeAdapterRequest requires the compiled CallableContract "
                "for artifact role resolution."
            )
        return contract

    def artifact_output_plan(
        self,
        ref: ArtifactSpecRef,
    ) -> ArtifactOutputPlan | None:
        """Return the selected output plan for one exact artifact identity."""

        if not isinstance(ref, ArtifactSpecRef):
            raise TypeError(
                "RuntimeAdapterRequest.artifact_output_plan requires an "
                f"ArtifactSpecRef, got {type(ref).__name__}."
            )
        if ref.plan_type is not ArtifactOutputPlan:
            raise TypeError(
                "Runtime adapter output-plan lookup requires an output artifact "
                f"ref, got {ref!r}."
            )
        plan = self.artifact_outputs.get(ref)
        if plan is None:
            return None
        return plan

    def require_artifact_output_plan(
        self,
        ref: ArtifactSpecRef,
    ) -> ArtifactOutputPlan:
        """Return one exact selected output plan or fail loudly."""

        plan = self.artifact_output_plan(ref)
        if plan is None:
            raise RuntimeError(
                f"Runtime adapter has no selected artifact output plan for {ref!r}."
            )
        return plan

    def selected_artifact_input_specs(self) -> ArtifactSpecCollection:
        """Return exact active input declarations in callable ABI order."""

        declared = self.require_callable_contract().artifact_inputs
        selected_occurrences = declared.select_declared_occurrences(
            edge.spec for edge in self.artifact_inputs.values()
        )
        selected_refs = selected_occurrences.ref_set()
        return ArtifactSpecCollection(
            spec for spec in declared if spec.ref() in selected_refs
        )

    def require_artifact_input_edge(
        self,
        ref: ArtifactSpecRef,
    ) -> "InvocationArtifactInputEdgePlan":
        """Return one exact runtime authority for a compiled input identity."""

        if not isinstance(ref, ArtifactSpecRef):
            raise TypeError(
                "RuntimeAdapterRequest.require_artifact_input_edge requires an "
                f"ArtifactSpecRef, got {type(ref).__name__}."
            )
        if ref.plan_type is not ArtifactInputPlan:
            raise TypeError(
                "Runtime adapter input-edge lookup requires an input artifact ref, "
                f"got {ref!r}."
            )
        matches = tuple(
            edge for edge in self.artifact_inputs.values() if edge.spec.ref() == ref
        )
        if not matches:
            raise RuntimeError(
                f"Runtime adapter has no compiled artifact input occurrence for "
                f"{ref!r}."
            )
        first = matches[0]
        if any(
            edge.spec != first.spec
            or (edge.storage_plan, edge.projection, edge.main_flow_projection)
            != (first.storage_plan, first.projection, first.main_flow_projection)
            for edge in matches[1:]
        ):
            raise ValueError(
                f"Compiled artifact input occurrences for {ref!r} resolve to "
                "different runtime authorities."
            )
        return first

    def runtime_artifact_input(
        self,
        edge: InvocationArtifactInputEdgePlan,
        *,
        backend: str,
    ) -> "RuntimeArtifactInput":
        """Bind an exact compiled input to this request's declared source context."""
        from openhcs.core.runtime_stores import RuntimeArtifactInput

        return RuntimeArtifactInput(
            edge_plan=edge,
            axis_scope=self.axis_scope,
            backend=backend,
            source_binding_plan=self.source_binding_plan,
        )

    def source_artifact_payload(self, ref: ArtifactSpecRef) -> object:
        """Resolve a named input through its existing source-origin owner."""
        binding = self.source_binding_for_artifact_ref(ref)
        owner = SourceUniverseRequest.for_binding(binding)
        return owner.source_artifact_payload(self, binding)


RuntimeAdapterFactory = Callable[[RuntimeAdapterRequest], object]
RuntimeCallableFactory = Callable[
    [Callable[..., object], "CallableContract"],
    Callable[..., object],
]


@dataclass(frozen=True, slots=True)
class RuntimeAdapterSpec:
    """Callable-owned runtime adapter injection contract."""

    parameter_name: str
    factory: RuntimeAdapterFactory
    manages_artifact_inputs: bool = False
    artifact_output_policy: type[ArtifactOutputPolicy] = (
        NativeReturnArtifactOutputPolicy
    )
    runtime_callable_factory: RuntimeCallableFactory | None = None

    def invocation_domain_inputs(
        self, contract: "CallableContract",
    ) -> ArtifactSpecCollection:
        """Use declared context inputs when the callable has no raw image ABI."""
        if contract.accepts_implicit_main_flow_input:
            return ArtifactSpecCollection(())
        return contract.group_scope_inputs

    def consumes_image_input(
        self,
        contract: "CallableContract",
        spec: ArtifactSpec,
    ) -> bool:
        """Distinguish image arguments from artifact-context dependencies."""
        return (
            spec.binds_callable_parameter() or contract.accepts_implicit_main_flow_input
        )

    def __post_init__(self) -> None:
        if not self.parameter_name:
            raise ValueError("RuntimeAdapterSpec.parameter_name cannot be empty.")
        if not callable(self.factory):
            raise TypeError("RuntimeAdapterSpec.factory must be callable.")
        if (
            not isinstance(self.artifact_output_policy, type)
            or not issubclass(self.artifact_output_policy, ArtifactOutputPolicy)
            or inspect.isabstract(self.artifact_output_policy)
        ):
            raise TypeError(
                "RuntimeAdapterSpec.artifact_output_policy requires a concrete "
                "ArtifactOutputPolicy declaration."
            )
        if self.runtime_callable_factory is not None and not callable(
            self.runtime_callable_factory
        ):
            raise TypeError(
                "RuntimeAdapterSpec.runtime_callable_factory must be callable or None."
            )

    def require_parameter_name(self) -> str:
        """Return the callable ABI name for this adapter injection."""
        return self.parameter_name

    def validate_callable_signature(self, func: Callable[..., Any]) -> None:
        """Ensure the declared adapter parameter exists at declaration time."""
        parameter_name = self.require_parameter_name()
        if parameter_name in inspect.signature(func).parameters:
            return
        raise TypeError(
            "Runtime adapter declaration requires callable signature parameter "
            f"{parameter_name!r}."
        )

    def executable_callable(
        self,
        resolved_callable: Callable[..., object],
        contract: "CallableContract",
    ) -> Callable[..., object]:
        """Build the executable callable from one ordinarily resolved callable."""
        factory = self.runtime_callable_factory
        if factory is None:
            return resolved_callable
        return factory(resolved_callable, contract)


def runtime_adapter(
    parameter_name: str,
    factory: RuntimeAdapterFactory,
    *,
    manages_artifact_inputs: bool = False,
    artifact_output_policy: type[
        ArtifactOutputPolicy
    ] = NativeReturnArtifactOutputPolicy,
    runtime_callable_factory: RuntimeCallableFactory | None = None,
) -> Callable[[_F], _F]:
    """Declare that a callable needs an invocation-scoped runtime adapter."""
    spec = RuntimeAdapterSpec(
        parameter_name=parameter_name,
        factory=factory,
        manages_artifact_inputs=manages_artifact_inputs,
        artifact_output_policy=artifact_output_policy,
        runtime_callable_factory=runtime_callable_factory,
    )

    def decorator(func: _F) -> _F:
        spec.validate_callable_signature(func)
        namespace = vars(func)
        if not isinstance(namespace, MutableMapping):
            raise TypeError(f"{func!r} does not expose a mutable metadata namespace.")
        namespace[FunctionContractAttribute.runtime_adapter] = spec
        add_parameter_exclusions(func, parameter_name)
        return func

    return decorator


def runtime_adapter_spec_from_callable(func: Any) -> RuntimeAdapterSpec | None:
    """Return the callable's declared runtime adapter contract, if any."""
    if callable(func):
        spec = _callable_namespace_runtime_adapter(func)
        if spec is not None:
            return spec
    reference_spec = _function_reference_runtime_adapter(func)
    if reference_spec is None:
        return None
    return reference_spec


def _callable_namespace_runtime_adapter(
    func: Callable[..., Any],
) -> RuntimeAdapterSpec | None:
    """Return adapter metadata preserved on callable namespaces."""
    try:
        namespace = vars(func)
    except TypeError:
        return None
    value = namespace.get(FunctionContractAttribute.runtime_adapter)
    if value is None:
        return None
    if not isinstance(value, RuntimeAdapterSpec):
        raise TypeError(
            "Runtime adapter metadata must be a RuntimeAdapterSpec, "
            f"got {type(value).__name__}."
        )
    return value


def _function_reference_runtime_adapter(func: object) -> RuntimeAdapterSpec | None:
    from openhcs.core.function_reference import FunctionReference

    if not isinstance(func, FunctionReference):
        return None
    return func.metadata.runtime_adapter
