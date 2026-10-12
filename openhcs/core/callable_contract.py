"""Typed callable contracts used by compiler phases.

This module centralizes metadata extraction from processing callables so the
compiler has one source of truth for memory and artifact declarations.
"""

from __future__ import annotations

import dataclasses
import inspect
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, MutableMapping, Sequence
from dataclasses import MISSING, asdict, dataclass, fields, is_dataclass
from enum import Enum
from functools import cache, wraps
from pathlib import Path
from threading import Lock
from types import MappingProxyType
from typing import (
    TYPE_CHECKING,
    Any,
    ClassVar,
    Mapping,
    get_args,
    get_type_hints,
)

from arraybridge import MemoryContractAttribute, MemoryType
from python_introspect import (
    RuntimeParameterDeclarationABC,
    add_parameter_exclusions,
    coerce_enum_member,
    declared_enum_type,
    enum_member_type,
    is_union_type,
    resolve_annotated,
    validate_annotation_value,
)

from openhcs.core.image_payload_execution_mode import (
    ImagePayloadExecutionMode,
)
from openhcs.core.artifact_key_selection import (
    ArtifactOutputPolicy,
    ArtifactPlanKeySelector,
    NativeReturnArtifactOutputPolicy,
)
from openhcs.core.artifacts.plans import ArtifactOutputPlan, ArtifactSpecRef
from openhcs.core.artifacts.specs import ArtifactSpec, ArtifactSpecCollection
from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.variable_component_stack_requirement import (
    VariableComponentStackRequirement,
)
from metaclass_registry.caches import IdentityBoundProcessCache
from openhcs.core.axes import AxisRole

if TYPE_CHECKING:
    from openhcs.core.aligned_image_payload import (
        AlignedImageSliceContext,
        ImagePayloadComposition,
    )
    from openhcs.core.function_reference import FunctionReference
    from openhcs.core.image_file_serialization import ImageFileSourceMetadata
    from openhcs.core.pipeline.compilation_session import CompilationPathResolver
    from openhcs.core.processing_preparation import PreparationOperation
    from openhcs.core.runtime_adapters import RuntimeAdapterSpec
    from openhcs.core.runtime_output_matching import RuntimeMatchedOutput
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
    from openhcs.core.runtime_batch_contracts import RuntimeBatchExecutionDomain
    from openhcs.core.vfs_protocol import DatasetPathDeclaration
    from openhcs.core.processing_contracts import (
        ProcessingContract,
    )


CallableNamespace = Mapping[str, Any]


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
    def from_callable(cls, func: Callable[..., object]) -> "CallableImportIdentity":
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


class CompilerPreparedAutoRegisterFamily(ABC):
    """AutoRegisterMeta family that can prepare runtime compiler substrates."""

    @classmethod
    @abstractmethod
    def prepare_registered_family(cls) -> None:
        """Prepare registered implementations before timed callable execution."""

    @classmethod
    def cache_preparation_operations(cls) -> tuple[PreparationOperation, ...]:
        """Project cache work independently of process-local readiness."""
        from openhcs.core.processing_preparation import RegistryFamilyPreparation

        return (RegistryFamilyPreparation(cls),)

    @classmethod
    def can_prepare_in_child(cls) -> bool:
        """Whether preparation populates a persistent cache the parent can load."""
        return False


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
    ) -> "FunctionStepExecutionScope":
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
        from openhcs.core.aligned_image_payload import compose_aligned_image_payload

        return compose_aligned_image_payload(
            owner_name,
            image_payloads,
            slice_contexts=slice_contexts,
            stack_broadcast_source_indices=stack_broadcast_source_indices,
            retain_single_input=self._retain_single_input,
        )


@dataclass(frozen=True, slots=True)
class PayloadAxisRequirement:
    """A callable's primary image must declare a payload axis with ``role``."""

    role: type[AxisRole]

    def __post_init__(self) -> None:
        if not (isinstance(self.role, type) and issubclass(self.role, AxisRole)):
            raise TypeError(
                f"PayloadAxisRequirement.role must be an AxisRole, got {self.role!r}."
            )

    @property
    def label(self) -> str:
        return f"payload axis {self.role.__name__}"

    def validate_source_metadata(
        self,
        metadata: ImageFileSourceMetadata,
        *,
        source_path: Path,
        load_as_monochrome: bool,
    ) -> None:
        """Validate one exact source after source-binding transformations."""

        if not load_as_monochrome and metadata.pixel_semantics.axes.with_role(self.role):
            return
        raise ValueError(
            f"Primary image requires a declared {self.role.__name__} payload axis, "
            f"but {source_path} has none after source-binding transformations."
        )


class PayloadAxisTransition(ABC):
    """Declared effect of a callable on its primary image's payload axes."""

    @abstractmethod
    def preserves(self, requirement: PayloadAxisRequirement) -> bool:
        """Return whether input evidence for ``requirement`` survives the call."""

    @abstractmethod
    def creates(self, requirement: PayloadAxisRequirement) -> bool:
        """Return whether the call supplies the axis without source inheritance."""

    def proves(self, requirement: PayloadAxisRequirement) -> bool:
        return self.preserves(requirement) or self.creates(requirement)


@dataclass(frozen=True, slots=True)
class PreservedPayloadAxes(PayloadAxisTransition):
    """The output declares the same payload axes as the input."""

    def preserves(self, requirement: PayloadAxisRequirement) -> bool:
        del requirement
        return True

    def creates(self, requirement: PayloadAxisRequirement) -> bool:
        del requirement
        return False


@dataclass(frozen=True, slots=True)
class CreatedPayloadAxis(PayloadAxisTransition):
    """The output declares a new payload axis with ``role``."""

    role: type[AxisRole]

    def preserves(self, requirement: PayloadAxisRequirement) -> bool:
        del requirement
        return False

    def creates(self, requirement: PayloadAxisRequirement) -> bool:
        return issubclass(self.role, requirement.role)


class CallableSignature(inspect.Signature):
    """Canonical ABI with path declarations derived from its own parameters."""

    __slots__ = ("_declared_path_parameters",)

    def __init__(
        self,
        parameters=None,
        *,
        return_annotation=inspect.Signature.empty,
        __validate_parameters__=True
    ):
        from openhcs.core.vfs_protocol import DatasetPathDeclaration

        super().__init__(
            parameters,
            return_annotation=return_annotation,
            __validate_parameters__=__validate_parameters__,
        )
        self._declared_path_parameters = MappingProxyType(
            {
                name: declaration
                for name, parameter in self.parameters.items()
                for declaration in (
                    DatasetPathDeclaration.from_annotation(parameter.annotation),
                )
                if declaration is not None
            }
        )

    @classmethod
    def from_signature(cls, signature: inspect.Signature) -> "CallableSignature":
        """Reuse an admitted ABI or enrich a plain signature at its boundary."""
        return (
            signature
            if isinstance(signature, cls)
            else cls(
                signature.parameters.values(),
                return_annotation=signature.return_annotation,
            )
        )

    @property
    def declared_path_parameters(self) -> Mapping[str, "DatasetPathDeclaration"]:
        return self._declared_path_parameters


class DeclaredValue(ABC):
    """How one callable-namespace declaration is validated and normalized."""

    default: ClassVar[Any] = None
    # A declaration whose default is itself a decision (not "undeclared") is
    # always written, so a reader never re-derives it.
    written_when_default: ClassVar[bool] = False

    def read(self, value: object, *, owner: str) -> Any:
        """Return the declared value, or this kind's default when undeclared."""
        if value is None:
            return self.default
        if not self.accepts(value):
            raise TypeError(f"{owner} must be {self.description()}, got {value!r}.")
        return self.normalize(value, owner=owner)

    @abstractmethod
    def accepts(self, value: object) -> bool:
        """Whether ``value`` is a declaration of this kind."""

    @abstractmethod
    def description(self) -> str:
        """What a valid declaration is, for error messages."""

    def normalize(self, value: Any, *, owner: str) -> Any:
        return value


@dataclass(frozen=True)
class DeclaredInstance(DeclaredValue):
    """An instance of one type; ``kind`` may be a zero-argument resolver."""

    kind: type | Callable[[], type]

    def resolved_kind(self) -> type:
        return self.kind if isinstance(self.kind, type) else self.kind()

    def accepts(self, value: object) -> bool:
        return isinstance(value, self.resolved_kind())

    def description(self) -> str:
        return self.resolved_kind().__name__


@dataclass(frozen=True)
class DeclaredSignature(DeclaredInstance):
    """A prepared signature snapshot, admitted as its canonical ABI view."""

    kind: type = inspect.Signature

    def description(self) -> str:
        return "an inspect.Signature"

    def normalize(self, value: Any, *, owner: str) -> Any:
        return CallableSignature.from_signature(value)


@dataclass(frozen=True)
class DeclaredMember(DeclaredInstance):
    """A member of a closed declaration enum with an undeclared default."""

    default: Any = None


@dataclass(frozen=True)
class DeclaredDecision(DeclaredInstance):
    """A declaration where None is a decision, such as "inject no context"."""

    written_when_default: ClassVar[bool] = True


@dataclass(frozen=True)
class DeclaredSubclass(DeclaredInstance):
    """A class from one nominal family."""

    def accepts(self, value: object) -> bool:
        return isinstance(value, type) and issubclass(value, self.resolved_kind())

    def description(self) -> str:
        return f"a {self.resolved_kind().__name__} class"


class DeclaredCallable(DeclaredValue):
    def accepts(self, value: object) -> bool:
        return callable(value)

    def description(self) -> str:
        return "callable"


class DeclaredRawFunction(DeclaredValue):
    """A raw processing callable or its transport reference."""

    def accepts(self, value: object) -> bool:
        return callable(value) or _is_function_reference(value)

    def description(self) -> str:
        return "callable or FunctionReference"


class DeclaredTuple(DeclaredValue):
    """A tuple declaration whose members are validated together."""

    default: ClassVar[tuple] = ()

    def accepts(self, value: object) -> bool:
        return isinstance(value, tuple)

    def description(self) -> str:
        return "a tuple"


class DeclaredNames(DeclaredTuple):
    """Unique non-empty parameter names."""

    def normalize(self, value: Any, *, owner: str) -> Any:
        return _unique_parameter_names(value, owner=owner)


class DeclaredAxisRoles(DeclaredTuple):
    def normalize(self, value: Any, *, owner: str) -> Any:
        if not all(isinstance(role, type) and issubclass(role, AxisRole) for role in value):
            raise TypeError(f"{owner} must be a tuple of axis roles, got {value!r}.")
        if len(value) != len(set(value)):
            raise TypeError(f"{owner} must contain unique roles.")
        return value


class DeclaredRuntimeParameters(DeclaredTuple):
    def normalize(self, value: Any, *, owner: str) -> Any:
        return RuntimeParameterDeclarationABC.require_declaration_types(
            value, boundary=owner,
        )


class DeclaredReturnSlots(DeclaredTuple):
    """Positions in the output ABI; checked against the outputs by the contract."""

    def normalize(self, value: Any, *, owner: str) -> Any:
        if not all(
            isinstance(position, int) and not isinstance(position, bool) and position >= 0
            for position in value
        ):
            raise TypeError(f"{owner} must contain non-negative slot positions.")
        return value


class DeclaredArtifactSpecs(DeclaredValue):
    """An ordered ArtifactSpec declaration."""

    default: ClassVar[ArtifactSpecCollection] = ArtifactSpecCollection(())

    def accepts(self, value: object) -> bool:
        return isinstance(value, (tuple, ArtifactSpecCollection))

    def description(self) -> str:
        return "an ordered ArtifactSpec tuple"

    def normalize(self, value: Any, *, owner: str) -> Any:
        for spec in value:
            if not isinstance(spec, ArtifactSpec):
                raise TypeError(
                    f"{owner} must contain ArtifactSpec values, got {type(spec).__name__}."
                )
        return value if isinstance(value, ArtifactSpecCollection) else ArtifactSpecCollection(value)


_DECLARATION_FIELD = "openhcs_callable_declaration"


def declared(attribute: str, kind: DeclaredValue) -> Any:
    """Declare one field together with its callable-namespace key and value kind."""
    return dataclasses.field(
        default=kind.default, metadata={_DECLARATION_FIELD: (attribute, kind)},
    )


@cache
def _declared_fields(cls: type) -> tuple[tuple[str, str, DeclaredValue], ...]:
    return tuple(
        (declaration.name, *declaration.metadata[_DECLARATION_FIELD])
        for declaration in fields(cls)
        if _DECLARATION_FIELD in declaration.metadata
    )


def _runtime_adapter_spec_type() -> type:
    from openhcs.core.runtime_adapters import RuntimeAdapterSpec

    return RuntimeAdapterSpec


def _request_binding_type() -> type:
    return CallableRequestBinding


@dataclass(frozen=True, slots=True, kw_only=True)
class CallableDeclaration:
    """What a processing callable declares to the compiler.

    Each field names its callable-namespace key and value kind once; the
    namespace codec (``from_namespace``/``as_namespace``) and validation are
    derived from those field declarations.
    """

    input_memory_type: str | None = declared(
        MemoryContractAttribute.INPUT.value, DeclaredInstance(str)
    )
    output_memory_type: str | None = declared(
        MemoryContractAttribute.OUTPUT.value, DeclaredInstance(str)
    )
    execution_memory_type: str | None = declared(
        MemoryContractAttribute.EXECUTION.value, DeclaredInstance(str)
    )
    artifact_inputs: ArtifactSpecCollection = declared(
        FunctionContractAttribute.artifact_inputs, DeclaredArtifactSpecs()
    )
    artifact_parameters: tuple[str, ...] = declared(
        FunctionContractAttribute.artifact_input_parameter_names, DeclaredNames()
    )
    artifact_outputs: ArtifactSpecCollection = declared(
        FunctionContractAttribute.artifact_outputs, DeclaredArtifactSpecs()
    )
    repeated_return_slots: tuple[int, ...] = declared(
        FunctionContractAttribute.repeated_return_slots, DeclaredReturnSlots()
    )
    runtime_bound_parameter_types: tuple[type[RuntimeParameterDeclarationABC], ...] = declared(
        FunctionContractAttribute.runtime_bound_parameters, DeclaredRuntimeParameters()
    )
    required_axis_roles: tuple[type[AxisRole], ...] = declared(
        FunctionContractAttribute.required_axis_roles, DeclaredAxisRoles()
    )
    bound_stack_requirement: VariableComponentStackRequirement | None = declared(
        FunctionContractAttribute.variable_component_stack_requirement,
        DeclaredInstance(VariableComponentStackRequirement),
    )
    allowed_group_by_roles: tuple[type[AxisRole], ...] = declared(
        FunctionContractAttribute.allowed_group_by_roles, DeclaredAxisRoles()
    )
    runtime_adapter: RuntimeAdapterSpec | None = declared(
        FunctionContractAttribute.runtime_adapter, DeclaredInstance(_runtime_adapter_spec_type)
    )
    runtime_context_parameter: str | None = declared(
        FunctionContractAttribute.runtime_context_parameter, DeclaredDecision(str)
    )
    execution_scope: FunctionStepExecutionScope = declared(
        FunctionContractAttribute.execution_scope,
        DeclaredMember(FunctionStepExecutionScope, default=FunctionStepExecutionScope.AXIS),
    )
    processing_contract: type[ProcessingContract] | None = declared(
        FunctionContractAttribute.processing_contract,
        DeclaredSubclass(lambda: _processing_contract_family()),
    )
    raw_processing_function: Callable[..., object] | FunctionReference | None = declared(
        FunctionContractAttribute.raw_processing_function, DeclaredRawFunction()
    )
    runtime_image_execution_mode: type[ImagePayloadExecutionMode] | None = declared(
        FunctionContractAttribute.runtime_image_execution_mode,
        DeclaredSubclass(ImagePayloadExecutionMode),
    )
    image_payload_consumption: ImagePayloadConsumption = declared(
        FunctionContractAttribute.image_payload_consumption,
        DeclaredMember(ImagePayloadConsumption, default=ImagePayloadConsumption.NATURAL),
    )
    request_binding: CallableRequestBinding | None = declared(
        FunctionContractAttribute.callable_request_binding,
        DeclaredInstance(_request_binding_type),
    )
    prepared_canonical_signature: inspect.Signature | None = declared(
        FunctionContractAttribute.canonical_signature, DeclaredSignature()
    )
    prepared_runtime_signature: inspect.Signature | None = declared(
        FunctionContractAttribute.raw_runtime_signature, DeclaredSignature()
    )
    payload_axis_requirement: PayloadAxisRequirement | None = declared(
        FunctionContractAttribute.payload_axis_requirement,
        DeclaredInstance(PayloadAxisRequirement),
    )
    payload_axis_transition: PayloadAxisTransition | None = declared(
        FunctionContractAttribute.payload_axis_transition,
        DeclaredInstance(PayloadAxisTransition),
    )

    def __post_init__(self) -> None:
        """Validate every declared field through its declared kind."""
        owner = type(self).__name__
        for name, _attribute, kind in _declared_fields(type(self)):
            value = getattr(self, name)
            if value is not kind.default:
                object.__setattr__(
                    self, name, kind.read(value, owner=f"{owner}.{name}"),
                )
        spec_parameter_names = _artifact_input_parameter_names(self.artifact_inputs)
        if self.artifact_parameters and not (
            frozenset(spec_parameter_names) <= frozenset(self.artifact_parameters)
        ):
            raise ValueError(
                "Callable artifact-fed parameter declarations disagree: "
                f"declared parameters {self.artifact_parameters!r}, "
                f"ArtifactSpec.parameter_name parameters {spec_parameter_names!r}."
            )

    @classmethod
    def from_namespace(cls, namespace: CallableNamespace, owner: str) -> "CallableDeclaration":
        """Read every declared field from a callable namespace."""
        return cls(**{
            name: kind.read(namespace.get(attribute), owner=f"{owner!r}.{attribute}")
            for name, attribute, kind in _declared_fields(cls)
        })

    def bound_to_callable(
        self, func: Callable[..., object], *, context_declared: bool,
    ) -> "CallableDeclaration":
        """Resolve what the callable's signature decides for this declaration."""
        signature = self.callable_signature(func)
        if self.runtime_adapter is not None:
            self.runtime_adapter.validate_callable_signature(func)
        stack_requirement = self.variable_component_stack_requirement
        return dataclasses.replace(
            self,
            artifact_inputs=_artifact_inputs_bound_to_signature(
                self.artifact_inputs, signature,
            ),
            artifact_parameters=(
                *(name for name in signature.parameters if name in self.artifact_parameters),
                *(name for name in self.artifact_parameters
                  if name not in signature.parameters),
            ),
            runtime_context_parameter=(
                self.runtime_context_parameter
                if context_declared
                else _signature_context_parameter(signature)
            ),
            # Signature defaults are captured before the callable becomes a reference.
            bound_stack_requirement=(
                None if stack_requirement is None
                else stack_requirement.bind_to_callable(func)
            ),
        )

    def field_values(self) -> dict[str, object]:
        """Return the declared fields by name."""
        return {
            name: getattr(self, name)
            for name, _attribute, _kind in _declared_fields(CallableDeclaration)
        }

    def as_namespace(self) -> dict[str, object]:
        """Write every field that differs from its undeclared default."""
        return {
            attribute: value
            for name, attribute, kind in _declared_fields(CallableDeclaration)
            for value in (getattr(self, name),)
            if value != kind.default or kind.written_when_default
        }

    @property
    def artifact_input_parameter_names(self) -> tuple[str, ...]:
        """Parameters fed by artifacts: the declared names, else the specs' names."""
        return self.artifact_parameters or _artifact_input_parameter_names(
            self.artifact_inputs
        )

    @property
    def variable_component_stack_requirement(self) -> VariableComponentStackRequirement | None:
        """The bound declared requirement, else the processing contract's."""
        if self.bound_stack_requirement is not None:
            return self.bound_stack_requirement
        if self.processing_contract is None:
            return None
        return self.processing_contract.variable_component_stack_requirement()

    @property
    def runtime_bound_parameter_names(self) -> tuple[str, ...]:
        """Declared parameters supplied by runtime execution infrastructure."""
        return tuple(
            parameter_type.require_parameter_name()
            for parameter_type in self.runtime_bound_parameter_types
        )

    @property
    def artifact_output_policy(self) -> type[ArtifactOutputPolicy]:
        """Project recording ownership from this callable's adapter declaration."""
        adapter = self.runtime_adapter
        if adapter is None:
            return NativeReturnArtifactOutputPolicy
        return adapter.artifact_output_policy

    @property
    def declared_memory_types(self) -> frozenset[MemoryType]:
        """Return every array framework declared by this callable."""
        return frozenset(
            MemoryType(declaration)
            for declaration in (
                self.input_memory_type,
                self.output_memory_type,
                self.execution_memory_type,
            )
            if declaration is not None
        )

    @staticmethod
    def prepared_callable_signature(func: Callable[..., object]) -> inspect.Signature | None:
        """Admit an owned snapshot only for its exact semantic callable boundary."""
        raw = getattr(func, FunctionContractAttribute.raw_processing_function, None)
        if raw is not None and raw is not func:
            return None
        signature = getattr(func, FunctionContractAttribute.canonical_signature, None)
        if signature is not None and not isinstance(signature, inspect.Signature):
            raise TypeError("Prepared callable signature must be an inspect.Signature or None.")
        return signature

    @classmethod
    def callable_signature(cls, func: Callable[..., object]) -> inspect.Signature:
        """Read the prepared exact ABI; unprepared wrapper/authoring views stay live."""
        signature = cls.prepared_callable_signature(func)
        return inspect.signature(func) if signature is None else signature

    @staticmethod
    def primary_input_name(parameters: Mapping[str, inspect.Parameter]) -> str | None:
        for parameter in parameters.values():
            if parameter.kind in (
                inspect.Parameter.POSITIONAL_ONLY,
                inspect.Parameter.POSITIONAL_OR_KEYWORD,
            ):
                return parameter.name
        return None

    def publish_signatures(self, namespace: MutableMapping[str, Any]) -> None:
        """Replace the namespace pair as one library preparation epoch."""
        namespace[FunctionContractAttribute.canonical_signature] = (
            self.prepared_canonical_signature
        )
        namespace.pop(FunctionContractAttribute.raw_runtime_signature, None)
        if self.prepared_runtime_signature is not None:
            namespace[FunctionContractAttribute.raw_runtime_signature] = (
                self.prepared_runtime_signature
            )


@dataclass(frozen=True, slots=True, kw_only=True)
class CallableContract(CallableDeclaration, ArtifactPlanKeySelector):
    """A callable's declaration bound to the callable it was read from.

    The declaration fields are inherited; this class adds the callable
    identity and what invoking it needs: the runtime callable, the semantic
    signature, kwarg validation and the positional return ABI.
    """

    func: Callable[..., object] | "FunctionReference"
    function_name: str
    module_name: str | None
    runtime_batch_executors: Mapping[RuntimeBatchExecutionDomain, Callable] | None = (
        None
    )

    canonical_return_output_specs: ArtifactSpecCollection = dataclasses.field(
        init=False,
        repr=False,
        compare=False,
    )
    trailing_return_output_specs: ArtifactSpecCollection = dataclasses.field(
        init=False,
        repr=False,
        compare=False,
    )
    _return_specs_by_ref: Mapping[ArtifactSpecRef, ArtifactSpec] = dataclasses.field(
        init=False,
        repr=False,
        compare=False,
    )
    canonical_return_output_refs: tuple[ArtifactSpecRef, ...] = dataclasses.field(
        init=False,
        repr=False,
        compare=False,
    )
    _trailing_return_output_refs: tuple[ArtifactSpecRef, ...] = dataclasses.field(
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        """Capture the declared positional ABI once, before any returned values.

        A ref may fill a second return slot only when the declaration names
        that slot in ``repeated_return_slots``; any other repeat is rejected.
        """
        CallableDeclaration.__post_init__(self)
        outputs = self.artifact_outputs
        repeated_slots = frozenset(self.repeated_return_slots)
        by_ref: dict[ArtifactSpecRef, ArtifactSpec] = {}
        for position, spec in enumerate(outputs):
            ref = spec.ref()
            if position in repeated_slots:
                if by_ref.get(ref) != spec:
                    raise ValueError(
                        f"Callable return slot {position} is declared as a repeat, "
                        f"but no earlier slot declares {spec!r}."
                    )
                continue
            if ref in by_ref:
                raise ValueError(
                    f"Callable output ABI contains duplicate artifact ref {ref!r}."
                )
            by_ref[ref] = spec
        if any(position >= len(outputs) for position in repeated_slots):
            raise ValueError(
                f"Callable repeated return slots {self.repeated_return_slots!r} "
                f"exceed its {len(outputs)} declared output slot(s)."
            )
        canonical_count = 0
        if self.execution_scope is FunctionStepExecutionScope.PLATE:
            canonical_count = min(1, len(outputs))
        elif outputs and outputs[0].participates_in_main_flow:
            canonical_count = 1
            if outputs[0].artifact_type is ImageArtifactType:
                for spec in outputs[1:]:
                    if (
                        not spec.participates_in_main_flow
                        or spec.artifact_type is not ImageArtifactType
                    ):
                        break
                    canonical_count += 1
        refs = tuple(spec.ref() for spec in outputs)
        object.__setattr__(
            self,
            "canonical_return_output_specs",
            ArtifactSpecCollection(outputs[:canonical_count]),
        )
        object.__setattr__(
            self,
            "trailing_return_output_specs",
            ArtifactSpecCollection(outputs[canonical_count:]),
        )
        object.__setattr__(
            self,
            "_return_specs_by_ref",
            MappingProxyType(by_ref),
        )
        object.__setattr__(
            self,
            "canonical_return_output_refs",
            refs[:canonical_count],
        )
        object.__setattr__(
            self,
            "_trailing_return_output_refs",
            refs[canonical_count:],
        )

    def __reduce__(
        self,
    ) -> tuple[Callable[..., "CallableContract"], tuple[Any, ...]]:
        """Serialize immutable mapping-backed executors across worker queues."""
        executors = (
            None if self.runtime_batch_executors is None
            else dict(self.runtime_batch_executors)
        )
        return (
            _rebuild_callable_contract,
            (type(self), self.field_values(), self.func, self.function_name,
             self.module_name, executors),
        )

    @classmethod
    def from_callable(
        cls,
        func: Callable[..., object] | "FunctionReference",
    ) -> "CallableContract":
        """Build a contract from callable attributes once at compiler boundary."""
        from openhcs.core.runtime_batch_contracts import RuntimeBatchCallableFamily

        projection = CallableProjection.from_callable(func)
        declaration = CallableDeclaration.from_namespace(
            projection.namespace, projection.name,
        )
        if callable(projection.func):
            declaration = declaration.bound_to_callable(
                projection.func,
                context_declared=(
                    FunctionContractAttribute.runtime_context_parameter
                    in projection.namespace
                ),
            )
        return cls(
            **declaration.field_values(),
            func=func,
            function_name=projection.name,
            module_name=projection.module_name,
            runtime_batch_executors=RuntimeBatchCallableFamily(
                func=func,
                raw_processing_function=declaration.raw_processing_function,
            ).executors(),
        )

    @property
    def declaration(self) -> CallableDeclaration:
        """The declaration alone, without the callable it is bound to."""
        return CallableDeclaration(**self.field_values())

    @property
    def main_flow_outputs(self) -> ArtifactSpecCollection:
        """Return declared outputs eligible for the canonical image flow."""

        return ArtifactSpecCollection(
            spec for spec in self.artifact_outputs if spec.participates_in_main_flow
        )

    def contextualize_returned_canonical_output(
        self,
        returned_output: Any,
        *,
        plane_projection: RuntimePlaneAxisValueProjection | None = None,
    ) -> Any:
        """Attach the compiled canonical ABI to one exact returned image axis."""

        from openhcs.core.aligned_image_payload import (
            AlignedImageSliceContext,
            AlignedImageStack,
            pack_aligned_image_outputs,
        )
        from openhcs.core.runtime_image_values import owned_runtime_value
        from openhcs.core.runtime_output_matching import split_runtime_output
        from openhcs.core.runtime_slice_projection import (
            RuntimeSliceProjection,
            RuntimeSliceProjectionDeclarationError,
        )

        canonical_specs = self.canonical_return_output_specs.specs
        if len(canonical_specs) <= 1:
            return returned_output
        canonical_output, trailing_outputs = split_runtime_output(returned_output)
        canonical_output = owned_runtime_value(canonical_output)
        if isinstance(canonical_output, AlignedImageStack):
            if canonical_output.slice_contexts:
                return returned_output
            output_values = canonical_output.slices
        else:
            projection = plane_projection
            function_name = self.function_name
            if projection is None:
                raise RuntimeSliceProjectionDeclarationError(
                    f"{function_name} declares {len(canonical_specs)} canonical "
                    "outputs but returned a non-aligned payload without a "
                    "compiled plane projection."
                )
            if projection.selects_one_plane:
                raise RuntimeSliceProjectionDeclarationError(
                    f"{function_name} declares {len(canonical_specs)} canonical "
                    "outputs after the compiled plane projection already selected "
                    f"plane {projection.plane_index}."
                )
            if projection.axis_size != len(canonical_specs):
                raise ValueError(
                    f"{function_name} declares {len(canonical_specs)} canonical "
                    "outputs but its compiled plane projection declares "
                    f"{projection.axis_size} value(s)."
                )
            output_axis = canonical_output.metadata.plane_axis
            if output_axis is not projection.axis:
                raise RuntimeSliceProjectionDeclarationError(
                    f"{function_name} declares {len(canonical_specs)} canonical "
                    "outputs but its returned payload does not declare the "
                    f"compiled {projection.axis.name!r} plane axis; got "
                    f"{output_axis!r}."
                )
            output_values = tuple(
                RuntimeSliceProjection.value_for_slice(
                    canonical_output,
                    projection.selected_plane(output_index),
                )
                for output_index in range(projection.axis_size)
            )
        if len(output_values) != len(canonical_specs):
            raise ValueError(
                f"{self.function_name} returned {len(output_values)} "
                "canonical output value(s) for "
                f"{len(canonical_specs)} compiled output spec(s)."
            )
        contextualized_output = pack_aligned_image_outputs(
            output_values,
            slice_contexts=AlignedImageSliceContext.main_flow_for_artifact_specs(
                canonical_specs
            ),
        )
        return (
            (contextualized_output, *trailing_outputs)
            if trailing_outputs
            else contextualized_output
        )

    def resolve_returned_output(
        self, returned_output: Any
    ) -> dict[ArtifactSpecRef, Any]:
        """Resolve every output in the callable ABI."""

        from openhcs.core.aligned_image_payload import AlignedImageStack
        from openhcs.core.runtime_output_matching import split_runtime_output

        canonical_output, trailing_values = split_runtime_output(returned_output)
        trailing_specs = self.trailing_return_output_specs.specs
        if len(trailing_values) != len(trailing_specs):
            raise ValueError(
                "Runtime callable trailing return count does not match its "
                f"declared trailing output slots: {len(trailing_values)} != "
                f"{len(trailing_specs)}."
            )
        resolved: dict[ArtifactSpecRef, Any] = {}
        canonical_specs = self.canonical_return_output_specs.specs
        if len(canonical_specs) == 1:
            resolved[self.canonical_return_output_refs[0]] = canonical_output
        elif canonical_specs:
            if not isinstance(canonical_output, AlignedImageStack):
                raise TypeError(
                    "Multiple canonical output specs require an AlignedImageStack with "
                    "one exact named slice context per output."
                )
            resolved.update(
                canonical_output.output_values_for_artifact_specs(canonical_specs)
            )
        # A declared repeated slot refills its output; the first slot's value is kept.
        for ref, value in zip(
            self._trailing_return_output_refs, trailing_values, strict=True,
        ):
            resolved.setdefault(ref, value)
        return resolved

    def resolve_returned_plan_values(
        self,
        returned_output: Any,
        selected_output_plans: tuple[ArtifactOutputPlan, ...],
    ) -> tuple[
        dict[ArtifactSpecRef, Any],
        tuple[RuntimeMatchedOutput, ...],
    ]:
        """Resolve the complete ABI and bind exact selected runtime plans once."""

        returned_values = self.resolve_returned_output(returned_output)
        specs_by_ref = self._return_specs_by_ref
        selected_refs: set[ArtifactSpecRef] = set()
        matched_outputs: list[RuntimeMatchedOutput] = []
        for plan in selected_output_plans:
            if not isinstance(plan, ArtifactOutputPlan):
                raise TypeError(
                    "Selected runtime outputs must be ArtifactOutputPlan values, "
                    f"got {type(plan).__name__}."
                )
            ref = plan.ref()
            if ref in selected_refs:
                raise ValueError(
                    f"Selected runtime output plans contain duplicate ref {ref!r}."
                )
            selected_refs.add(ref)
            spec = specs_by_ref.get(ref)
            if spec is None:
                raise ValueError(
                    f"Selected output plan {ref!r} is not declared by the callable ABI."
                )
            matched_outputs.append((plan, spec, returned_values[ref]))
        return returned_values, tuple(matched_outputs)

    @property
    def output_group_scope_sources(self) -> tuple[ArtifactSpecRef, ...]:
        """Return exact input identities owning declared output group scopes."""

        return tuple(
            dict.fromkeys(
                source_ref
                for output_spec in self.artifact_outputs
                for source_ref in output_spec.group_scope_sources()
            )
        )

    @property
    def group_scope_inputs(self) -> ArtifactSpecCollection:
        """Return inputs whose declared relations own this invocation's group scope."""

        input_specs = self.artifact_inputs
        source_refs = self.output_group_scope_sources
        if not source_refs:
            return input_specs
        sources = ArtifactSpecCollection(
            source_spec
            for source_ref in source_refs
            for source_spec in (input_specs.by_ref(source_ref),)
            if source_spec is not None
        )
        missing = tuple(
            source_ref
            for source_ref in source_refs
            if input_specs.by_ref(source_ref) is None
        )
        if missing:
            raise ValueError(
                f"Callable {self.function_name!r} output group-scope relations "
                f"reference undeclared inputs {missing!r}."
            )
        return sources

    @property
    def lifecycle_anchor_owner_inputs(self) -> ArtifactSpecCollection:
        """Inputs whose stored values, not main-flow anchors, drive invocation.

        A callable fed main-flow pixels runs once per main-flow anchor; its
        undeclared artifact inputs are context for that anchor. A declared
        group-lineage relation still names its owning inputs.
        """
        if self.main_flow_supplies_primary_image and not self.output_group_scope_sources:
            return ArtifactSpecCollection(())
        return self.group_scope_inputs

    @property
    def main_flow_supplies_primary_image(self) -> bool:
        """Whether the runtime passes main-flow pixels as the primary argument.

        Such a callable runs once per main-flow cohort.
        """
        adapter = self.runtime_adapter
        return self.accepts_implicit_main_flow_input and not (
            adapter is not None and adapter.manages_artifact_inputs
        )

    def preserves_input_main_flow(self) -> bool:
        """Return whether declared artifact outputs leave main flow unchanged."""

        return self.artifact_output_policy.preserves_input_main_flow(self)

    @property
    def invocation_domain_inputs(self) -> ArtifactSpecCollection:
        """Derive carrier inputs through the declared adapter's nominal owner."""
        adapter = self.runtime_adapter
        return (
            self.group_scope_inputs
            if adapter is None
            else adapter.invocation_domain_inputs(self)
        )

    @property
    def config_bound_parameters(self) -> tuple[inspect.Parameter, ...]:
        """PipelineConfig-owned parameters declared by the callable signature."""

        from openhcs.core.config import runtime_config_parameter

        signature = self.canonical_signature
        return tuple(
            normalized
            for parameter in signature.parameters.values()
            for normalized in (runtime_config_parameter(parameter),)
            if normalized is not None
        )

    @property
    def config_bound_parameter_names(self) -> tuple[str, ...]:
        """Names of config values supplied by the compiled step scope."""

        return tuple(parameter.name for parameter in self.config_bound_parameters)

    @property
    def overridable_runtime_parameter_names(self) -> frozenset[str]:
        """Runtime settings that authoring may override on a function occurrence.

        Config bindings consume explicit values before public-ABI validation;
        semantic controls remain executable kwargs. Neither is an injected
        runtime object, even when the default form hides its parameter.
        """
        return frozenset(self.config_bound_parameter_names).union(
            parameter.require_parameter_name()
            for parameter in self.runtime_bound_parameter_types
            if parameter.is_semantic_control
        )

    @property
    def runtime_owned_parameter_names(self) -> frozenset[str]:
        """Parameters supplied by compiled artifact, config, or runtime state."""

        names = {
            *self.artifact_input_parameter_names,
            *self.runtime_bound_parameter_names,
            *self.config_bound_parameter_names,
        }
        if self.runtime_context_parameter is not None:
            names.add(self.runtime_context_parameter)
        if self.runtime_adapter is not None:
            names.add(self.runtime_adapter.require_parameter_name())
        return frozenset(names)

    @property
    def declared_path_parameters(self) -> Mapping[str, "DatasetPathDeclaration"]:
        """Plate-relative path declarations owned by the semantic ABI."""
        return CallableSignature.from_signature(
            self.canonical_signature
        ).declared_path_parameters

    def declared_path_values(
        self,
        kwargs: Mapping[str, object],
    ) -> Mapping[str, tuple["DatasetPathDeclaration", object]]:
        """Return authored or signature-default values for declared paths."""

        signature = self.canonical_signature
        values: dict[str, tuple["DatasetPathDeclaration", object]] = {}
        for parameter_name, declaration in self.declared_path_parameters.items():
            value = kwargs.get(parameter_name, signature.parameters[parameter_name].default)
            if parameter_name not in kwargs and value is inspect.Parameter.empty:
                continue
            if value is not None:
                values[parameter_name] = (declaration, value)
        return MappingProxyType(values)

    def resolve_declared_paths(
        self,
        kwargs: Mapping[str, object],
        resolver: "CompilationPathResolver",
    ) -> dict[str, object]:
        """Resolve only explicitly declared public path arguments."""

        resolved = dict(kwargs)
        for parameter_name, (declaration, value) in self.declared_path_values(
            kwargs
        ).items():
            if not isinstance(value, (str, Path)):
                raise TypeError(
                    f"Callable {self.function_name!r} path parameter "
                    f"{parameter_name!r} requires str or Path, got "
                    f"{type(value).__name__}."
                )
            resolved[parameter_name] = resolver.resolve(
                value,
                declaration,
                owner=f"callable {self.function_name}.{parameter_name}",
            )
        return resolved

    def require_processing_contract(self) -> "type[ProcessingContract]":
        """Return the declared processing contract or fail at the contract boundary."""
        processing_contract = self.processing_contract
        if processing_contract is None:
            raise TypeError(
                f"Callable {self.function_name!r} must declare a ProcessingContract."
            )
        return processing_contract

    def runtime_main_flow_call_argument(self, source_payload: Any) -> Any:
        """Project this callable's ABI without discarding an adapter's context."""
        if self.runtime_adapter is not None:
            return source_payload
        return self.raw_main_flow_call_argument(source_payload)

    def raw_main_flow_call_argument(self, source_payload: Any) -> Any:
        """Pass the main-flow value as the primary parameter declares it.

        A bare array enters the payload family here; a parameter that does not
        declare the payload's type receives the payload's array.
        """
        from openhcs.core.runtime_image_values import ImagePayload, owned_runtime_value

        signature = self.canonical_signature
        primary_name = self.primary_input_name(signature.parameters)
        annotation = (
            None if primary_name is None else signature.parameters[primary_name].annotation
        )
        if (
            annotation is inspect.Parameter.empty
            and self.image_payload_consumption is ImagePayloadConsumption.COMPOSED
        ):
            return source_payload
        source_payload = owned_runtime_value(source_payload)
        return source_payload if any(
            isinstance(source_payload, argument_type)
            for argument_type in _nominal_argument_types(annotation)
        ) or not isinstance(source_payload, ImagePayload) else source_payload.data

    def main_flow_call_argument(self, source_payload: Any) -> Any:
        """Let the processing declaration retain context needed before raw calls."""
        return self.require_processing_contract().main_flow_call_argument(
            self, source_payload,
        )

    @property
    def collapses_input_plane_axis(self) -> bool:
        """Whether the nominal processing declaration reduces the stack axis."""
        return self.processing_contract is not None and (
            self.require_processing_contract().collapses_input_plane_axis
        )

    @property
    def artifact_specs(self) -> ArtifactSpecCollection:
        """All artifact specs declared by this callable, each output once."""
        repeated_slots = frozenset(self.repeated_return_slots)
        return ArtifactSpecCollection(
            (
                *self.artifact_inputs,
                *(
                    spec
                    for position, spec in enumerate(self.artifact_outputs)
                    if position not in repeated_slots
                ),
            )
        )

    @property
    def primary_input_parameter_name(self) -> str | None:
        """FunctionStep input payload parameter declared by callable signature."""
        signature = self.canonical_signature
        return self.primary_input_name(signature.parameters)

    @property
    def accepts_implicit_main_flow_input(self) -> bool:
        """Whether the callable accepts its primary input from unnamed main flow."""

        primary_input = self.primary_input_parameter_name
        return (
            primary_input is not None
            and primary_input not in self.runtime_owned_parameter_names
        )

    def runtime_batch_executor(
        self,
        domain: RuntimeBatchExecutionDomain,
    ) -> Callable | None:
        """Return the declared runtime batch executor for one domain."""
        if self.runtime_batch_executors is None:
            return None
        return self.runtime_batch_executors.get(domain)

    def require_memory_types(
        self, *, callable_label: str | None = None
    ) -> tuple[str, str]:
        """Admit both declared memory domains before runtime conversion."""
        if self.input_memory_type is None or self.output_memory_type is None:
            raise ValueError(
                f"Callable {self.function_name!r} is missing memory types."
            )
        valid_types = frozenset(memory_type.value for memory_type in MemoryType)
        if (
            self.input_memory_type not in valid_types
            or self.output_memory_type not in valid_types
        ):
            raise ValueError(
                f"Function '{callable_label or self.function_name}' has invalid "
                f"memory types: {self.input_memory_type}/{self.output_memory_type}. "
                f"Valid: {', '.join(sorted(valid_types))}"
            )
        return self.input_memory_type, self.output_memory_type

    def require_execution_memory_type(
        self, *, step_name: str | None = None
    ) -> MemoryType | None:
        """Admit the declared execution framework with its callable context."""
        declaration = self.execution_memory_type
        if declaration is None:
            return None
        valid_types = frozenset(memory_type.value for memory_type in MemoryType)
        if declaration not in valid_types:
            step_context = "" if step_name is None else f" in step {step_name!r}"
            raise ValueError(
                f"Callable {self.function_name!r}{step_context} "
                f"declares invalid execution memory type {declaration!r}; "
                f"valid memory types are {', '.join(sorted(valid_types))}."
            )
        return MemoryType(declaration)

    def resolve_runtime_callable(self) -> Callable[..., object]:
        """Return the executable callable for this contract."""
        cache = CallableContractRuntimeCache.process_cache()
        with CallableContractRuntimeCache.resolution_lock:
            cached = cache.get_bound(self)
        if cached is not None:
            return cached
        resolved = _resolve_declared_callable(self.func)
        runtime_adapter = self.runtime_adapter
        if runtime_adapter is not None:
            resolved = runtime_adapter.executable_callable(resolved, self)
        with CallableContractRuntimeCache.resolution_lock:
            cache.put_bound(self, resolved)
        return resolved

    def resolve_canonical_raw_callable(self) -> Callable[..., object]:
        """Return the declaration-owned callable whose signature defines behavior."""
        declared = self.raw_processing_function
        return _resolve_declared_callable(self.func if declared is None else declared)

    def canonical_raw_import_identity(self) -> CallableImportIdentity:
        """Return the complete import identity of the canonical raw callable."""

        return CallableImportIdentity.from_callable(
            self.resolve_canonical_raw_callable()
        )

    def resolve_raw_runtime_callable(self) -> Callable[..., object]:
        """Remove runtime wrappers without crossing a semantic request binding."""
        canonical = self.resolve_canonical_raw_callable()
        if self.request_binding is None:
            return inspect.unwrap(canonical)

        binding_key = FunctionContractAttribute.callable_request_binding

        def is_request_boundary(candidate: Callable[..., object]) -> bool:
            namespace = _callable_namespace(candidate)
            if binding_key not in namespace:
                return False
            wrapped = namespace.get("__wrapped__")
            return not callable(wrapped) or binding_key not in _callable_namespace(
                wrapped
            )

        resolved = inspect.unwrap(canonical, stop=is_request_boundary)
        if binding_key not in _callable_namespace(resolved):
            raise RuntimeError(
                f"Callable {self.function_name!r} declares a request binding, but "
                "its canonical raw callable has no request-binding boundary."
            )
        return resolved

    def resolve_signature(self, raw_callable: Callable[..., object]) -> inspect.Signature:
        """Resolve the semantic ABI once after declaration preparation."""
        signature = inspect.signature(raw_callable)
        annotations = (
            self.request_binding.public_annotations_dict
            if self.request_binding is not None
            else get_type_hints(raw_callable, include_extras=True)
        )
        return signature.replace(
            parameters=tuple(
                parameter.replace(annotation=annotations.get(name, parameter.annotation))
                for name, parameter in signature.parameters.items()
            ),
            return_annotation=annotations.get("return", signature.return_annotation),
        )

    @property
    def canonical_parameter_annotations(self) -> Mapping[str, object]:
        """Derive annotations from the original semantic signature owner."""
        return {
            name: parameter.annotation
            for name, parameter in self.canonical_signature.parameters.items()
        }

    @property
    def canonical_signature(self) -> inspect.Signature:
        """The prepared semantic signature; unprepared authoring resolves it live."""
        if self.prepared_canonical_signature is not None:
            return self.prepared_canonical_signature
        return self.resolve_signature(self.resolve_canonical_raw_callable())

    def with_prepared_signature(self) -> "CallableContract":
        """Snapshot each actual target independently after declaration preparation."""
        canonical = self.resolve_canonical_raw_callable()
        runtime = self.resolve_raw_runtime_callable()
        return dataclasses.replace(
            self,
            prepared_canonical_signature=self.resolve_signature(canonical),
            prepared_runtime_signature=(
                None if runtime is canonical else self.resolve_signature(runtime)
            ),
        )

    @property
    def raw_runtime_signature(self) -> inspect.Signature:
        """The distinct raw execution signature, or the shared canonical one."""
        if self.prepared_runtime_signature is not None:
            return self.prepared_runtime_signature
        if self.prepared_canonical_signature is not None:
            return self.prepared_canonical_signature
        return self.resolve_signature(self.resolve_raw_runtime_callable())

    @classmethod
    def from_prepared_callable(cls, func: Callable[..., object]) -> "CallableContract":
        """Construct a compiled view only after the declaration owner prepares it."""
        return CallableProjection.from_callable(func).prepared_contract()

    def decode_public_kwargs(self, kwargs: Mapping[str, object]) -> dict[str, object]:
        """Descend declared scalar enums at authoring, before source projection."""

        decoded = dict(kwargs)
        for name, annotation in self.canonical_parameter_annotations.items():
            if name not in kwargs or enum_member_type(resolve_annotated(annotation)) is None:
                continue
            value = kwargs[name]
            decoded[name] = value if value is None else coerce_enum_member(annotation, value)
            validate_annotation_value(
                annotation, decoded[name], path=f"{self.function_name}.{name}",
            )
        return decoded

    def validate_public_kwargs(
        self,
        kwargs: Mapping,
        *,
        runtime_loaded_artifact_parameter_names: Iterable[str] = (),
    ) -> tuple[tuple[object, object], ...]:
        """Validate behavior kwargs against the canonical raw callable ABI."""

        if not isinstance(kwargs, Mapping):
            raise TypeError(
                "CallableContract.validate_public_kwargs requires a mapping."
            )
        signature = self.canonical_signature
        runtime_owned_value = object()
        call_kwargs = dict(kwargs)
        runtime_loaded_parameters = frozenset(runtime_loaded_artifact_parameter_names)

        def bind_runtime_owned(parameter_name: str) -> None:
            parameter = signature.parameters.get(parameter_name)
            if parameter is None:
                return
            if parameter_name in call_kwargs and call_kwargs[parameter_name] is not runtime_owned_value:
                raise TypeError(
                    f"Callable {self.function_name!r} public kwargs cannot set "
                    f"runtime-owned parameter {parameter_name!r}."
                )
            if parameter.kind is inspect.Parameter.POSITIONAL_ONLY:
                raise TypeError(
                    f"Callable {self.function_name!r} runtime-owned parameter "
                    f"{parameter_name!r} cannot be positional-only."
                )
            call_kwargs[parameter_name] = runtime_owned_value

        overridable_parameters = self.overridable_runtime_parameter_names
        for parameter_name in (
            *(name for name in self.artifact_input_parameter_names
              if name not in call_kwargs or name in runtime_loaded_parameters),
            self.runtime_context_parameter,
            self.runtime_adapter.require_parameter_name() if self.runtime_adapter is not None else None,
            *(parameter_type.require_parameter_name()
              for parameter_type in self.runtime_bound_parameter_types
              if parameter_type.require_parameter_name() not in overridable_parameters),
            *self.config_bound_parameter_names,
        ):
            if parameter_name is not None:
                bind_runtime_owned(parameter_name)

        primary_input = self.primary_input_parameter_name
        call_args = () if primary_input is None else (runtime_owned_value,)
        try:
            signature.bind(*call_args, **call_kwargs)
        except TypeError as exc:
            raise TypeError(
                f"Callable {self.function_name!r} has invalid public kwargs for "
                f"canonical raw signature {signature}: {exc}"
            ) from exc
        resolved_annotations = self.canonical_parameter_annotations
        for parameter_name, value in kwargs.items():
            annotation = resolved_annotations.get(parameter_name)
            if declared_enum_type(annotation) is None:
                continue
            try:
                validate_annotation_value(
                    annotation,
                    value,
                    path=f"{self.function_name}.{parameter_name}",
                )
            except (TypeError, ValueError) as exc:
                raise TypeError(
                    f"Callable {self.function_name!r} has invalid public value "
                    f"for {parameter_name!r}: {exc}"
                ) from exc
        return tuple(kwargs.items())

    def validate_artifact_input_parameter_bindings(self) -> None:
        """Validate exact artifact occurrences against the normalized callable ABI."""

        from openhcs.core.pipeline.function_contracts import (
            special_input_parameter_accepts_sequence,
        )

        artifact_parameters = {}
        parameters = self.canonical_signature.parameters
        for parameter_name in self.artifact_input_parameter_names:
            parameter = parameters.get(parameter_name)
            if parameter is None:
                raise ValueError(
                    f"Callable {self.function_name!r} does not declare parameter "
                    f"{parameter_name!r}."
                )
            artifact_parameters[parameter_name] = parameter
        specs_by_parameter: dict[str, list[ArtifactSpec]] = {}
        for spec in self.artifact_inputs:
            parameter_name = spec.parameter_name
            if parameter_name is None:
                continue
            if parameter_name not in artifact_parameters:
                raise ValueError(
                    f"Callable {self.function_name!r} artifact input {spec.ref()!r} "
                    f"binds undeclared artifact-fed parameter {parameter_name!r}."
                )
            parameter = artifact_parameters[parameter_name]
            if (
                parameter.annotation is not inspect.Signature.empty
                and spec.artifact_type.runtime_parameter_types()
                and not spec.artifact_type.accepts_parameter_annotation(
                    parameter.annotation
                )
            ):
                raise TypeError(
                    f"Callable {self.function_name!r} parameter "
                    f"{parameter_name!r} does not accept "
                    f"{spec.artifact_type.value} artifact payloads."
                )
            specs_by_parameter.setdefault(parameter_name, []).append(spec)

        for parameter_name, parameter in artifact_parameters.items():
            bound_specs = tuple(specs_by_parameter.get(parameter_name, ()))
            if not bound_specs:
                if parameter.default is inspect.Parameter.empty:
                    raise ValueError(
                        f"Callable {self.function_name!r} artifact-fed parameter "
                        f"{parameter_name!r} has no exact artifact declaration "
                        "binding."
                    )
                continue
            if (
                len(bound_specs) > 1
                and not (
                    self.runtime_adapter is not None
                    and self.runtime_adapter.manages_artifact_inputs
                )
                and not special_input_parameter_accepts_sequence(parameter)
                and any(
                    spec.artifact_type is not ImageArtifactType for spec in bound_specs
                )
            ):
                raise ValueError(
                    f"Callable {self.function_name!r} scalar artifact-fed parameter "
                    f"{parameter_name!r} has multiple exact artifact occurrences "
                    f"{tuple(spec.ref() for spec in bound_specs)!r}."
                )


def _rebuild_callable_contract(
    contract_type: type[CallableContract],
    declaration_values: dict[str, Any],
    func: Callable[..., object] | "FunctionReference",
    function_name: str,
    module_name: str | None,
    executors: dict[object, object] | None,
) -> CallableContract:
    """Rebuild a CallableContract with immutable batch executors."""
    return contract_type(
        **declaration_values,
        func=func,
        function_name=function_name,
        module_name=module_name,
        runtime_batch_executors=(
            None if executors is None else MappingProxyType(executors)
        ),
    )


@dataclass(frozen=True, slots=True)
class CallableRequestBinding:
    """Typed declaration for public kwargs projected into a request record."""

    request_type: type[object]
    request_parameter: str
    public_fields: tuple[str, ...]
    public_defaults: tuple[tuple[str, Any], ...] = ()
    public_annotations: tuple[tuple[str, Any], ...] = ()

    @property
    def public_defaults_dict(self) -> dict[str, Any]:
        """Return request-field defaults as a runtime mapping."""
        return dict(self.public_defaults)

    @property
    def public_annotations_dict(self) -> dict[str, Any]:
        """Return request-field annotations as a runtime mapping."""
        return dict(self.public_annotations)

    @classmethod
    def from_dataclass(
        cls,
        request_type: type[object],
        *,
        request_parameter: str,
        public_fields: tuple[str, ...],
        public_defaults: Mapping[str, Any],
    ) -> "CallableRequestBinding":
        """Build a binding declaration from a request dataclass."""
        _validate_request_public_fields(request_type, public_fields)
        return cls(
            request_type=request_type,
            request_parameter=request_parameter,
            public_fields=public_fields,
            public_defaults=tuple(public_defaults.items()),
            public_annotations=tuple(get_type_hints(request_type).items()),
        )

    def request_from_bound_arguments(
        self,
        bound_arguments: Mapping[str, Any],
    ) -> object:
        """Build the request object from public bound call arguments."""
        defaults = self.public_defaults_dict
        request_kwargs: dict[str, Any] = {}
        missing: list[str] = []
        for field_name in self.public_fields:
            if field_name in bound_arguments:
                request_kwargs[field_name] = bound_arguments[field_name]
            elif field_name in defaults:
                request_kwargs[field_name] = defaults[field_name]
            else:
                missing.append(field_name)
        if missing:
            raise TypeError(
                f"{self.request_type.__name__} request is missing public "
                f"field(s): {', '.join(missing)}."
            )
        return self.request_type(**request_kwargs)

    def implementation_kwargs(
        self,
        bound_arguments: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Return kwargs for the implementation callable."""
        request_fields = set(self.public_fields)
        local_kwargs = {
            name: value
            for name, value in bound_arguments.items()
            if name not in request_fields
        }
        local_kwargs[self.request_parameter] = self.request_from_bound_arguments(
            bound_arguments,
        )
        return local_kwargs


@dataclass(frozen=True, slots=True)
class RequestParameterName:
    """Validated implementation parameter name for callable request binding."""

    value: str

    def __post_init__(self) -> None:
        if not isinstance(self.value, str) or not self.value:
            raise ValueError("request_parameter must be a non-empty string.")


@dataclass(frozen=True, slots=True)
class RequestPublicFieldSelection:
    """Validated public request field selection."""

    request_type: type[object]
    field_names: tuple[str, ...] | None = None

    @property
    def names(self) -> tuple[str, ...]:
        if self.field_names is None:
            return tuple(field.name for field in fields(self.request_type))
        return tuple(self.field_names)


def callable_request(
    request_type: type[object],
    *,
    request_parameter: str = "request",
    public_fields: tuple[str, ...] | None = None,
    public_defaults: Mapping[str, Any] | object | None = None,
) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    """Expose request-record fields as the public callable signature."""
    if not is_dataclass(request_type):
        raise TypeError(
            "callable_request request_type must be a dataclass type, "
            f"got {request_type!r}."
        )
    binding = CallableRequestBinding.from_dataclass(
        request_type=request_type,
        request_parameter=RequestParameterName(request_parameter).value,
        public_fields=RequestPublicFieldSelection(
            request_type=request_type,
            field_names=public_fields,
        ).names,
        public_defaults=_public_defaults_mapping(public_defaults),
    )

    def decorator(func: Callable[..., Any]) -> Callable[..., Any]:
        implementation_signature = inspect.signature(func)
        if request_parameter not in implementation_signature.parameters:
            raise ValueError(
                f"{func.__name__} must declare request parameter {request_parameter!r}."
            )
        public_signature = _request_public_signature(
            func,
            binding,
            implementation_signature,
        )

        @wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            bound = public_signature.bind(*args, **kwargs)
            bound.apply_defaults()
            return func(**binding.implementation_kwargs(bound.arguments))

        wrapper_namespace = _mutable_callable_namespace(wrapper)
        wrapper_namespace.pop(FunctionContractAttribute.canonical_signature, None)
        wrapper_namespace.pop(FunctionContractAttribute.raw_runtime_signature, None)
        wrapper_namespace[FunctionContractAttribute.callable_request_binding] = binding
        wrapper_namespace["__signature__"] = public_signature
        return wrapper

    return decorator


def _public_defaults_mapping(
    public_defaults: Mapping[str, Any] | object | None,
) -> Mapping[str, Any]:
    """Return request public defaults as a mapping."""
    if public_defaults is None:
        return {}
    if isinstance(public_defaults, Mapping):
        return public_defaults
    if is_dataclass(public_defaults) and not isinstance(public_defaults, type):
        return asdict(public_defaults)
    raise TypeError(
        "public_defaults must be a mapping, dataclass instance, or None; "
        f"got {type(public_defaults).__name__}."
    )


def _attach_optional_metadata(
    func: Any,
    *,
    field_name: str,
    value: object,
    kind: type,
) -> None:
    """Validate and attach one optional declaration."""

    if value is None:
        return
    _mutable_callable_namespace(func)[field_name] = DeclaredInstance(kind).read(
        value, owner=field_name,
    )


def attach_callable_contract_metadata(
    func: Any,
    *,
    processing_contract: "type[ProcessingContract] | None" = None,
    raw_processing_function: Any | None = None,
    prepare: Any | None = None,
    runtime_image_execution_mode: type[ImagePayloadExecutionMode] | None = None,
    runtime_bound_parameters: tuple[type[RuntimeParameterDeclarationABC], ...] = (),
    payload_axis_requirement: PayloadAxisRequirement | None = None,
    payload_axis_transition: PayloadAxisTransition | None = None,
) -> None:
    """Attach OpenHCS callable metadata used by compiler/runtime phases."""
    _mutable_callable_namespace(func).pop(FunctionContractAttribute.canonical_signature, None)
    _mutable_callable_namespace(func).pop(FunctionContractAttribute.raw_runtime_signature, None)
    if processing_contract is not None:
        if not (
            isinstance(processing_contract, type)
            and issubclass(processing_contract, _processing_contract_family())
        ):
            raise TypeError(
                "processing_contract must be a ProcessingContract class, "
                f"got {processing_contract!r}."
            )
        # A contract already on the callable (an inner declaration) is kept.
        _mutable_callable_namespace(func).setdefault(
            FunctionContractAttribute.processing_contract, processing_contract
        )
    if raw_processing_function is not None:
        if not callable(raw_processing_function):
            raise TypeError(
                "raw_processing_function must be callable, "
                f"got {type(raw_processing_function).__name__}."
            )
        namespace = _mutable_callable_namespace(func)
        namespace[FunctionContractAttribute.raw_processing_function] = (
            raw_processing_function
        )
        raw_prepare = DeclaredCallable().read(
            _callable_namespace(raw_processing_function).get(
                FunctionContractAttribute.processing_prepare
            ),
            owner="raw_processing_function prepare hook",
        )
        if (
            raw_prepare is not None
            and FunctionContractAttribute.processing_prepare not in namespace
        ):
            namespace[FunctionContractAttribute.processing_prepare] = raw_prepare
    _attach_runtime_bound_parameter_metadata(
        func,
        runtime_bound_parameters,
        source=raw_processing_function,
    )
    if prepare is not None:
        if not callable(prepare):
            raise TypeError(f"prepare must be callable, got {type(prepare).__name__}.")
        _mutable_callable_namespace(func)[
            FunctionContractAttribute.processing_prepare
        ] = prepare
    if runtime_image_execution_mode is not None:
        if not (
            isinstance(runtime_image_execution_mode, type)
            and issubclass(runtime_image_execution_mode, ImagePayloadExecutionMode)
        ):
            raise TypeError(
                "runtime_image_execution_mode must be an ImagePayloadExecutionMode "
                f"class, got {runtime_image_execution_mode!r}."
            )
        _mutable_callable_namespace(func)[
            FunctionContractAttribute.runtime_image_execution_mode
        ] = runtime_image_execution_mode
    _attach_optional_metadata(
        func,
        field_name=FunctionContractAttribute.payload_axis_requirement,
        value=payload_axis_requirement,
        kind=PayloadAxisRequirement,
    )
    _attach_optional_metadata(
        func,
        field_name=FunctionContractAttribute.payload_axis_transition,
        value=payload_axis_transition,
        kind=PayloadAxisTransition,
    )

    _project_runtime_owned_parameter_exclusions(func)


def _project_runtime_owned_parameter_exclusions(func: Any) -> None:
    """Project contract-owned runtime parameters into generic introspection."""

    add_parameter_exclusions(
        func,
        CallableContract.from_callable(func).runtime_owned_parameter_names,
    )


def _processing_contract_family() -> type["ProcessingContract"]:
    from openhcs.core.processing_contracts import ProcessingContract

    return ProcessingContract


def _attach_runtime_bound_parameter_metadata(
    func: Any,
    parameter_types: tuple[type[RuntimeParameterDeclarationABC], ...],
    *,
    source: Any | None,
) -> None:
    """Merge runtime-bound parameter declarations into callable metadata."""
    attribute = FunctionContractAttribute.runtime_bound_parameters
    ordered: list[type[RuntimeParameterDeclarationABC]] = []
    seen_names: set[str] = set()
    for owner in (source, func):
        if owner is None:
            continue
        for parameter_type in vars(owner).get(attribute, ()):
            _append_runtime_parameter_type(parameter_type, ordered, seen_names)
    for parameter_type in parameter_types:
        _append_runtime_parameter_type(parameter_type, ordered, seen_names)
    if ordered:
        _mutable_callable_namespace(func)[attribute] = tuple(ordered)


def _append_runtime_parameter_type(
    parameter_type: object,
    ordered: list[type[RuntimeParameterDeclarationABC]],
    seen_names: set[str],
) -> None:
    declaration = RuntimeParameterDeclarationABC.require_declaration_type(
        parameter_type,
        boundary="runtime_bound_parameters",
    )
    parameter_name = declaration.require_parameter_name()
    if parameter_name in seen_names:
        return
    ordered.append(declaration)
    seen_names.add(parameter_name)


def processing_prepare(*targets: Any) -> Any:
    """Declare a preparation callable for one or more processing callables.

    This keeps preparation binding explicit and colocated with the prepare
    function definition instead of relying on tail-end attribute assignment.
    """
    if not targets:
        raise ValueError("processing_prepare requires at least one target callable.")
    for target in targets:
        if not callable(target):
            raise TypeError(
                "processing_prepare targets must be callable, "
                f"got {type(target).__name__}."
            )

    def decorator(prepare: Any) -> Any:
        if not callable(prepare):
            raise TypeError(
                "processing_prepare can only decorate callables, "
                f"got {type(prepare).__name__}."
            )
        for target in targets:
            attach_processing_prepare(target, prepare)
        return prepare

    return decorator


def attach_processing_prepare(func: Any, prepare: Any) -> None:
    """Attach preparation metadata across a decorated callable family."""
    if not callable(func):
        raise TypeError(
            "attach_processing_prepare target must be callable, "
            f"got {type(func).__name__}."
        )
    if not callable(prepare):
        raise TypeError(
            "attach_processing_prepare prepare must be callable, "
            f"got {type(prepare).__name__}."
        )
    for target in CallableProjection.from_callable(func).prepare_targets():
        namespace = _mutable_callable_namespace(target)
        namespace.pop(FunctionContractAttribute.canonical_signature, None)
        namespace.pop(FunctionContractAttribute.raw_runtime_signature, None)
        namespace[FunctionContractAttribute.processing_prepare] = prepare


def runtime_image_execution_mode(
    mode: type[ImagePayloadExecutionMode],
) -> Any:
    """Declare the image execution mode the compiler should preserve."""
    if not (isinstance(mode, type) and issubclass(mode, ImagePayloadExecutionMode)):
        raise TypeError(
            "runtime_image_execution_mode mode must be an ImagePayloadExecutionMode "
            f"class, got {mode!r}."
        )

    def decorator(func: Any) -> Any:
        _mutable_callable_namespace(func)[
            FunctionContractAttribute.runtime_image_execution_mode
        ] = mode
        return func

    return decorator


def requires_payload_axis(role: type[AxisRole]) -> Any:
    """Declare that the primary image must carry a payload axis with ``role``."""

    requirement = PayloadAxisRequirement(role)

    def decorator(func: Any) -> Any:
        attach_callable_contract_metadata(func, payload_axis_requirement=requirement)
        return func

    return decorator


def preserves_payload_axes(func: Any) -> Any:
    """Declare that a callable's output keeps its input's payload axes."""

    attach_callable_contract_metadata(
        func,
        payload_axis_transition=PreservedPayloadAxes(),
    )
    return func


def creates_payload_axis(role: type[AxisRole]) -> Any:
    """Declare that a callable's output carries a new payload axis with ``role``."""

    transition = CreatedPayloadAxis(role)

    def decorator(func: Any) -> Any:
        attach_callable_contract_metadata(func, payload_axis_transition=transition)
        return func

    return decorator


def prepare_processing_callable(func: Any) -> None:
    """Prepare declarations through their shared process-local operation contract."""
    from openhcs.core.processing_preparation import CallablePreparation

    CallablePreparation.from_callable(func).prepare()


def reset_processing_callable_preparation_cache() -> None:
    """Clear process-local preparation caches for deterministic tests and tooling."""
    from openhcs.core.processing_preparation import PreparationOperation

    PreparationOperation.reset()


def prepare_module_autoregister_families(module_name: str) -> None:
    """Prepare the module's declared registry obligation once in this process."""
    from openhcs.core.processing_preparation import ModuleRegistryPreparation

    ModuleRegistryPreparation(module_name).prepare()


def _is_function_reference(func: Any) -> bool:
    """Return whether func is the compiler's nominal picklable reference."""
    from openhcs.core.function_reference import FunctionReference

    return isinstance(func, FunctionReference)


def _resolve_declared_callable(func: Any) -> Callable[..., object]:
    """Resolve one callable declaration without applying runtime adapters."""

    if _is_function_reference(func):
        return func.resolve()
    if callable(func):
        return func
    raise TypeError(f"Invalid callable contract function: {func}")


def _callable_namespace(func: Any) -> CallableNamespace:
    """Return the readable metadata namespace for a callable-like object."""
    if _is_function_reference(func):
        return func.declaration.as_namespace()
    return vars(func)


def _mutable_callable_namespace(func: Any) -> MutableMapping[str, Any]:
    """Return the writable metadata namespace for a Python callable."""
    namespace = vars(func)
    if not isinstance(namespace, MutableMapping):
        raise TypeError(f"{func!r} does not expose a mutable metadata namespace.")
    return namespace


@dataclass(frozen=True, slots=True)
class CallableProjection:
    """Nominal view over callable metadata used at compiler/runtime boundaries."""

    func: Any
    name: str
    module_name: str | None
    namespace: CallableNamespace

    @classmethod
    def from_callable(cls, func: Any) -> "CallableProjection":
        """Project a callable or compiler function reference into stable metadata."""
        if _is_function_reference(func):
            name = func.function_name
            module_name = func.original_module
        else:
            name = func.__name__
            module_name = func.__module__
        namespace = _callable_namespace(func)
        if not isinstance(name, str):
            raise TypeError(
                f"Callable name must be a string, got {type(name).__name__}."
            )
        if module_name is not None and not isinstance(module_name, str):
            raise TypeError(
                f"{name!r}.__module__ must be a string or None, "
                f"got {type(module_name).__name__}."
            )
        return cls(func=func, name=name, module_name=module_name, namespace=namespace)

    def has_published_signature(self) -> bool:
        """Whether catalog preparation already published this callable's signature."""
        return DeclaredSignature().read(
            self.namespace.get(FunctionContractAttribute.canonical_signature),
            owner=f"{self.name!r}.{FunctionContractAttribute.canonical_signature}",
        ) is not None

    def declared_callable(self) -> Any:
        """Keep ready library references or resolve live authored targets, preparing nothing."""
        if self.has_published_signature():
            return self.func
        return _resolve_declared_callable(self.func)

    def declared_contract(self) -> "CallableContract":
        """The contract read from the declaration alone, preparing nothing.

        A signature is read from the callable's annotations and preparation never
        changes it. Authoring a pipeline (converting a ``.cppipe``, lowering a
        function pattern) runs no kernel, so it must neither compile nor load
        one: kernels belong to the catalog preparation of the process that executes.
        """
        return self._contract_of(self.declared_callable())

    def prepared_contract(self) -> "CallableContract":
        """The same contract, after the declaration owner prepared the callable."""
        return self._contract_of(self.prepared_callable())

    def _contract_of(self, resolved: Any) -> "CallableContract":
        contract = CallableContract.from_callable(resolved)
        if contract.prepared_canonical_signature is None:
            contract = contract.with_prepared_signature()
        return dataclasses.replace(
            contract, func=self.func, function_name=self.name,
            module_name=self.module_name,
        )

    def prepared_callable(self) -> Any:
        """Keep ready library references or prepare live authored targets before validation."""
        if self.has_published_signature():
            return self.func
        resolved = _resolve_declared_callable(self.func)
        for target in type(self).from_callable(resolved).prepare_targets():
            prepare_processing_callable(target)
        return resolved

    def warm_canonical_signature(self) -> None:
        """Publish prepared target signatures only after all library hooks finish."""
        contract = CallableContract.from_callable(self.func).with_prepared_signature()
        contract.publish_signatures(_mutable_callable_namespace(self.func))

    def prepare_targets(self) -> tuple[Any, ...]:
        """Return wrapper/raw callables that may carry preparation metadata."""
        targets: list[Any] = []
        seen: set[int] = set()
        pending = [self.func]
        while pending:
            target = pending.pop()
            target_id = id(target)
            if target_id in seen:
                continue
            seen.add(target_id)
            targets.append(target)
            namespace = _callable_namespace(target)
            raw = namespace.get(FunctionContractAttribute.raw_processing_function)
            if callable(raw):
                pending.append(raw)
            wrapped = namespace.get("__wrapped__")
            if callable(wrapped):
                pending.append(wrapped)
        return tuple(targets)


def _signature_context_parameter(signature: inspect.Signature) -> str | None:
    """Inject processing context into a callable that names its parameter."""
    from openhcs.core.context.processing_context import ProcessingContext

    parameter_name = ProcessingContext.require_parameter_name()
    return parameter_name if parameter_name in signature.parameters else None


def _nominal_argument_types(annotation: object) -> tuple[type, ...]:
    annotation = resolve_annotated(annotation)
    if is_union_type(annotation):
        return tuple(
            argument_type for member in get_args(annotation)
            for argument_type in _nominal_argument_types(member)
        )
    return (
        (annotation,)
        if annotation is not Any and isinstance(annotation, type)
        else ()
    )


def _validate_request_public_fields(
    request_type: type[object],
    public_fields: tuple[str, ...],
) -> None:
    """Validate declared public request fields against the dataclass type."""
    dataclass_field_names = {field.name for field in fields(request_type)}
    missing = [
        field_name
        for field_name in public_fields
        if field_name not in dataclass_field_names
    ]
    if missing:
        raise ValueError(
            f"{request_type.__name__} has no request field(s): {', '.join(missing)}."
        )


def _request_public_signature(
    func: Callable[..., Any],
    binding: CallableRequestBinding,
    implementation_signature: inspect.Signature,
) -> inspect.Signature:
    """Return the public signature with request fields expanded."""
    defaults = binding.public_defaults_dict
    annotations = binding.public_annotations_dict
    request_parameters = tuple(
        inspect.Parameter(
            field_name,
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
            default=_request_field_default(binding.request_type, field_name, defaults),
            annotation=annotations.get(field_name, inspect.Parameter.empty),
        )
        for field_name in binding.public_fields
    )
    local_parameters = tuple(
        parameter
        for name, parameter in implementation_signature.parameters.items()
        if name != binding.request_parameter
    )
    return inspect.Signature(
        parameters=(*request_parameters, *local_parameters),
        return_annotation=implementation_signature.return_annotation,
    )


def _request_field_default(
    request_type: type[object],
    field_name: str,
    public_defaults: Mapping[str, Any],
) -> Any:
    """Return the public default for one request field."""
    if field_name in public_defaults:
        return public_defaults[field_name]
    field_by_name = {field.name: field for field in fields(request_type)}
    field = field_by_name[field_name]
    if field.default is not MISSING:
        return field.default
    if field.default_factory is not MISSING:  # type: ignore[comparison-overlap]
        return field.default_factory()  # type: ignore[misc]
    return inspect.Parameter.empty


def _unique_parameter_names(
    parameter_names: tuple[str, ...],
    *,
    owner: str,
) -> tuple[str, ...]:
    """Return a validated tuple of unique non-empty callable parameter names."""

    if not isinstance(parameter_names, tuple):
        raise TypeError(f"{owner} must be a tuple.")
    normalized = tuple(
        parameter_name.strip()
        for parameter_name in parameter_names
        if isinstance(parameter_name, str)
    )
    if (
        len(normalized) != len(parameter_names)
        or any(not parameter_name for parameter_name in normalized)
        or len(normalized) != len(set(normalized))
    ):
        raise TypeError(f"{owner} must contain unique non-empty strings.")
    return normalized


def _artifact_input_parameter_names(
    artifact_inputs: Iterable[ArtifactSpec],
) -> tuple[str, ...]:
    """Return unique artifact-fed parameter names in declaration order."""

    return tuple(
        dict.fromkeys(
            spec.parameter_name
            for spec in artifact_inputs
            if spec.parameter_name is not None
        )
    )


def _artifact_inputs_bound_to_signature(
    artifact_inputs: ArtifactSpecCollection,
    signature: inspect.Signature,
) -> ArtifactSpecCollection:
    """Bind an input to the same-name non-primary parameter the signature declares."""

    primary_parameter_name = CallableDeclaration.primary_input_name(signature.parameters)
    artifact_parameter_names = frozenset(signature.parameters) - {
        primary_parameter_name
    }
    return ArtifactSpecCollection(
        (
            dataclasses.replace(spec, parameter_name=spec.name)
            if spec.parameter_name is None and spec.name in artifact_parameter_names
            else spec
        )
        for spec in artifact_inputs
    )
