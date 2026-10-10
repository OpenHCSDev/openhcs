"""Function-level artifact contract decorators for the pipeline compiler."""

from abc import ABC
from collections.abc import Mapping, Sequence
import inspect
from types import UnionType
from typing import (
    Annotated,
    Any,
    Callable,
    ClassVar,
    TypeVar,
    Union,
    get_args,
    get_origin,
    get_type_hints,
)

from metaclass_registry import AutoRegisterMeta
from python_introspect import RuntimeParameterDeclarationABC, add_parameter_exclusions

from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    SpecialArtifactType,
)
from openhcs.core.callable_contract import (
    CallableMetadata,
    FunctionStepExecutionScope,
    ImagePayloadConsumption,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.image_payload_execution_mode import (
    FullStackExecution,
    ImagePayloadExecutionMode,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.core.variable_component_stack_requirement import (
    AlwaysRequiresVariableComponentStack,
    VariableComponentStackRequirement,
)
from openhcs.processing.materialization import MaterializationSpec
from openhcs.core.axes import AxisRole

F = TypeVar("F", bound=Callable)


def runtime_context_parameter(parameter_name: str | None) -> Callable[[F], F]:
    """Declare context injection, or disable it while retaining the public ABI."""

    if parameter_name is not None and not isinstance(parameter_name, str):
        raise TypeError("runtime_context_parameter must be a parameter name or None.")

    def decorator(func: F) -> F:
        if (
            parameter_name is not None
            and parameter_name not in inspect.signature(func).parameters
        ):
            raise ValueError(
                f"Callable {func.__name__!r} does not declare parameter "
                f"{parameter_name!r}."
            )
        namespace = vars(func)
        namespace.pop(FunctionContractAttribute.canonical_signature, None)
        namespace.pop(FunctionContractAttribute.raw_runtime_signature, None)
        namespace[FunctionContractAttribute.runtime_context_parameter] = parameter_name
        return func

    return decorator


def resolved_callable_type_hints(func: Callable) -> dict[str, Any]:
    """Return the callable's resolved type contract or propagate its error."""

    signature = CallableMetadata.prepared_callable_signature(func)
    if signature is None:
        return get_type_hints(func)
    from typing import _strip_annotations

    return {
        **{name: _strip_annotations(parameter.annotation) for name, parameter in signature.parameters.items()
           if parameter.annotation is not inspect.Parameter.empty},
        **({} if signature.return_annotation is inspect.Signature.empty else {"return": _strip_annotations(signature.return_annotation)}),
    }


def annotation_accepts_runtime_type(annotation: object, value_type: type[Any]) -> bool:
    """Return whether a resolved annotation explicitly accepts a nominal type."""

    if annotation in (inspect.Signature.empty, Any):
        return False
    origin = get_origin(annotation)
    if origin in (Union, UnionType):
        return any(
            annotation_accepts_runtime_type(member, value_type)
            for member in get_args(annotation)
        )
    if origin is Annotated:
        annotated_type, *_metadata = get_args(annotation)
        return annotation_accepts_runtime_type(annotated_type, value_type)
    if origin in (Sequence, tuple, list):
        return any(
            member is not Ellipsis
            and annotation_accepts_runtime_type(member, value_type)
            for member in get_args(annotation)
        )
    nominal_type = origin if isinstance(origin, type) else annotation
    return isinstance(nominal_type, type) and issubclass(value_type, nominal_type)


def annotation_produces_runtime_type(
    annotation: object,
    runtime_type: type[Any],
) -> bool:
    """Return whether every value declared by an annotation has a nominal type."""

    if annotation in (inspect.Signature.empty, Any):
        return False
    origin = get_origin(annotation)
    if origin in (Union, UnionType):
        return all(
            annotation_produces_runtime_type(member, runtime_type)
            for member in get_args(annotation)
        )
    if origin is Annotated:
        annotated_type, *_metadata = get_args(annotation)
        return annotation_produces_runtime_type(annotated_type, runtime_type)
    nominal_type = origin if isinstance(origin, type) else annotation
    return isinstance(nominal_type, type) and issubclass(nominal_type, runtime_type)


def resolved_callable_parameter(
    func: Callable,
    parameter_name: str,
) -> inspect.Parameter:
    """Return one callable parameter with its runtime type hint resolved."""

    signature = CallableMetadata.callable_signature(func)
    parameter = signature.parameters.get(parameter_name)
    if parameter is None:
        raise ValueError(
            f"Callable {func.__name__!r} does not declare parameter "
            f"{parameter_name!r}."
        )
    annotation = resolved_callable_type_hints(func).get(
        parameter_name,
        parameter.annotation,
    )
    return parameter.replace(annotation=annotation)


class ObjectLabelInputExecutionMode(ABC, metaclass=AutoRegisterMeta):
    """How a callable consumes object-label special-input domains."""

    __registry_key__ = "key"
    __skip_if_no_key__ = True

    key: ClassVar[str | None] = None

    @classmethod
    def preserves_full_stack(cls, *, image_stack_required: bool) -> bool:
        """Return whether binding must preserve the declared label stack."""
        del image_stack_required
        return False

    @classmethod
    def invocation_kwargs(
        cls,
        kwargs: Mapping[str, Any],
        *,
        execution_mode: type[ImagePayloadExecutionMode],
        image_projection: RuntimePlaneAxisValueProjection | None,
        runtime_projection: RuntimePlaneAxisValueProjection | None,
        semantic_controls: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Return the invocation kwargs once the image's execution mode is known."""
        del execution_mode, image_projection, runtime_projection
        return {**kwargs, **semantic_controls}

    @classmethod
    def semantic_label_payload(cls, source_projected_payload, completion_payload):
        """Return the label payload that represents this measurement domain."""
        raise TypeError(
            f"{cls.__name__} declares no object-measurement label domain."
        )

    @classmethod
    def image_execution_mode(
        cls,
        labels,
        default: type[ImagePayloadExecutionMode],
        *,
        runtime_slice_count: int | None = None,
    ) -> type[ImagePayloadExecutionMode]:
        """Return the image execution mode for the semantic label payload."""
        raise TypeError(
            f"{cls.__name__} declares no object-measurement execution mode."
        )


class SliceAlignedLabels(ObjectLabelInputExecutionMode):
    """Labels are consumed plane by plane, aligned with the image."""

    key = "slice_aligned"

    @classmethod
    def semantic_label_payload(cls, source_projected_payload, completion_payload):
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        del source_projected_payload
        projection = completion_payload.declared_plane_projection()
        if projection is not None and projection.axis_size == 1:
            return RuntimeSliceProjection.value_for_singleton_slice(
                completion_payload,
                source_description="Slice-aligned object-label input",
            )
        return completion_payload

    @classmethod
    def image_execution_mode(cls, labels, default, *, runtime_slice_count=None):
        from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope

        if labels.object_label_domain().scope is ObjectLabelDomainScope.PAYLOAD:
            return default.for_payload_scoped_labels(runtime_slice_count)
        return default.for_plane_scoped_labels(labels.declared_plane_projection())


class FullStackLabels(ObjectLabelInputExecutionMode):
    """Labels are consumed as one whole stack."""

    key = "full_stack"

    @classmethod
    def preserves_full_stack(cls, *, image_stack_required: bool) -> bool:
        del image_stack_required
        return True

    @classmethod
    def semantic_label_payload(cls, source_projected_payload, completion_payload):
        del completion_payload
        return source_projected_payload

    @classmethod
    def image_execution_mode(cls, labels, default, *, runtime_slice_count=None):
        del labels, default, runtime_slice_count
        return FullStackExecution


class MatchImageStackLabels(ObjectLabelInputExecutionMode):
    """Labels follow the image: a stack when the image needs one."""

    key = "match_image_stack"

    @classmethod
    def preserves_full_stack(cls, *, image_stack_required: bool) -> bool:
        return image_stack_required

    @classmethod
    def invocation_kwargs(
        cls,
        kwargs,
        *,
        execution_mode,
        image_projection,
        runtime_projection,
        semantic_controls,
    ):
        """Match scalar images to their declared singleton runtime root.

        Matching labels can consume a singleton root only after the image's
        final execution mode and retained plane projection have been resolved.
        """
        if (
            execution_mode.per_plane
            and image_projection is None
            and runtime_projection is not None
            and runtime_projection.axis_size == 1
        ):
            from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

            kwargs = RuntimeSliceProjection.kwargs_for_slice(
                kwargs, runtime_projection.selected_plane(0)
            )
        return {**kwargs, **semantic_controls}


def _artifact_spec_from_output_declaration(
    spec: str | ArtifactSpec | tuple[str, MaterializationSpec | None],
) -> ArtifactSpec:
    """Normalize one output declaration into an ArtifactSpec."""
    if isinstance(spec, ArtifactSpec):
        return spec.for_plan_type(ArtifactOutputPlan)

    if isinstance(spec, str):
        name = spec.strip()
        if not name:
            raise ValueError("Artifact output names cannot be empty.")
        return ArtifactSpec.output(name, SpecialArtifactType)

    if isinstance(spec, tuple) and len(spec) == 2:
        key, mat_spec = spec
        if not isinstance(key, str):
            raise ValueError(
                f"Artifact output key must be string, got {type(key)}: {key}"
            )
        name = key.strip()
        if not name:
            raise ValueError("Artifact output names cannot be empty.")
        if mat_spec is not None and not isinstance(mat_spec, MaterializationSpec):
            raise ValueError(
                "Materialization spec must be a MaterializationSpec or None. "
                f"Got {type(mat_spec)} for key '{key}'."
            )
        return ArtifactSpec.output(
            name,
            SpecialArtifactType,
            materialization=mat_spec,
        )

    raise ValueError(
        f"Invalid artifact output spec: {spec}. "
        "Must be string, ArtifactSpec, or "
        "(string, MaterializationSpec) tuple."
    )


def _artifact_spec_from_input_declaration(
    spec: str | ArtifactSpec,
) -> ArtifactSpec:
    """Normalize one input declaration into an ArtifactSpec."""
    if isinstance(spec, ArtifactSpec):
        return spec.for_plan_type(ArtifactInputPlan)
    if isinstance(spec, str):
        return ArtifactSpec.input(
            spec,
            SpecialArtifactType,
            parameter_name=spec,
        )
    raise ValueError(
        f"Invalid artifact input spec: {spec}. " "Must be string or ArtifactSpec."
    )


def artifact_outputs(
    *output_specs: str | ArtifactSpec | tuple[str, MaterializationSpec | None],
) -> Callable[[F], F]:
    """Declare named artifacts produced by a processing function."""

    def decorator(func: F) -> F:
        artifact_specs = ArtifactSpecCollection(
            _artifact_spec_from_output_declaration(spec) for spec in output_specs
        ).unique(conflict_context=f"{func.__name__} artifact output")
        vars(func)[FunctionContractAttribute.artifact_outputs] = artifact_specs
        return func

    return decorator


def artifact_inputs(*input_specs: str | ArtifactSpec) -> Callable[[F], F]:
    """Declare named artifacts consumed by a processing function."""

    def decorator(func: F) -> F:
        artifact_specs = ArtifactSpecCollection(
            _artifact_spec_from_input_declaration(spec) for spec in input_specs
        ).specs
        vars(func)[FunctionContractAttribute.artifact_inputs] = artifact_specs
        add_parameter_exclusions(
            func,
            tuple(
                spec.parameter_name
                for spec in artifact_specs
                if spec.parameter_name is not None
            ),
        )
        return func

    return decorator


def _special_parameter_names(
    parameter_names: tuple[str, ...],
    *,
    decorator_name: str,
) -> tuple[str, ...]:
    normalized = tuple(name.strip() for name in parameter_names if name.strip())
    if len(normalized) != len(parameter_names):
        raise ValueError(f"{decorator_name} parameter names cannot be empty.")
    return normalized


def special_inputs(*parameter_names: str) -> Callable[[F], F]:
    """Declare runtime-managed non-image parameters for compatibility loaders."""

    normalized = _special_parameter_names(
        parameter_names,
        decorator_name="special_inputs",
    )

    def decorator(func: F) -> F:
        vars(func)[FunctionContractAttribute.special_inputs] = normalized
        add_parameter_exclusions(func, normalized)
        return func

    return decorator


def runtime_bound_parameters(
    *parameter_types: type[RuntimeParameterDeclarationABC],
) -> Callable[[F], F]:
    """Declare callable parameters supplied by runtime execution infrastructure."""

    normalized = _runtime_parameter_declaration_types(
        parameter_types,
        decorator_name="runtime_bound_parameters",
    )

    def decorator(func: F) -> F:
        vars(func)[FunctionContractAttribute.runtime_bound_parameters] = normalized
        add_parameter_exclusions(
            func,
            tuple(
                parameter_type.require_parameter_name() for parameter_type in normalized
            ),
        )
        return func

    return decorator


def _runtime_parameter_declaration_types(
    parameter_types: tuple[type[RuntimeParameterDeclarationABC], ...],
    *,
    decorator_name: str,
) -> tuple[type[RuntimeParameterDeclarationABC], ...]:
    return RuntimeParameterDeclarationABC.require_declaration_types(
        parameter_types,
        boundary=decorator_name,
    )


def _axis_roles(roles: tuple[type[AxisRole], ...], decorator_name: str) -> tuple:
    for role in roles:
        if not (isinstance(role, type) and issubclass(role, AxisRole)):
            raise TypeError(f"{decorator_name} takes axis roles; got {role!r}.")
    if len(roles) != len(set(roles)):
        raise TypeError(f"{decorator_name} roles must be unique.")
    return roles


def required_axis_roles(*roles: type[AxisRole]) -> Callable[[F], F]:
    """Declare axis roles the step's variable axes must cover for a callable."""
    normalized = _axis_roles(roles, "required_axis_roles")

    def decorator(func: F) -> F:
        vars(func)[FunctionContractAttribute.required_axis_roles] = normalized
        return func

    return decorator


def require_variable_component_stack(func: F) -> F:
    """Declare that a callable needs a real stacked variable-component axis."""
    vars(func)[
        FunctionContractAttribute.variable_component_stack_requirement
    ] = AlwaysRequiresVariableComponentStack()
    return func


def variable_component_stack_requirement(
    requirement: VariableComponentStackRequirement,
) -> Callable[[F], F]:
    """Attach a typed stack-axis requirement to a callable."""
    if not isinstance(requirement, VariableComponentStackRequirement):
        raise TypeError(
            "variable_component_stack_requirement requires "
            "VariableComponentStackRequirement."
        )

    def decorator(func: F) -> F:
        vars(func)[
            FunctionContractAttribute.variable_component_stack_requirement
        ] = requirement
        return func

    return decorator


def allowed_group_by_roles(*roles: type[AxisRole]) -> Callable[[F], F]:
    """Declare the axis roles a callable's step may group by."""
    normalized = _axis_roles(roles, "allowed_group_by_roles")

    def decorator(func: F) -> F:
        vars(func)[FunctionContractAttribute.allowed_group_by_roles] = normalized
        return func

    return decorator


def execution_scope(
    scope: FunctionStepExecutionScope,
) -> Callable[[F], F]:
    """Declare the lifecycle scope for a FunctionStep callable."""
    if not isinstance(scope, FunctionStepExecutionScope):
        raise TypeError("execution_scope requires FunctionStepExecutionScope.")

    def decorator(func: F) -> F:
        vars(func)[FunctionContractAttribute.execution_scope] = scope
        return func

    return decorator


def object_label_input_execution_mode(
    mode: type[ObjectLabelInputExecutionMode],
) -> Callable[[F], F]:
    """Declare how a callable consumes object-label special inputs."""

    if not (isinstance(mode, type) and issubclass(mode, ObjectLabelInputExecutionMode)):
        raise TypeError(
            "object_label_input_execution_mode mode must be "
            "ObjectLabelInputExecutionMode."
        )

    def decorator(func: F) -> F:
        vars(func)[FunctionContractAttribute.object_label_input_execution_mode] = mode
        return func

    return decorator


def object_label_input_execution_mode_from_callable(
    func: Callable,
) -> type[ObjectLabelInputExecutionMode]:
    """Return the declared object-label special-input execution mode."""

    try:
        namespace = vars(func)
    except TypeError:
        return SliceAlignedLabels
    if FunctionContractAttribute.object_label_input_execution_mode not in namespace:
        return SliceAlignedLabels
    declared = namespace[FunctionContractAttribute.object_label_input_execution_mode]
    if not (
        isinstance(declared, type)
        and issubclass(declared, ObjectLabelInputExecutionMode)
    ):
        raise TypeError(
            f"{func} object-label input execution mode must be "
            "ObjectLabelInputExecutionMode."
        )
    return declared


def composed_image_payload(func: F) -> F:
    """Declare that a callable consumes its image input as a composed image set."""
    vars(func)[
        FunctionContractAttribute.image_payload_consumption
    ] = ImagePayloadConsumption.COMPOSED
    return func


def special_input_parameter_accepts_sequence(
    parameter: inspect.Parameter,
) -> bool:
    """Return whether one callable parameter declares an ordered value sequence."""

    return get_origin(parameter.annotation) in (Sequence, tuple, list)
