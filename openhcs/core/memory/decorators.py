"""Canonical OpenHCS import surface for arraybridge memory decorators.

The underlying memory conversion behavior belongs to arraybridge. OpenHCS adds
compiler/runtime metadata preservation at this boundary so memory declarations
and callable preparation contracts compose predictably.
"""

from __future__ import annotations

from collections.abc import Callable
import functools
import inspect
from typing import Any

import arraybridge as _arraybridge
from arraybridge import MemoryType


def _with_openhcs_metadata(decorator: Callable[..., Any]) -> Callable[..., Any]:
    """Wrap an arraybridge decorator with optional OpenHCS prepare metadata."""

    def openhcs_decorator(
        *args: Any,
        prepare: Any = None,
        contract: Any = None,
        **kwargs: Any,
    ) -> Any:
        if contract is None:
            from openhcs.processing.backends.lib_registry.unified_registry import (
                ProcessingContract,
            )

            contract = ProcessingContract.FLEXIBLE
        declared_processing_contract = _declared_processing_contract_name(contract)
        if declared_processing_contract is None:
            kwargs["contract"] = contract

        if args and callable(args[0]) and len(args) == 1:
            wrapped = decorator(image_payload_boundary(args[0]), **kwargs)
            _attach_openhcs_metadata(
                wrapped,
                prepare=prepare,
                declared_processing_contract=declared_processing_contract,
            )
            return wrapped

        arraybridge_decorator = decorator(*args, **kwargs)

        def decorate(target: Any) -> Any:
            wrapped = arraybridge_decorator(image_payload_boundary(target))
            _attach_openhcs_metadata(
                wrapped,
                prepare=prepare,
                declared_processing_contract=declared_processing_contract,
            )
            return wrapped

        return decorate

    openhcs_decorator.__name__ = getattr(decorator, "__name__", "openhcs_decorator")
    openhcs_decorator.__doc__ = getattr(decorator, "__doc__", None)
    openhcs_decorator.__module__ = __name__
    return openhcs_decorator


def _declares_image_payload(annotation: Any, *, member: type) -> bool:
    """Whether a parameter annotation admits payloads of family ``member``."""
    from python_introspect import is_union_type, resolve_annotated
    from typing import get_args

    annotation = resolve_annotated(annotation)
    if is_union_type(annotation):
        return any(
            _declares_image_payload(declared, member=member)
            for declared in get_args(annotation)
        )
    return isinstance(annotation, type) and issubclass(annotation, member)


def _admits_plain_image_payload(annotation: Any) -> bool:
    """Whether a parameter annotation names ``ImagePayload`` itself."""
    from python_introspect import is_union_type, resolve_annotated
    from typing import get_args

    from openhcs.core.runtime_image_values import ImagePayload

    annotation = resolve_annotated(annotation)
    if is_union_type(annotation):
        return any(_admits_plain_image_payload(member) for member in get_args(annotation))
    return annotation is ImagePayload


@functools.cache
def image_payload_boundary(wrapped: Any) -> Any:
    """Wrap bare image arguments once where the callable declares ``ImagePayload``.

    This is where a processing function's image arguments turn from bare
    arrays into payloads: inside the memory decorator (so direct, runtime and
    slice-by-slice calls share it), and on composed raw leaves. The primary
    parameter is wrapped when it declares any payload family member; another
    parameter is wrapped when it declares ``ImagePayload`` itself and receives
    a bare array.
    """
    from openhcs.core.runtime_array_values import is_array_payload
    from openhcs.core.runtime_image_values import ImagePayload, PlainImagePayload

    raw_signature = inspect.signature(inspect.unwrap(wrapped), eval_str=True)
    parameters = tuple(raw_signature.parameters.values())
    if not parameters:
        return wrapped
    primary = parameters[0].name
    image_parameters = tuple(
        (index, parameter.name)
        for index, parameter in enumerate(parameters)
        if (
            _declares_image_payload(parameter.annotation, member=ImagePayload)
            if index == 0
            else _admits_plain_image_payload(parameter.annotation)
        )
    )
    if not image_parameters:
        return wrapped
    positions = dict(image_parameters)

    def as_payload(name: str, value: Any) -> Any:
        if name == primary:
            return ImagePayload.of(value)
        if is_array_payload(value) and not isinstance(value, ImagePayload):
            return PlainImagePayload(value)
        return value

    def as_bare(value: Any) -> Any:
        if type(value) is PlainImagePayload:
            return value.data
        if type(value) is tuple:
            return tuple(as_bare(item) for item in value)
        return value

    @functools.wraps(wrapped)
    def image_payload_callable(*args: Any, **kwargs: Any) -> Any:
        primary_value = args[0] if args else kwargs.get(primary)
        args = tuple(
            as_payload(positions[index], value) if index in positions else value
            for index, value in enumerate(args)
        )
        for name in positions.values():
            if name in kwargs:
                kwargs[name] = as_payload(name, kwargs[name])
        result = wrapped(*args, **kwargs)
        # Bare pixels in, bare pixels out: a caller that passed an array (an
        # array library, slice-by-slice stacking) gets arrays back.
        if primary in positions.values() and not isinstance(primary_value, ImagePayload):
            return as_bare(result)
        return result

    return image_payload_callable


def _declared_processing_contract_name(contract: Any) -> str | None:
    """Return OpenHCS processing-contract metadata carried by a decorator."""
    if contract is None or callable(contract):
        return None
    name = getattr(contract, "name", None)
    if isinstance(name, str) and name:
        return name
    if isinstance(contract, str) and contract:
        return contract
    raise TypeError(
        "OpenHCS memory decorator contract must be a callable arraybridge "
        f"validator or a processing contract declaration; got {contract!r}."
    )


def _attach_openhcs_metadata(
    wrapped: Any,
    *,
    prepare: Any,
    declared_processing_contract: str | None,
) -> None:
    from openhcs.core.callable_contract import attach_callable_contract_metadata
    from openhcs.core.config import runtime_config_parameter
    from python_introspect import add_parameter_exclusions, parameter_exclusions

    signature = _signature_with_resolved_raw_annotations(wrapped)
    raw_callable = inspect.unwrap(wrapped)
    add_parameter_exclusions(
        wrapped,
        parameter_exclusions(raw_callable),
    )
    normalized_parameter_items: list[inspect.Parameter] = []
    runtime_config_parameter_names: list[str] = []
    for parameter in signature.parameters.values():
        normalized = runtime_config_parameter(parameter)
        if normalized is not None:
            runtime_config_parameter_names.append(parameter.name)
            normalized = normalized.replace(default=normalized.annotation())
        normalized_parameter_items.append(
            parameter if normalized is None else normalized
        )
    normalized_parameters = tuple(normalized_parameter_items)
    if normalized_parameters != tuple(signature.parameters.values()):
        wrapped.__signature__ = signature.replace(parameters=normalized_parameters)
    if runtime_config_parameter_names:
        add_parameter_exclusions(wrapped, tuple(runtime_config_parameter_names))
    if prepare is not None:
        from openhcs.core.callable_contract import attach_processing_prepare

        attach_processing_prepare(wrapped, prepare)
    if declared_processing_contract is not None:
        _strip_unowned_semantic_controls(wrapped, declared_processing_contract)
        attach_callable_contract_metadata(
            wrapped,
            declared_processing_contract=declared_processing_contract,
        )


def _signature_with_resolved_raw_annotations(wrapped: Any) -> inspect.Signature:
    """Resolve postponed annotations at their authoritative callable globals."""

    signature = inspect.signature(wrapped)
    raw_signature = inspect.signature(inspect.unwrap(wrapped), eval_str=True)
    raw_parameters = raw_signature.parameters
    parameters = tuple(
        (
            parameter.replace(annotation=raw_parameters[parameter.name].annotation)
            if parameter.name in raw_parameters
            else parameter
        )
        for parameter in signature.parameters.values()
    )
    return signature.replace(
        parameters=parameters,
        return_annotation=raw_signature.return_annotation,
    )


def _strip_unowned_semantic_controls(
    wrapped: Any,
    declared_processing_contract: str,
) -> None:
    from openhcs.processing.backends.lib_registry.unified_registry import (
        ProcessingContract,
    )

    contract = ProcessingContract.from_declared_name(declared_processing_contract)
    if contract is None:
        return
    allowed_semantic_control_names = (
        contract.declaration.injected_semantic_control_parameter_names()
    )
    semantic_control_names = {
        parameter_type.require_parameter_name()
        for parameter_type in ProcessingContract.semantic_control_parameter_types()
    }
    params_to_strip = semantic_control_names - allowed_semantic_control_names
    if not params_to_strip:
        return
    signature = inspect.signature(wrapped)
    enabled_hidden_defaults = tuple(
        name
        for name in params_to_strip
        if name in signature.parameters
        and signature.parameters[name].default is not inspect.Parameter.empty
        and bool(signature.parameters[name].default)
    )
    if enabled_hidden_defaults:
        raise ValueError(
            f"Processing contract {declared_processing_contract!r} cannot hide "
            "enabled semantic-control defaults: "
            f"{enabled_hidden_defaults!r}."
        )
    filtered_parameters = tuple(
        parameter
        for parameter in signature.parameters.values()
        if parameter.name not in params_to_strip
    )
    if len(filtered_parameters) != len(signature.parameters):
        wrapped.__signature__ = signature.replace(parameters=filtered_parameters)


memory_types = _with_openhcs_metadata(_arraybridge.memory_types)
for _memory_type in MemoryType:
    globals()[_memory_type.value] = _with_openhcs_metadata(
        getattr(_arraybridge, _memory_type.value)
    )

__all__ = [
    "memory_types",
    *(memory_type.value for memory_type in MemoryType),
]
