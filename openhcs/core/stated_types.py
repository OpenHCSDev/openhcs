"""A user-facing declaration must state its type.

OpenHCS builds a form control, an MCP parameter description and an array
conversion from a declared type. ``Any`` gives them nothing to build, so it is
refused where the declaration is consumed, naming the field or parameter.
"""

from __future__ import annotations

import ast
import inspect
import typing
from collections.abc import Callable, Iterator, Mapping
from dataclasses import fields, is_dataclass


class UnstatedTypeError(TypeError):
    """A config field or a function parameter is annotated ``Any``."""


def says_any(annotation: object, namespace: Mapping[str, object]) -> bool:
    """Whether ``Any`` appears in an annotation, at any depth, evaluated or quoted."""
    if isinstance(annotation, str):
        return _quoted_says_any(annotation, namespace)
    if isinstance(annotation, list):  # the parameter list of ``Callable[[...], R]``
        return any(says_any(member, namespace) for member in annotation)
    if annotation is typing.Any:
        return True
    origin = typing.get_origin(annotation)
    if origin is typing.Literal:
        return False  # Literal members are values, not types.
    members = typing.get_args(annotation)
    if origin is typing.Annotated:
        members = members[:1]  # The rest is metadata.
    return any(says_any(member, namespace) for member in members)


def _quoted_says_any(annotation: str, namespace: Mapping[str, object]) -> bool:
    """Read a quoted annotation by name, without evaluating it.

    A function under ``from __future__ import annotations`` may name types that
    exist only for the type checker; looking names up never fails on those.
    """
    for node in ast.walk(ast.parse(annotation.strip(), mode="eval")):
        if isinstance(node, ast.Name) and namespace.get(node.id) is typing.Any:
            return True
        if (
            isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and getattr(namespace.get(node.value.id), node.attr, None) is typing.Any
        ):
            return True
    return False


def _dataclasses_in(annotation: object) -> Iterator[type]:
    if is_dataclass(annotation) and isinstance(annotation, type):
        yield annotation
    for member in typing.get_args(annotation):
        yield from _dataclasses_in(member)


def require_stated_field_types(config_type: type) -> None:
    """Refuse a config dataclass that has, or nests, a field annotated ``Any``."""
    unstated: list[str] = []
    reached: set[type] = set()
    pending = [config_type]
    while pending:
        owner = pending.pop()
        if owner in reached:
            continue
        reached.add(owner)
        hints = typing.get_type_hints(owner, include_extras=True)
        for declared in fields(owner):
            if says_any(hints[declared.name], {}):
                unstated.append(f"{owner.__qualname__}.{declared.name}")
            pending.extend(_dataclasses_in(hints[declared.name]))
    if unstated:
        raise UnstatedTypeError(
            f"{config_type.__qualname__} declares {', '.join(sorted(unstated))} as Any. "
            "State each field's type: its form control and its description are built from it."
        )


def require_stated_parameter_types(function: Callable[..., object]) -> None:
    """Refuse a processing function with a parameter annotated ``Any``."""
    namespace = inspect.unwrap(function).__globals__
    unstated = [
        name
        for name, parameter in inspect.signature(function).parameters.items()
        if says_any(parameter.annotation, namespace)
    ]
    if unstated:
        raise UnstatedTypeError(
            f"Function {function.__name__!r} declares {', '.join(map(repr, unstated))} as Any. "
            "State each parameter's type (for example float, int, bool, str, an Enum, "
            "a Literal of the allowed values, or the array type of the function's memory "
            "decorator): its form control and its description are built from it."
        )
