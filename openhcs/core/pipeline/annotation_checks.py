from __future__ import annotations

import inspect
from collections.abc import Sequence
from types import UnionType
from typing import Annotated, Any, Union, get_args, get_origin


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


def special_input_parameter_accepts_sequence(
    parameter: inspect.Parameter,
) -> bool:
    """Return whether one callable parameter declares an ordered value sequence."""

    return get_origin(parameter.annotation) in (Sequence, tuple, list)
