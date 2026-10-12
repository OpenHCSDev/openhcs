"""The memory decorators OpenHCS functions declare with, and runtime-slice stacking.

Array libraries, devices and conversion belong to ArrayBridge; import them from
there.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING, Any

from arraybridge import ArrayGeometry
from arraybridge.libraries import ArrayLibrary

# OpenHCS wraps ArrayBridge decorators to preserve compiler metadata while
# leaving conversion semantics in ArrayBridge.
from . import decorators as decorators

if TYPE_CHECKING:
    from openhcs.core.runtime_array_values import ArrayPlacement

for _library in ArrayLibrary.all():
    _library.prepare_import()

memory_types = decorators.memory_types
for _library in ArrayLibrary.all():
    globals()[_library.name] = getattr(decorators, _library.name)


def stack_runtime_slices(slices: Sequence[Any], placement: ArrayPlacement) -> Any:
    """Stack an explicitly declared runtime-slice sequence along axis zero."""

    slice_values = tuple(slices)
    if not slice_values:
        raise ValueError("Runtime-slice stacking requires at least one slice.")
    prepared_slices = [placement.place(value) for value in slice_values]
    runtime_slice_stack_geometry(prepared_slices)
    return placement.stack(prepared_slices)


def runtime_slice_stack_geometry(slices: Sequence[Any]) -> ArrayGeometry:
    """Validate the geometry shared by deferred and concrete slice stacks."""
    from openhcs.core.runtime_array_values import array_geometry

    shapes = tuple(array_geometry(value).shape for value in slices)
    if not shapes:
        raise ValueError("Runtime-slice stacking requires at least one slice.")
    if any(shape != shapes[0] for shape in shapes[1:]):
        raise ValueError(
            "Runtime slices must have one exact shape before stacking; "
            f"got {shapes!r}."
        )
    return ArrayGeometry((len(shapes), *shapes[0]))


def unstack_runtime_slices(
    stack: Any,
    placement: ArrayPlacement,
    *,
    expected_count: int | None = None,
) -> tuple[Any, ...]:
    """Split an explicitly declared leading runtime-slice axis."""

    converted = placement.place(stack)
    shape = tuple(int(value) for value in converted.shape)
    if not shape:
        raise ValueError("Runtime-slice unstacking requires a leading array axis.")
    if expected_count is not None and shape[0] != expected_count:
        raise ValueError(
            "Runtime-slice stack cardinality does not match its declaration: "
            f"{shape[0]} != {expected_count}."
        )
    return tuple(converted[index] for index in range(shape[0]))


__all__ = [
    "memory_types",
    *(library.name for library in ArrayLibrary.all()),
    "decorators",
    "stack_runtime_slices",
    "unstack_runtime_slices",
    "runtime_slice_stack_geometry",
]
