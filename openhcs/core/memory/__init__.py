"""Memory module for OpenHCS.

This module re-exports ArrayBridge's memory taxonomy and conversion utilities.
OpenHCS adds only runtime composition helpers and callable metadata adapters.
"""

from collections.abc import Sequence
from typing import Any

from arraybridge import ArrayGeometry

# Re-export from arraybridge
from arraybridge import (
    # Converters
    convert_memory,
    detect_memory_type,
    # Stack utilities
    stack_slices,
    unstack_slices,
    # Slice processing
    process_slices,
    # Exceptions
    MemoryConversionError,
)
from arraybridge.types import (
    MEMORY_TYPE_CUPY,
    MEMORY_TYPE_JAX,
    MEMORY_TYPE_NUMPY,
    MEMORY_TYPE_PYCLESPERANTO,
    MEMORY_TYPE_TENSORFLOW,
    MEMORY_TYPE_TORCH,
    MemoryType,
)

# OpenHCS wraps ArrayBridge decorators to preserve compiler metadata while
# leaving conversion semantics in ArrayBridge.
from . import decorators as decorators

for _memory_type in MemoryType:
    _memory_type.prepare_import()

memory_types = decorators.memory_types
for _memory_type in MemoryType:
    globals()[_memory_type.value] = getattr(decorators, _memory_type.value)


def stack_runtime_slices(
    slices: Sequence[Any],
    memory_type: str,
    gpu_id: int | None,
) -> Any:
    """Stack an explicitly declared runtime-slice sequence along axis zero."""

    slice_values = tuple(slices)
    if not slice_values:
        raise ValueError("Runtime-slice stacking requires at least one slice.")
    target = MemoryType(memory_type)
    prepared_slices = [
        MemoryType(detect_memory_type(value)).convert_to(value, target, gpu_id)
        for value in slice_values
    ]
    runtime_slice_stack_geometry(prepared_slices)
    return target.stack_arrays(prepared_slices, gpu_id)


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
    memory_type: str,
    gpu_id: int | None,
    *,
    expected_count: int | None = None,
) -> tuple[Any, ...]:
    """Split an explicitly declared leading runtime-slice axis."""

    converted = MemoryType(detect_memory_type(stack)).convert_to(
        stack, MemoryType(memory_type), gpu_id
    )
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
    # Converters
    "convert_memory",
    "detect_memory_type",
    # Memory type constants
    "MEMORY_TYPE_NUMPY",
    "MEMORY_TYPE_CUPY",
    "MEMORY_TYPE_TORCH",
    "MEMORY_TYPE_TENSORFLOW",
    "MEMORY_TYPE_JAX",
    "MEMORY_TYPE_PYCLESPERANTO",
    # Decorators
    "memory_types",
    *(memory_type.value for memory_type in MemoryType),
    "decorators",
    # Stack utilities
    "stack_slices",
    "unstack_slices",
    "stack_runtime_slices",
    "unstack_runtime_slices",
    # Slice processing
    "process_slices",
    # GPU cleanup
    # Exceptions
    "MemoryConversionError",
    # Types
    "MemoryType",
]
