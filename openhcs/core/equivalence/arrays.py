"""Canonical array payload handling for runtime equivalence."""

from __future__ import annotations

import hashlib

import numpy as np

from arraybridge import detect_memory_type
from openhcs.core.runtime_array_values import host_array


def array_memory_type(value: object) -> str | None:
    """Return the ArrayBridge memory type for an array payload, if known."""
    try:
        return detect_memory_type(value)
    except ValueError:
        return None


def contiguous_host_array(value: object) -> np.ndarray | None:
    """Return an ArrayBridge-supported array as contiguous host NumPy."""
    if array_memory_type(value) is None:
        return None
    return np.ascontiguousarray(host_array(value))


def canonical_scalar(value: object) -> object:
    """Return the Python scalar for backend scalar values."""
    if isinstance(value, np.generic):
        return value.item()
    return value


def semantic_array_payload(
    value: object,
) -> tuple[str, str, tuple[int, ...], str] | None:
    """Return a backend-independent exact payload for array content."""
    array = contiguous_host_array(value)
    if array is None:
        return None
    digest = hashlib.sha256()
    digest.update(memoryview(array).cast("B"))
    return (
        "array",
        str(array.dtype),
        tuple(int(axis) for axis in array.shape),
        digest.hexdigest(),
    )


def semantic_array_shape(value: object) -> tuple[int, ...] | None:
    """Return backend-independent array shape without hashing content."""
    array = contiguous_host_array(value)
    if array is None:
        return None
    return tuple(int(axis) for axis in array.shape)
