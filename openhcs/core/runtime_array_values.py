"""Nominal runtime array payload protocol and NumPy interoperation."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any, Self

import numpy as np
from arraybridge import ArrayGeometry, ArrayPayload
from arraybridge.devices import Device
from arraybridge.libraries import Array, ArrayLibrary


def runtime_array_ufunc_result(
    ufunc: Any,
    method: str,
    inputs: tuple[Any, ...],
    kwargs: Mapping[str, Any],
) -> Any:
    """Invoke a NumPy ``__array_ufunc__`` protocol method without dynamic lookup."""
    match method:
        case "__call__":
            return ufunc(*inputs, **kwargs)
        case "reduce":
            return ufunc.reduce(*inputs, **kwargs)
        case "accumulate":
            return ufunc.accumulate(*inputs, **kwargs)
        case "reduceat":
            return ufunc.reduceat(*inputs, **kwargs)
        case "outer":
            return ufunc.outer(*inputs, **kwargs)
        case "at":
            return ufunc.at(*inputs, **kwargs)
        case _:
            return NotImplemented


class RuntimeArrayPayload(ArrayPayload, ABC):
    """Nominal ABC for array payload types accepted by runtime artifacts."""

    __array_priority__ = 1000

    @property
    @abstractmethod
    def shape(self) -> Any: ...

    @property
    def dtype(self) -> Any:
        """Return the array dtype; structured owners may derive it before realization."""
        return self.array_payload_data().dtype

    @property
    def geometry(self) -> ArrayGeometry:
        """Return the array geometry; structured owners derive it without realizing."""
        return ArrayGeometry(tuple(int(size) for size in self.shape))

    @abstractmethod
    def array_payload_data(self) -> Any: ...

    @abstractmethod
    def with_data(self, data: Any) -> Self: ...

    def __array__(self, dtype: Any | None = None, copy: bool | None = None) -> Any:
        data = np.asarray(host_array(self), dtype=dtype)
        return data.copy() if copy else data

    def array_ufunc_result(self, result: Any) -> Any:
        if isinstance(result, tuple):
            return tuple(self.array_ufunc_result(item) for item in result)
        if isinstance(result, np.ndarray) and np.issubdtype(result.dtype, np.bool_):
            return result
        if isinstance(result, np.ndarray):
            return self.with_data(result)
        return result

    def compare_array_payload(self, other: Any, ufunc: Any) -> Any:
        return ufunc(np.asarray(self), runtime_array_operand(other))

    def __lt__(self, other: Any) -> Any:
        return self.compare_array_payload(other, np.less)

    def __le__(self, other: Any) -> Any:
        return self.compare_array_payload(other, np.less_equal)

    def __gt__(self, other: Any) -> Any:
        return self.compare_array_payload(other, np.greater)

    def __ge__(self, other: Any) -> Any:
        return self.compare_array_payload(other, np.greater_equal)

    def __array_ufunc__(
        self,
        ufunc: Any,
        method: str,
        *inputs: Any,
        **kwargs: Any,
    ) -> Any:
        converted_inputs = tuple(runtime_array_operand(value) for value in inputs)
        if "out" in kwargs:
            kwargs = {
                **kwargs,
                "out": tuple(runtime_array_operand(value) for value in kwargs["out"]),
            }
        result = runtime_array_ufunc_result(ufunc, method, converted_inputs, kwargs)
        if result is NotImplemented:
            return NotImplemented
        return self.array_ufunc_result(result)


class DataBackedRuntimeArrayPayload(RuntimeArrayPayload):
    """Runtime array payload whose concrete array is stored in ``data``."""

    data: Any

    @property
    def shape(self) -> Any:
        return self.data.shape

    @property
    def ndim(self) -> int:
        return self.data.ndim

    @property
    def dtype(self) -> Any:
        return self.data.dtype

    def array_payload_data(self) -> Any:
        return self.data

    def __getitem__(self, key: Any) -> Any:
        return self.data[key]

    def __len__(self) -> int:
        return len(self.data)


RuntimeArrayData = RuntimeArrayPayload | np.ndarray


def runtime_array_operand(value: Any) -> Any:
    """Return the ndarray operand for nominal runtime array payloads."""
    if isinstance(value, RuntimeArrayPayload):
        return value.array_payload_data()
    return value


def host_array(value: Any) -> np.ndarray:
    """Return an array, or a payload's array, as the NumPy array OpenHCS stores.

    Files, object labels and NumPy readers all hold host arrays. A function may
    return its outputs in any array library, on any device; this is where such
    an array is copied to host memory, by the library the array itself belongs to.
    """
    data = runtime_array_operand(value)
    return ArrayLibrary.of(data).to_numpy(data)


@dataclass(frozen=True, slots=True)
class ArrayPlacement:
    """Where an array lives: its array library and the device of that library."""

    library: ArrayLibrary[Array]
    device: Device

    @classmethod
    def of(cls, value: Any) -> ArrayPlacement:
        """The placement of an existing array or payload."""
        data = runtime_array_operand(value)
        library = ArrayLibrary.of(data)
        return cls(library, library.device_of(data))

    @classmethod
    def beside(cls, value: Any, library: ArrayLibrary[Array]) -> ArrayPlacement:
        """``library`` on the device that holds ``value``."""
        return cls(library, cls.of(value).device)

    @property
    def memory_type(self) -> str:
        """The library's name, as memory declarations spell it."""
        return str(self.library.name)

    def place(self, value: Any) -> Any:
        """Return an array here; the same object when it already is."""
        data = runtime_array_operand(value)
        return ArrayLibrary.of(data).convert_to(data, self.library, self.device)

    def stack(self, values: Sequence[Any]) -> Any:
        """Stack arrays already placed here along a new leading axis."""
        return self.library.stack_arrays(list(values), self.device)


def array_geometry(value: Any) -> ArrayGeometry:
    """Return the geometry of an array or runtime payload without realizing it."""
    if isinstance(value, RuntimeArrayPayload):
        return value.geometry
    return ArrayGeometry.require_from_value(value)


def mask_array(mask: Any) -> Any:
    """Return the concrete array of a mask given as an array or array payload."""
    operand = runtime_array_operand(mask)
    return operand if is_array_payload(operand) else np.asarray(operand)


def is_array_payload(data: Any) -> bool:
    """Return whether OpenHCS or ArrayBridge owns this array payload type."""
    if isinstance(data, RuntimeArrayPayload):
        return True
    try:
        ArrayLibrary.of(data)
    except ValueError:
        return False
    return True
