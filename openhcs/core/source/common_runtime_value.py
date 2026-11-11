"""Common runtime value projection with no SCC-member imports."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True, slots=True)
class CommonRuntimeValue:
    """Projection of a value family that is only valid when all values agree."""

    values: tuple[Any, ...]

    @classmethod
    def from_values(
        cls,
        values: Iterable[Any],
        *,
        ignore_none: bool = False,
    ) -> "CommonRuntimeValue":
        unique_values: list[Any] = []
        for value in values:
            if ignore_none and value is None:
                continue
            if not any(value == existing for existing in unique_values):
                unique_values.append(value)
        return cls(tuple(unique_values))

    @property
    def single(self) -> Any | None:
        """Return the shared value, or None when values disagree or are absent."""
        if len(self.values) == 1:
            return self.values[0]
        return None
