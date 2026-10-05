"""Generic returned-output matching for runtime artifact contracts."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, TypeAlias

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactSpec,
)


class RuntimeOutputBundle(ABC):
    """Nominal multi-output value exposed to generic runtime matching."""

    @abstractmethod
    def as_runtime_tuple(self) -> tuple[object, ...]:
        """Return the canonical main output followed by artifact outputs."""


RuntimeMatchedOutput: TypeAlias = tuple[ArtifactOutputPlan, ArtifactSpec, Any]


def runtime_output_tuple(value: Any) -> Any:
    """Lower a nominal output bundle to the generic positional output ABI."""

    if isinstance(value, RuntimeOutputBundle):
        return value.as_runtime_tuple()
    return value


def split_runtime_output(value: Any) -> tuple[Any, tuple[Any, ...]]:
    """Split one runtime return into its canonical and artifact positions."""

    positional = runtime_output_tuple(value)
    if isinstance(positional, tuple):
        if not positional:
            raise ValueError("Runtime output tuples cannot be empty.")
        return positional[0], tuple(positional[1:])
    return positional, ()
