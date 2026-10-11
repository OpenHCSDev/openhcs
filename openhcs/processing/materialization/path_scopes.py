"""Nominal relative-path scopes for materialized artifacts."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from openhcs.core.context.processing_context import ProcessingContext


class MaterializationRelativePathScope(ABC):
    """Scope a writer-declared relative path to its runtime execution."""

    @abstractmethod
    def scoped_path(
        self,
        relative_path: PurePosixPath,
        context: ProcessingContext | None,
    ) -> PurePosixPath:
        """Return the relative path owned by one runtime execution context."""


@dataclass(frozen=True, slots=True)
class SharedMaterializationRelativePathScope(MaterializationRelativePathScope):
    """Keep a relative output path shared across execution axes."""

    def scoped_path(
        self,
        relative_path: PurePosixPath,
        context: ProcessingContext | None,
    ) -> PurePosixPath:
        del context
        return relative_path


@dataclass(frozen=True, slots=True)
class ExecutionAxisMaterializationRelativePathScope(MaterializationRelativePathScope):
    """Isolate relative outputs when one execution contains multiple axes."""

    def scoped_path(
        self,
        relative_path: PurePosixPath,
        context: ProcessingContext | None,
    ) -> PurePosixPath:
        if context is None or context.execution_runtime is None:
            return relative_path
        if len(context.execution_runtime.execution_axis_values) <= 1:
            return relative_path

        from openhcs.core.source_projection import OpenHCSPlaneAddress

        axis_token = OpenHCSPlaneAddress.component_token(context.require_axis_id())
        return PurePosixPath(axis_token) / relative_path
