"""Payload base shared by every artifact kind.

Artifacts are named, non-primary-image values produced or consumed by function
invocations. This module owns what a payload is independently of its kind: its
generic shape, its declared name, and the materialization metadata it may carry.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.runtime_array_values import is_array_payload
from openhcs.core.runtime_tabular_values import is_table_payload

if TYPE_CHECKING:
    from openhcs.core.artifacts.plans import ArtifactOutputPlan
    from openhcs.core.steps.function_output_identity import FunctionOutputIdentity


class PayloadShape(ABC, metaclass=AutoRegisterMeta):
    """Generic runtime payload shape required by an artifact kind."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def accepts(cls, value: object) -> bool:
        """Return whether a runtime value has this shape."""


class AnyPayloadShape(PayloadShape):
    name = "any"

    @classmethod
    def accepts(cls, value: object) -> bool:
        del value
        return True


class ArrayPayloadShape(PayloadShape):
    name = "array"

    @classmethod
    def accepts(cls, value: object) -> bool:
        return is_array_payload(value)


class TablePayloadShape(PayloadShape):
    name = "table"

    @classmethod
    def accepts(cls, value: object) -> bool:
        return is_table_payload(value)


class MappingPayloadShape(PayloadShape):
    name = "mapping"

    @classmethod
    def accepts(cls, value: object) -> bool:
        return isinstance(value, Mapping)


class NamedArtifactPayload:
    """Nominal payload whose declared name must match its compiled artifact."""

    __slots__ = ()
    name: str

    def require_name(self) -> None:
        """Require a nonempty declared name."""

        if not self.name:
            raise ValueError(f"{type(self).__name__}.name cannot be empty.")

    def validate_artifact_name(self, expected_name: str) -> None:
        """Require a nonempty name equal to its compiled artifact's name."""

        self.require_name()
        if self.name != expected_name:
            raise ValueError(
                f"Runtime payload name {self.name!r} does not match planned "
                f"artifact {expected_name!r}."
            )


class ArtifactMaterializationPayload(ABC):
    """Nominal marker for rich artifact materialization metadata."""

    @abstractmethod
    def participates_in_runtime_export_observation(self) -> bool:
        """Return whether this materialization is a pipeline-declared export."""

    @abstractmethod
    def participates_in_persistent_materialization(self) -> bool:
        """Return whether this materialization writes to persistent targets."""

    @abstractmethod
    def uses_source_identity_filename(self) -> bool:
        """Return whether this materialization names files by source identity."""

    @abstractmethod
    def filename_qualifier(self, output_plan: ArtifactOutputPlan) -> str | None:
        """Derive the output role required by this materialization purpose."""

    def filename_identity_for_output(
        self,
        identity: FunctionOutputIdentity,
        output_plan: ArtifactOutputPlan,
    ) -> FunctionOutputIdentity:
        """Apply a declared role through the shared filename identity algorithm."""
        qualifier = self.filename_qualifier(output_plan)
        return (
            identity
            if qualifier is None
            else identity.with_filename_qualifier(qualifier)
        )


@dataclass(frozen=True)
class NoMainFlowOutput:
    """Nominal return value for invocations that record artifacts only."""
