from dataclasses import dataclass
from typing import Optional

from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.callable.function_patterns import (
    DEFAULT_GROUP_KEY,
    FunctionInvocationKey,
)


class MissingArtifactInputError(ValueError):
    """Raised when a step consumes an artifact that no prior producer provides."""

    def __init__(
        self,
        *,
        step_id: int,
        artifact_key: str,
        step_name: str | None,
    ) -> None:
        self.step_id = step_id
        self.artifact_key = artifact_key
        self.step_name = step_name
        step_label = step_name or str(step_id)
        super().__init__(
            f"Step {step_id} ({step_label}) needs artifact input "
            f"{artifact_key!r}, but no previous step, source binding, or "
            "metadata resolver provides it."
        )


@dataclass(frozen=True, slots=True)
class ArtifactProducer:
    """Compiled artifact producer identity and scope."""

    spec: ArtifactSpec
    groups: tuple[Optional[str], ...]
    invocation_keys: tuple[FunctionInvocationKey, ...]
    producer_step_index: int | None = None

    def __post_init__(self) -> None:
        if self.producer_step_index is not None and (
            type(self.producer_step_index) is not int or self.producer_step_index < 0
        ):
            raise ValueError(
                "ArtifactProducer.producer_step_index must be a non-negative "
                "integer or None."
            )

    def has_explicit_invocation_group_ownership(self) -> bool:
        """Return whether grouped pattern dispatch owns this output's groups."""

        return bool(self.invocation_keys) and all(
            key.group_key != DEFAULT_GROUP_KEY for key in self.invocation_keys
        )

    def owns_invocation(self, invocation_key: FunctionInvocationKey) -> bool:
        """Return whether this producer owns the consumer's compile-time group."""

        return invocation_key in self.invocation_keys
