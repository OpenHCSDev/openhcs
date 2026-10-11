"""Generic runtime artifact addresses carried by progress events."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import ClassVar

from openhcs.core.progress.types import ProgressContextPayload
from openhcs.core.runtime_stores import RuntimeArtifactAddress, StoredRuntimeValue


class RuntimeArtifactPayloadError(ValueError):
    """Raised when runtime artifact progress context is malformed."""


@dataclass(frozen=True, slots=True)
class RuntimeArtifactProgressPayload(ProgressContextPayload):
    """Transport addresses for runtime values written by one step event."""

    context_key: ClassVar[str] = "runtime_artifacts"
    malformed_error: ClassVar[type[ValueError]] = RuntimeArtifactPayloadError

    addresses: tuple[RuntimeArtifactAddress, ...]

    @classmethod
    def from_records(
        cls,
        records: Sequence[StoredRuntimeValue],
    ) -> "RuntimeArtifactProgressPayload | None":
        addresses = tuple(
            RuntimeArtifactAddress.from_record(record) for record in records
        )
        return None if not addresses else cls(addresses=addresses)
