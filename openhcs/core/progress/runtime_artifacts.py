"""Generic runtime artifact addresses carried by progress events."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any, ClassVar

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

    @classmethod
    def from_context_body(
        cls,
        body: Mapping[str, Any],
    ) -> "RuntimeArtifactProgressPayload":
        raw_addresses = body.get("addresses")
        if not isinstance(raw_addresses, Sequence) or isinstance(
            raw_addresses,
            (str, bytes, bytearray),
        ):
            raise RuntimeArtifactPayloadError(
                "Runtime artifact payload field 'addresses' must be a sequence."
            )
        try:
            return cls(
                addresses=tuple(
                    RuntimeArtifactAddress.from_dict(address)
                    for address in raw_addresses
                )
            )
        except (KeyError, TypeError, ValueError) as error:
            raise RuntimeArtifactPayloadError(
                f"Malformed runtime artifact address: {error}"
            ) from error

    def context_body(self) -> dict[str, Any]:
        return {"addresses": [address.to_dict() for address in self.addresses]}
