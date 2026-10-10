"""Framework-neutral pipeline scope identity under one dataset scope."""

from __future__ import annotations

import re
from dataclasses import dataclass

from openhcs.core.dataset_sources.dataset_scopes import SCOPE_SEGMENT_SEPARATOR

PIPELINE_SCOPE_SEGMENT = "pipeline"
PIPELINE_SCOPE_PATTERN = re.compile(
    rf"^.+{re.escape(SCOPE_SEGMENT_SEPARATOR)}{re.escape(PIPELINE_SCOPE_SEGMENT)}$"
)


@dataclass(frozen=True, slots=True)
class PipelineScopeIdentity:
    """ObjectState scope for the pipeline under one plate scope."""

    scope_id: str
    plate_scope: str

    @classmethod
    def from_plate_scope(cls, plate_scope: str) -> "PipelineScopeIdentity":
        if not plate_scope:
            raise ValueError("Pipeline scope requires a non-empty plate scope.")
        return cls(
            scope_id=(
                f"{plate_scope}{SCOPE_SEGMENT_SEPARATOR}{PIPELINE_SCOPE_SEGMENT}"
            ),
            plate_scope=plate_scope,
        )

    @classmethod
    def from_scope_id(cls, scope_id: str) -> "PipelineScopeIdentity":
        if not cls.matches(scope_id):
            raise ValueError(f"Invalid pipeline scope id: {scope_id!r}")
        plate_scope, _pipeline_segment = scope_id.rsplit(
            SCOPE_SEGMENT_SEPARATOR,
            1,
        )
        return cls(scope_id=scope_id, plate_scope=plate_scope)

    @classmethod
    def matches(cls, scope_id: str) -> bool:
        return PIPELINE_SCOPE_PATTERN.fullmatch(scope_id) is not None

    @classmethod
    def handler_pattern(cls) -> str:
        return PIPELINE_SCOPE_PATTERN.pattern
