"""Constants for the materialization system (greenfield)."""

from __future__ import annotations

from enum import Enum


class WriteMode(str, Enum):
    """Overwrite/delete semantics for materialization writes."""

    OVERWRITE = "overwrite"
    ERROR = "error"
