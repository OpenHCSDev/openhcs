"""Shared DTOs for the headless OpenHCS agent API."""

from __future__ import annotations

from dataclasses import dataclass


SCHEMA_VERSION = "openhcs.agent.v1"


@dataclass(frozen=True, slots=True)
class RenderedSource:
    schema_version: str
    title: str
    source: str
    mime_type: str = "text/x-python"
