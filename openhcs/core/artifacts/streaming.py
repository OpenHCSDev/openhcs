"""Whether a declared artifact joins automatic viewer streaming.

Every artifact remains available for explicit, on-demand streaming from its
materialized outputs. The declaration only controls the automatic viewer
streaming performed as part of pipeline execution.
"""

from __future__ import annotations

from abc import ABC
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta


class ViewerStreaming(ABC, metaclass=AutoRegisterMeta):
    """How one declared artifact reaches the configured viewers."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    automatically_streams: ClassVar[bool]


class AutomaticStreaming(ViewerStreaming):
    """Stream the artifact to enabled viewers as the pipeline saves it."""

    name = "automatic"
    automatically_streams = True


class OnDemandStreaming(ViewerStreaming):
    """Stream the artifact only when a user asks for it."""

    name = "on_demand"
    automatically_streams = False
