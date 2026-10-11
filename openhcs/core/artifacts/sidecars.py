"""Sidecar roles: named artifacts derived from a primary artifact."""

from __future__ import annotations

from abc import ABC
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta


class ArtifactSidecarRole(ABC, metaclass=AutoRegisterMeta):
    """A named sidecar artifact derived from a primary artifact.

    Each role is a subclass; a domain declares its own roles beside the
    kernel's two.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str]
    inspection_only: ClassVar[bool] = False
    """Whether the sidecar exists only for inspection, never as a pipeline result."""

    @classmethod
    def name_for(
        cls,
        primary_artifact_name: str,
        *,
        separator: str = "__",
    ) -> str:
        """Return the sidecar artifact name for one primary artifact."""
        if not separator:
            raise ValueError("ArtifactSidecarRole sidecar separator cannot be empty.")
        normalized = primary_artifact_name.strip()
        if not normalized:
            raise ValueError("primary_artifact_name cannot be empty.")
        return f"{normalized}{separator}{cls.name}"


class MaterializedImageCopy(ArtifactSidecarRole):
    """A materialized copy of an image artifact (for example a saved image)."""

    name = "materialized_image_copy"


class QaCheckpoint(ArtifactSidecarRole):
    """An inspection checkpoint published beside a primary artifact."""

    name = "qa_checkpoint"
    inspection_only = True
