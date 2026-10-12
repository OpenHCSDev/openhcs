"""Lightweight nominal tab identities for OpenHCS desktop windows."""

from __future__ import annotations

from enum import Enum
from typing import Self

from formbridge.services.tab_identity import TabLabelDeclarationMixin

class PlateViewerTab(TabLabelDeclarationMixin, str, Enum):
    """Plate-viewer tabs with declaration-owned public labels."""

    def __new__(cls, value: str, label: str) -> Self:
        member = str.__new__(cls, value)
        member._value_ = value
        member.label = label
        return member

    IMAGE_BROWSER = ("image_browser", "Image Browser")
    METADATA = ("metadata", "Metadata")
