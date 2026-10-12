"""Lightweight nominal tab identities for OpenHCS desktop windows."""

from __future__ import annotations

from enum import Enum
from typing import Self

from formbridge.services.tab_identity import TabLabelDeclarationMixin


class DualEditorTab(TabLabelDeclarationMixin, str, Enum):
    """Step-editor tab labels, importable without Qt (gallery catalog, agent UI bridge).

    The tabs themselves are the ``StepEditorTab`` classes in
    ``openhcs.pyqt_gui.windows.dual_editor_tabs``; each takes its label from here.
    """

    def __new__(cls, value: str, label: str) -> Self:
        member = str.__new__(cls, value)
        member._value_ = value
        member.label = label
        return member

    STEP_SETTINGS = ("step_settings", "Step Settings")
    FUNCTION_PATTERN = ("function_pattern", "Function Pattern")
    ARTIFACTS = ("artifacts", "Artifacts")


class PlateViewerTab(TabLabelDeclarationMixin, str, Enum):
    """Plate-viewer tabs with declaration-owned public labels."""

    def __new__(cls, value: str, label: str) -> Self:
        member = str.__new__(cls, value)
        member._value_ = value
        member.label = label
        return member

    IMAGE_BROWSER = ("image_browser", "Image Browser")
    METADATA = ("metadata", "Metadata")
