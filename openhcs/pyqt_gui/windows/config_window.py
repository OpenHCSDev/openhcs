"""OpenHCS's configuration window: its document format and window ids."""

from __future__ import annotations

from typing import ClassVar

from pyqt_reactive.windows.config_window import ConfigDocumentFormat, ConfigWindow

from openhcs.core.config_document import ConfigDocumentAuthority
from formbridge.bridge.identities import UiStableWindowIdentityDeclaration


class OpenHCSConfigDocument(ConfigDocumentFormat):
    """The OpenHCS configuration document (``ConfigDocumentAuthority``)."""

    def render(self, config: object, *, expected_config_type: type, clean_mode: bool) -> str:
        return ConfigDocumentAuthority.render(
            config,
            expected_config_type=expected_config_type,
            clean_mode=clean_mode,
        )

    def from_source(self, source: str, *, expected_config_type: type) -> object:
        return ConfigDocumentAuthority.from_source(
            source,
            expected_config_type=expected_config_type,
        )


class OpenHCSConfigWindow(ConfigWindow):
    """Config windows over OpenHCS configuration documents."""

    document_format: ClassVar[ConfigDocumentFormat] = OpenHCSConfigDocument()

    def window_manager_scope_id(self) -> str | None:
        if self.scope_id is None:
            return None
        return UiStableWindowIdentityDeclaration.window_id_for_manager_scope(self.scope_id)
