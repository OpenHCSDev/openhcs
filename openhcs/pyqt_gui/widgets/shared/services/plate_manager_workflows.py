"""Code-mode application for the dataset manager: a thin client of the session."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from pyqt_reactive.widgets.shared.manager_workflows import ManagerCodeExecutionWorkflow

from openhcs.authoring.session.dataset_document import (
    AllDatasetDocumentScope,
    DatasetDocumentScope,
    apply_dataset_document,
)
from openhcs.ui.shared.plate_manager_code_document import (
    PlateManagerCodeDocumentAuthority,
)

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session


@dataclass(frozen=True, slots=True)
class PlateManagerCodeWorkflow(ManagerCodeExecutionWorkflow):
    """Applies an edited dataset document to the session."""

    workflow_key = "plate_manager"
    session: "Session"
    scope: DatasetDocumentScope = field(default_factory=AllDatasetDocumentScope)

    def migration_namespace(self, code: str, error: Exception) -> dict | None:
        del code, error
        return None

    def apply_namespace(self, namespace) -> bool:
        apply_dataset_document(
            self.session,
            PlateManagerCodeDocumentAuthority.from_namespace(namespace),
            self.scope,
        )
        return True

    def validate_namespace(self, namespace) -> bool:
        PlateManagerCodeDocumentAuthority.from_namespace(namespace)
        return True
