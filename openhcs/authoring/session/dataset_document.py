"""The datasets as one Python document: render it, and apply an edited one.

A document covers either the selected datasets (applying it upserts them and
leaves the rest alone) or all of them (applying it makes the dataset list
exactly the document's). Each scope is one :class:`DatasetDocumentScope`.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta
from objectstate.object_state import ObjectState, ObjectStateRegistry
from objectstate.value_semantics import semantic_values_equal

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.selection import SelectedAllSelectionMode, SelectedScopeIdsCarrier
from openhcs.serialization.pycodify_formatters import LazyDataclassFieldEmissionState
from openhcs.ui.shared.plate_manager_code_document import (
    PlateManagerCodeDocumentAuthority,
    PlateManagerOrchestratorCodePayload,
)
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session


@dataclass(frozen=True, kw_only=True, slots=True)
class DatasetDocumentScope(ABC, metaclass=AutoRegisterMeta):
    """Which datasets a document covers, and what applying it may change."""

    __registry_key__ = "mode"
    __skip_if_no_key__ = True

    mode: ClassVar[SelectedAllSelectionMode | None] = None
    selected_scope_ids: tuple[str, ...] = ()

    @classmethod
    def from_carrier(
        cls,
        carrier: SelectedScopeIdsCarrier,
        *,
        default: SelectedAllSelectionMode = SelectedAllSelectionMode.SELECTED,
    ) -> "DatasetDocumentScope":
        mode = SelectedAllSelectionMode(carrier.resolved_selection_mode(default))
        return cls.__registry__[mode](selected_scope_ids=tuple(carrier.selected_scope_ids))

    def require_payload_scope(self, scope_ids: tuple[str, ...]) -> None:
        if self.selected_scope_ids and frozenset(scope_ids) != frozenset(
            self.selected_scope_ids
        ):
            raise ValueError(
                "Selected-scope code documents must keep their selected dataset "
                "scope ids. Read the document again to change its scope."
            )

    @abstractmethod
    def commits_global_draft(self, state: ObjectState | None) -> bool:
        """Whether applying also commits an unchanged global draft."""

    @abstractmethod
    def synchronize(
        self, session: "Session", payload: PlateManagerOrchestratorCodePayload
    ) -> None:
        """Make the dataset list agree with the document within this scope."""


class SelectedDatasetDocumentScope(DatasetDocumentScope):
    """Upsert the selected datasets; keep every other dataset."""

    mode = SelectedAllSelectionMode.SELECTED

    def commits_global_draft(self, state: ObjectState | None) -> bool:
        return False

    def synchronize(self, session, payload) -> None:
        self.require_payload_scope(payload.plate_paths)
        session.ensure_datasets(payload.plate_paths)


class AllDatasetDocumentScope(DatasetDocumentScope):
    """Make the dataset list exactly the document's."""

    mode = SelectedAllSelectionMode.ALL

    def commits_global_draft(self, state: ObjectState | None) -> bool:
        return bool(state and state.dirty_fields)

    def synchronize(self, session, payload) -> None:
        session.sync_datasets(payload.plate_paths)


@dataclass(frozen=True, slots=True)
class DatasetDocument(SelectedScopeIdsCarrier):
    """Rendered dataset source plus the payload that produced it."""

    source: str
    payload: PlateManagerOrchestratorCodePayload
    clean_mode: bool = True


def live_global_config(session: "Session") -> GlobalPipelineConfig:
    state = ObjectStateRegistry.get_by_scope("")
    if state is None:
        return session.global_config
    return state.to_object(update_delegate=False)


def authored_pipeline_config(scope_id: str) -> PipelineConfig:
    """The dataset's PipelineConfig with only its authored fields."""

    state = ObjectStateRegistry.get_by_scope(scope_id)
    if state is None or ObjectStateRegistry.get_object(scope_id) is None:
        raise ValueError(f"Dataset {scope_id!r} has no registered orchestrator ObjectState.")
    config = state.to_object(update_delegate=False)
    if not isinstance(config, PipelineConfig):
        raise TypeError("A dataset ObjectState must rebuild a PipelineConfig.")
    return LazyDataclassFieldEmissionState.retain_only_authored_paths(
        config, state.signature_diff_fields
    )


def render_dataset_document(
    session: "Session",
    scope_ids: tuple[str, ...],
    *,
    selection_mode: SelectedAllSelectionMode,
) -> DatasetDocument:
    payload = PlateManagerCodeDocumentAuthority.from_values(
        plate_paths=list(scope_ids),
        global_pipeline_config=live_global_config(session),
        per_plate_configs={
            scope_id: authored_pipeline_config(scope_id) for scope_id in scope_ids
        },
        pipeline_data={
            scope_id: list(session.pipeline_steps(scope_id)) for scope_id in scope_ids
        },
    )
    return DatasetDocument(
        source=PlateManagerCodeDocumentAuthority.render(payload),
        payload=payload,
        selection_mode=selection_mode.value,
        selected_scope_ids=tuple(scope_ids),
    )


def apply_dataset_document(
    session: "Session",
    payload: PlateManagerOrchestratorCodePayload,
    scope: DatasetDocumentScope,
) -> None:
    """Apply an edited document; change only what differs from the session."""

    scope.require_payload_scope(payload.plate_paths)
    global_changed = scope.commits_global_draft(
        ObjectStateRegistry.get_by_scope("")
    ) or not semantic_values_equal(
        live_global_config(session), payload.global_pipeline_config
    )
    changed_configs = {
        scope_id: config
        for scope_id, config in payload.per_plate_configs.items()
        if (state := ObjectStateRegistry.get_by_scope(scope_id)) is None
        or state.dirty_fields
        or not semantic_values_equal(authored_pipeline_config(scope_id), config)
    }
    changed_pipelines = {}
    for scope_id, submitted in payload.pipeline_data.items():
        current = (
            session.pipeline_steps(scope_id)
            if ObjectStateRegistry.get_by_scope(
                PipelineScopeIdentity.from_plate_scope(scope_id).scope_id
            )
            is not None
            else []
        )
        if len(current) != len(submitted) or not all(
            existing.same_declaration(new) for existing, new in zip(current, submitted)
        ):
            changed_pipelines[scope_id] = submitted
    if global_changed:
        session.require_definition_mutation_allowed()
    for scope_id in changed_configs.keys() | changed_pipelines.keys():
        session.require_definition_mutation_allowed(scope_id)
    scope.synchronize(session, payload)
    if global_changed:
        session.apply_global_config(payload.global_pipeline_config)
    session.apply_dataset_configs(changed_configs)
    for scope_id, steps in changed_pipelines.items():
        session.set_pipeline(scope_id, list(steps))
