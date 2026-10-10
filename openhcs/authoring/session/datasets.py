"""The session's dataset list, held in one root ObjectState."""

from __future__ import annotations

from dataclasses import dataclass

from objectstate.collection_containers import RootState
from objectstate.object_state import ObjectState, ObjectStateRegistry

from openhcs.core.dataset_sources.dataset_scopes import DatasetScope

# "" is the GlobalPipelineConfig scope; the dataset list has its own.
DATASET_LIST_SCOPE_ID = "__plates__"
DATASET_LIST_PARAMETER = "orchestrator_scope_ids"


@dataclass(frozen=True, slots=True)
class DatasetRow:
    """One visible dataset row."""

    scope: DatasetScope

    @classmethod
    def of(cls, scope_id: str) -> "DatasetRow":
        return cls(DatasetScope.parse(scope_id))

    @property
    def scope_id(self) -> str:
        return self.scope.scope_id

    @property
    def name(self) -> str:
        return self.scope.display_name

    @property
    def root(self) -> str:
        return str(self.scope.root)

    @property
    def pipeline_path(self) -> str | None:
        path = self.scope.pipeline_path
        return None if path is None else str(path)


def dataset_list_state() -> ObjectState:
    """The root ObjectState listing every dataset scope, registered on first use."""

    state = ObjectStateRegistry.get_by_scope(DATASET_LIST_SCOPE_ID)
    if state is None:
        state = ObjectState(object_instance=RootState(), scope_id=DATASET_LIST_SCOPE_ID)
        ObjectStateRegistry.register(state, _skip_snapshot=True)
    return state


def dataset_scope_ids(state: ObjectState | None = None) -> list[str]:
    """Dataset scope ids in list order."""

    root = dataset_list_state() if state is None else state
    stored = root.parameters.get(DATASET_LIST_PARAMETER)
    return [] if stored is None else [str(scope_id) for scope_id in stored]


def write_dataset_scope_ids(scope_ids: list[str]) -> None:
    dataset_list_state().update_parameter(DATASET_LIST_PARAMETER, list(scope_ids))
