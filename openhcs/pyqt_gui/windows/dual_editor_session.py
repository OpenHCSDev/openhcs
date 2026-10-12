"""What the step editor edits (``StepEdit``) and the family its tabs belong to."""

from __future__ import annotations

import copy
import logging
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any, ClassVar, cast

from objectstate import ObjectState, ObjectStateEditSession
from pyqt_reactive.windows.tabbed_editor_window import EditedObject, EditorTab, SaveRefused

from openhcs.authoring.session.step_scopes import build_step_scope_id
from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.config import SourceBindingsConfig
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.source_binding_context import SourceBindingContext
from openhcs.core.steps.function_step import FunctionSpec, FunctionStep
from openhcs.pyqt_gui.widgets.step_parameter_editor import StepEditorStateRequest

logger = logging.getLogger(__name__)


def _nothing_to_do(*_args: object) -> None:
    """Default for the hooks a caller may leave out."""


class StepEditorTab(EditorTab):
    """A tab of the step editor. Subclass it to add a tab; the window needs no change."""

    @property
    def edit(self) -> StepEdit:
        return cast(StepEdit, self.window.edited)

    def set_step_index(self, index: int) -> None:
        """The step moved to another position in its pipeline."""
        del index

    def pipeline_step_replaced(self, step: FunctionStep) -> None:
        """Another editor replaced the pipeline's step object with ``step``."""
        del step


@dataclass(eq=False)
class StepEdit(EditedObject):
    """One ``FunctionStep`` of a plate's pipeline while it is being edited."""

    tab_family: ClassVar[type[EditorTab]] = StepEditorTab

    #: The step object the pipeline holds; replaced when another editor saves this step.
    pipeline_step: FunctionStep
    plate_scope: str
    orchestrator: Any
    is_new: bool = False
    list_position: int | None = None
    on_save: Callable[[FunctionStep], None] = _nothing_to_do
    before_mutation: Callable[[], None] = _nothing_to_do
    source_bindings: SourceBindingsConfig | None = None
    source_binding_context: SourceBindingContext | None = None
    function_invocation_badge_provider: Callable[[str, int, Callable], str | None] | None = None
    compiled_artifact_inspection_provider: Callable[
        [str], CompiledArtifactInspection | None
    ] = _nothing_to_do
    main_window: Any = None
    #: The clone that is edited, so unsaved changes never reach the pipeline's object.
    step: FunctionStep = field(init=False)
    _scope_id: str = field(init=False)
    _state: ObjectState = field(init=False)

    def __post_init__(self) -> None:
        self.step = copy.deepcopy(self.pipeline_step)
        self._scope_id = build_step_scope_id(self.plate_scope, self.step)
        self._state = StepEditorStateRequest(self._scope_id).resolve()

    @property
    def scope_id(self) -> str:
        return self._scope_id

    @property
    def state(self) -> ObjectState:
        return self._state

    def title(self) -> str:
        name = str(self._state.get_current_values()["name"])
        if self.list_position is not None:
            name = f"{self.list_position + 1}. {name}"
        return f"{'New' if self.is_new else 'Edit'} Step: {name}"

    def save_label(self) -> str:
        return "Create" if self.is_new else "Save"

    def require_mutation_allowed(self) -> None:
        self.before_mutation()

    def object_session(self) -> ObjectStateEditSession[FunctionStep]:
        """The ObjectState edit boundary for this step."""
        return ObjectStateEditSession(
            state_provider=lambda: self._state,
            fallback_object=self.step,
            expected_type=FunctionStep,
        )

    def function_pattern(self) -> FunctionSpec:
        """The function pattern the ObjectState currently holds."""
        return cast(FunctionSpec, self.object_session().parameter_value("func"))

    @staticmethod
    def normalized_function_pattern(pattern: FunctionSpec) -> FunctionSpec:
        return cast(
            FunctionSpec,
            FunctionStepTransportAuthority.normalize_function_spec(pattern),
        )

    def apply_function_pattern(self, pattern: FunctionSpec) -> FunctionSpec:
        """Normalize a function pattern and write it to the ObjectState."""
        normalized = self.normalized_function_pattern(pattern)
        self.object_session().update_parameter("func", normalized)
        return normalized

    def compiled_inspection(self) -> CompiledArtifactInspection | None:
        """The plate's current compiled artifact inspection, if it has been compiled."""
        inspection = self.compiled_artifact_inspection_provider(self.plate_scope)
        if inspection is not None and not isinstance(inspection, CompiledArtifactInspection):
            raise TypeError(
                f"Compiled artifact inspection provider returned {type(inspection).__name__}."
            )
        return inspection

    def save(self) -> FunctionStep:
        saved = self.object_session().to_object(update_delegate=False)
        if not saved.name or not saved.name.strip():
            raise SaveRefused("Step name cannot be empty.")
        self.is_new = False
        self.step = saved
        self.pipeline_step = saved
        self.on_save(saved)
        return saved
