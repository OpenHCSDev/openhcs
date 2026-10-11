"""Nominal declarations for PipelineEditor debug-session actions."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.agent.dto.common import AgentError
from python_introspect import to_jsonable

from openhcs.core.debug import DebugCommand, DebugCommandType
from openhcs.core.debug import (
    ChooseSourceGroupDebugCommand,
    RandomSourceGroupDebugCommand,
    RestartDebugCommand,
    RunDebugCommand,
    RunToPauseDebugCommand,
    StepDebugCommand,
    StopDebugCommand,
    ToggleDebugCommand,
)

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.debug_toolbar import DebugToolbarWidget
    from openhcs.core.debug_session_projection import DebugSessionProjectionContext
    from openhcs.pyqt_gui.widgets.shared.services.pipeline_editor_workflows import (
        PipelineEditorDebugWorkflow,
    )


@dataclass(frozen=True, slots=True)
class DebugActionDisabledReason:
    """Agent/UI facing disabled reason for one debug action."""

    code: str
    message: str
    hint: str

    def as_agent_error(self) -> AgentError:
        return AgentError(code=self.code, message=self.message, hint=self.hint)


class DebugToolbarPlacement(ABC, metaclass=AutoRegisterMeta):
    """Where the debug toolbar shows an action; ``name`` is its UI-bridge spelling."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[DebugToolbarPlacement]]] = {}

    name: ClassVar[str | None] = None
    shown: ClassVar[bool] = True
    """Actions placed here get a toolbar button."""
    panel_order: ClassVar[int] = 0
    """Position of this placement's button panel in the toolbar."""

    @classmethod
    def panels(cls) -> tuple[type[DebugToolbarPlacement], ...]:
        """The placements the toolbar renders as button panels, in order."""

        return tuple(
            sorted(
                (placement for placement in cls.__registry__.values() if placement.shown),
                key=lambda placement: placement.panel_order,
            )
        )


class PrimaryPanel(DebugToolbarPlacement):
    name = "primary"
    panel_order = 0


class SessionPanel(DebugToolbarPlacement):
    name = "session"
    panel_order = 1


class InspectorPanel(DebugToolbarPlacement):
    name = "inspector"
    panel_order = 2


class OffToolbar(DebugToolbarPlacement):
    """Actions invoked through the editor or the UI bridge, without a button."""

    name = "hidden"
    shown = False


class PipelineDebugActionDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """Single semantic owner for one PipelineEditor debug action."""

    __registry__: ClassVar[
        dict[
            type[DebugCommandType] | str,
            type[PipelineDebugActionDeclarationBase],
        ]
    ] = {}
    __registry_key__ = "identity"
    __skip_if_no_key__ = True

    identity: ClassVar[type[DebugCommandType] | str | None] = None
    """The debug command this action sends, or an auxiliary action's id."""
    toolbar_placement: ClassVar[type[DebugToolbarPlacement]] = OffToolbar
    toolbar_order: ClassVar[int] = 0
    label: ClassVar[str]
    tooltip: ClassVar[str]
    side_effects: ClassVar[tuple[str, ...]] = ("starts_or_controls_debug_execution",)
    confirmation_required: ClassVar[bool] = True
    requires_active_debug_session: ClassVar[bool] = False
    requires_active_or_pending_execution: ClassVar[bool] = False
    enabled_during_pending_execution: ClassVar[bool] = False

    @classmethod
    def action_id(cls) -> str:
        return to_jsonable(cls.require_identity())

    @classmethod
    def require_identity(cls) -> type[DebugCommandType] | str:
        if cls.identity is None:
            raise ValueError(
                f"{cls.__name__} does not declare a debug action identity."
            )
        return cls.identity

    @classmethod
    def is_toolbar_action(cls) -> bool:
        return cls.toolbar_placement.shown

    @classmethod
    def toolbar_actions(cls) -> tuple[type[PipelineDebugActionDeclarationBase], ...]:
        return tuple(
            sorted(
                (
                    declaration
                    for declaration in cls.__registry__.values()
                    if declaration.is_toolbar_action()
                ),
                key=lambda declaration: (
                    declaration.toolbar_placement.panel_order,
                    declaration.toolbar_order,
                    declaration.action_id(),
                ),
            )
        )

    @classmethod
    def for_action_id(
        cls, action_id: str
    ) -> type[PipelineDebugActionDeclarationBase]:
        for declaration in cls.__registry__.values():
            if declaration.action_id() == action_id:
                return declaration
        raise ValueError(f"Unknown PipelineEditor debug action: {action_id!r}")

    @classmethod
    def for_command_type(
        cls,
        command_type: type[DebugCommandType],
    ) -> type[PipelineDebugCommandActionDeclaration]:
        declaration = cls.__registry__.get(command_type)
        if declaration is None:
            raise ValueError(f"Unhandled debug command route: {command_type.name}")
        if not issubclass(declaration, PipelineDebugCommandActionDeclaration):
            raise TypeError(
                f"Debug action {command_type.name!r} is not a command declaration."
            )
        return declaration

    @classmethod
    def label_for(cls, context: "DebugSessionProjectionContext") -> str:
        del context
        return cls.label

    @classmethod
    def tooltip_for(cls, context: "DebugSessionProjectionContext") -> str:
        del context
        return cls.tooltip

    @classmethod
    def availability_override(
        cls,
        context: "DebugSessionProjectionContext",
    ) -> DebugActionDisabledReason | None:
        del context
        return None

    @classmethod
    @abstractmethod
    def invoke(cls, workflow: "PipelineEditorDebugWorkflow") -> None:
        """Invoke this action through the nominal editor workflow."""

    @classmethod
    @abstractmethod
    def emit_from(cls, toolbar: "DebugToolbarWidget") -> None:
        """Emit this action's toolbar signal."""


class PipelineDebugCommandActionDeclaration(PipelineDebugActionDeclarationBase):
    """Debug action backed by a core DebugCommandType."""

    identity: ClassVar[type[DebugCommandType] | None] = None

    @classmethod
    def command_type(cls) -> type[DebugCommandType]:
        return cls.require_identity()

    @classmethod
    def invoke(cls, workflow: "PipelineEditorDebugWorkflow") -> None:
        workflow.run_command(cls.command_type())

    @classmethod
    def emit_from(cls, toolbar: "DebugToolbarWidget") -> None:
        toolbar.command_requested.emit(DebugCommand(cls.command_type()))


class PipelineDebugAuxiliaryActionDeclaration(PipelineDebugActionDeclarationBase):
    """Debug action owned by the toolbar but not represented by DebugCommandType."""

    identity: ClassVar[str | None] = None
    side_effects: ClassVar[tuple[str, ...]] = ("opens_debug_runtime_inspector",)
    confirmation_required: ClassVar[bool] = False

    @classmethod
    def invoke(cls, workflow: "PipelineEditorDebugWorkflow") -> None:
        workflow.show_runtime_inspection()

    @classmethod
    def emit_from(cls, toolbar: "DebugToolbarWidget") -> None:
        toolbar.runtime_inspection_requested.emit()


class ToggleDebugModeAction(PipelineDebugCommandActionDeclaration):
    identity = ToggleDebugCommand
    label = "Debug"
    tooltip = "Debug toolbar active. Use Debug, Step, Pause, Restart, or Inspect."

    @classmethod
    def invoke(cls, workflow: "PipelineEditorDebugWorkflow") -> None:
        workflow.show_status(cls.tooltip)


class StartOrContinueDebugAction(PipelineDebugCommandActionDeclaration):
    identity = RunDebugCommand
    toolbar_placement = PrimaryPanel
    toolbar_order = 10
    label = "Debug"
    tooltip = "Start or continue debug execution for the selected plate"

    @classmethod
    def label_for(cls, context: "DebugSessionProjectionContext") -> str:
        if context.active_session is not None:
            return "Continue"
        target = context.target
        if target is not None and target.initialized and target.compiled:
            return "Start Debug"
        return cls.label


class StepDebugAction(PipelineDebugCommandActionDeclaration):
    identity = StepDebugCommand
    toolbar_placement = PrimaryPanel
    toolbar_order = 20
    label = "Step"
    tooltip = "Run one debug step"


class RunToPauseDebugAction(PipelineDebugCommandActionDeclaration):
    identity = RunToPauseDebugCommand
    toolbar_placement = PrimaryPanel
    toolbar_order = 30
    label = "Run to Pause"
    tooltip = "Run until the next pause marker"

    @classmethod
    def availability_override(
        cls,
        context: "DebugSessionProjectionContext",
    ) -> DebugActionDisabledReason | None:
        if not context.pause_boundaries.has_pause_boundaries:
            return DebugActionDisabledReason(
                code="debug_pause_boundary_required",
                message="Run to Pause requires at least one debug-pause step.",
                hint=(
                    "Enable debug_pause on a pipeline step before invoking "
                    "Run to Pause."
                ),
            )
        return None


class RestartDebugAction(PipelineDebugCommandActionDeclaration):
    identity = RestartDebugCommand
    toolbar_placement = SessionPanel
    toolbar_order = 40
    label = "Restart"
    tooltip = "Restart the current debug session"
    requires_active_debug_session = True


class InspectRuntimeValuesAction(PipelineDebugAuxiliaryActionDeclaration):
    identity = "runtime_values"
    toolbar_placement = InspectorPanel
    toolbar_order = 10
    label = "Inspect Runtime"
    tooltip = "Inspect live runtime values for the paused debug worker"
    requires_active_debug_session = True


class ChooseSourceGroupDebugAction(PipelineDebugCommandActionDeclaration):
    identity = ChooseSourceGroupDebugCommand
    toolbar_placement = SessionPanel
    toolbar_order = 10
    label = "Choose source group"
    tooltip = "Choose a well/image set for debug execution"


class StopDebugSessionAction(PipelineDebugCommandActionDeclaration):
    identity = StopDebugCommand
    toolbar_placement = SessionPanel
    toolbar_order = 20
    label = "Stop debug session"
    tooltip = "Stop the active debug execution"
    requires_active_or_pending_execution = True
    enabled_during_pending_execution = True

    @classmethod
    def invoke(cls, workflow: "PipelineEditorDebugWorkflow") -> None:
        workflow.stop_command()


class RandomSourceGroupDebugAction(PipelineDebugCommandActionDeclaration):
    identity = RandomSourceGroupDebugCommand
    label = "Random source group"
    tooltip = "Choose a random well/image set for debug execution"


__all__ = (
    "ChooseSourceGroupDebugAction",
    "DebugActionDisabledReason",
    "DebugToolbarPlacement",
    "InspectRuntimeValuesAction",
    "PipelineDebugActionDeclarationBase",
    "PipelineDebugAuxiliaryActionDeclaration",
    "PipelineDebugCommandActionDeclaration",
    "RandomSourceGroupDebugAction",
    "RestartDebugAction",
    "RunToPauseDebugAction",
    "StartOrContinueDebugAction",
    "StepDebugAction",
    "StopDebugSessionAction",
    "ToggleDebugModeAction",
)
