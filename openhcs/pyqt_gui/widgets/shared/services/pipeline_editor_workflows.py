"""Workflow services owned by the pipeline editor widget."""

from __future__ import annotations

import logging
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable, TypeAlias

from objectstate.object_state import ObjectState
from PyQt6.QtWidgets import QFileDialog
from pyqt_reactive.widgets.shared.manager_workflows import (
    ManagerCodeExecutionWorkflow,
)

from openhcs.core.callable_contract import CallableContract
from openhcs.core.debug import (
    DebugCommandType,
    DebugCursor,
    FileManagerDebugSnapshotStore,
)
from openhcs.core.debug_views import DebugViewModel
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps.abstract import AbstractStep
from openhcs.pyqt_gui.widgets.shared.services.pipeline_debug_actions import (
    PipelineDebugActionDeclarationBase,
)
from openhcs.pyqt_gui.windows.debug_inspector_window import DebugInspectorWindow

logger = logging.getLogger(__name__)

TimeTravelDirtyStates: TypeAlias = Iterable[tuple[str, ObjectState]]

if TYPE_CHECKING:
    pass


@dataclass(frozen=True, slots=True)
class FunctionPatternInvocationBadge:
    """GUI badge for one invocation in a FunctionStep function pattern."""

    group_key: str
    position: int
    function_name: str
    is_current_cursor: bool = False
    is_dirty_replay_start: bool = False

    @property
    def text(self) -> str:
        prefix = "▶ " if self.is_current_cursor else ""
        suffix = " *" if self.is_dirty_replay_start else ""
        return f"{prefix}{self.group_key}[{self.position}] {self.function_name}{suffix}"

    @property
    def is_visible(self) -> bool:
        """Only debug-significant invocations need a title badge."""
        return self.is_current_cursor or self.is_dirty_replay_start


@dataclass(frozen=True, slots=True)
class PipelineEditorFunctionPresentation:
    """Owns function-pattern names, preview text, and invocation badges."""

    editor: Any

    def format_func_preview(
        self,
        func,
        state=None,
        *,
        step_index: int | None = None,
    ) -> str | None:
        badges = self.visible_invocation_badges(func, step_index=step_index)
        if badges:
            return "func=" + " | ".join(badge.text for badge in badges)
        if isinstance(func, tuple) and len(func) >= 1:
            return f"func={self.func_name(func)}"
        if isinstance(func, list) and func:
            func_names = [self.func_name(f) for f in func if f is not None]
            return f"func=[{', '.join(func_names)}]"
        if callable(func):
            func_name = CallableContract.from_callable(func).function_name
            return f"func={func_name}"
        if isinstance(func, dict):
            orchestrator = self.editor._get_current_orchestrator()
            metadata_cache = orchestrator.metadata_cache if orchestrator else None
            step = state.to_object(update_delegate=False) if state else None
            grouping_axes = (
                step.processing_config.group_by.grouping_axes()
                if isinstance(step, AbstractStep)
                and step.processing_config.group_by is not None
                else ()
            )
            entries = []
            for key in sorted(func.keys()):
                display_name = None
                if grouping_axes and metadata_cache:
                    display_name = metadata_cache.get_component_metadata(
                        grouping_axes[0], str(key)
                    )
                if display_name is None:
                    display_name = str(key)
                entries.append(f"{display_name}: {self.func_name(func[key])}")
            return f"func={{{', '.join(entries)}}}"
        return None

    def invocation_badges(
        self,
        func,
        *,
        step_index: int | None = None,
    ) -> tuple[FunctionPatternInvocationBadge, ...]:
        if not func:
            return ()
        normalized = normalize_function_pattern(func)
        displayed = (
            self.editor.session.displayed_debug_session(self.editor.current_plate)
            if self.editor.current_plate
            else None
        )
        cursor = None if displayed is None else displayed.cursor
        dirty_cursor = None if displayed is None else displayed.dirty_from_cursor
        return tuple(
            FunctionPatternInvocationBadge(
                group_key=item.key.group_key,
                position=item.key.position,
                function_name=item.key.function_name,
                is_current_cursor=(
                    self._cursor_matches_step_index(cursor, step_index)
                    and cursor.matches_invocation_key_parts(
                        group_key=item.key.group_key,
                        position=item.key.position,
                        function_name=item.key.function_name,
                    )
                    if cursor is not None
                    else False
                ),
                is_dirty_replay_start=(
                    self._cursor_matches_step_index(dirty_cursor, step_index)
                    and dirty_cursor.matches_invocation_key_parts(
                        group_key=item.key.group_key,
                        position=item.key.position,
                        function_name=item.key.function_name,
                    )
                    if dirty_cursor is not None
                    else False
                ),
            )
            for item in normalized.iter_items()
        )

    def visible_invocation_badges(
        self,
        func,
        *,
        step_index: int | None = None,
    ) -> tuple[FunctionPatternInvocationBadge, ...]:
        return tuple(
            badge
            for badge in self.invocation_badges(func, step_index=step_index)
            if badge.is_visible
        )

    def badge_provider(
        self,
        step: AbstractStep,
        *,
        step_index: int,
    ) -> Callable[[str, int, Callable], str | None]:
        badges = {
            (badge.group_key, badge.position, badge.function_name): badge
            for badge in self.invocation_badges(step.func, step_index=step_index)
        }

        def badge_text(group_key: str, position: int, func: Callable) -> str | None:
            badge = badges.get((group_key, position, self.func_name(func)))
            return badge.text if badge is not None and badge.is_visible else None

        return badge_text

    @staticmethod
    def _cursor_matches_step_index(cursor: DebugCursor, step_index: int | None) -> bool:
        return step_index is not None and cursor.step_index == step_index

    def func_name(self, func_entry) -> str:
        if isinstance(func_entry, tuple) and len(func_entry) >= 1:
            return CallableContract.from_callable(func_entry[0]).function_name
        if isinstance(func_entry, list) and func_entry:
            first = self.func_name(func_entry[0])
            if len(func_entry) > 1:
                last = self.func_name(func_entry[-1])
                return f"{first}→{last}"
            return first
        if callable(func_entry):
            return CallableContract.from_callable(func_entry).function_name
        return str(func_entry)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class PipelineEditorDebugWorkflow:
    """Owns debug-toolbar command dispatch and snapshot inspector routing."""

    editor: Any

    def handle_command(self, command) -> None:
        declaration = PipelineDebugActionDeclarationBase.for_command_type(
            command.command_type
        )
        declaration.invoke(self)

    def show_status(self, message: str) -> None:
        """Present one declaration-owned debug status message."""

        self.editor.status_message.emit(message)

    def run_command(
        self,
        command_type: DebugCommandType = DebugCommandType.RUN,
    ) -> None:
        scope_id = self.editor.current_plate
        if not scope_id:
            self.editor.status_message.emit("Select a dataset before running debug mode.")
            return
        session = self.editor.session
        command_label = command_type.value.replace("_", " ")
        self.editor.status_message.emit(f"Submitting debug {command_label} for {scope_id}")
        cursor = self._replay_cursor(command_type)
        session.debug_terminal_summaries.pop(scope_id, None)
        session.start(
            session.run_debug,
            scope_id,
            command_type=command_type,
            pause_step_indices=self.pause_step_indices(),
            start_step_index=0 if cursor is None else cursor.step_index,
            start_after_invocation_key=None if cursor is None else cursor.invocation_key,
        )

    def pause_step_indices(self) -> tuple[int, ...]:
        return tuple(
            index
            for index, step in enumerate(self.editor.displayed_steps)
            if step.debug_pause
        )

    def _replay_cursor(self, command_type: DebugCommandType) -> DebugCursor | None:
        scope_id = self.editor.current_plate
        displayed = self.editor.session.displayed_debug_session(scope_id)
        if (
            command_type is DebugCommandType.RESTART
            and displayed is not None
            and displayed.dirty_from_cursor is not None
        ):
            return displayed.dirty_from_cursor
        if command_type is DebugCommandType.STEP:
            if displayed is not None and displayed.cursor is not None:
                return displayed.cursor
            summary = self.editor.session.debug_terminal_summaries.get(scope_id)
            if summary is not None:
                return summary.cursor
        return None

    def stop_command(self) -> None:
        self.editor.session.stop_execution(True)
        self.editor.status_message.emit("Requested debug execution stop.")

    def show_runtime_inspection(self) -> None:
        active = self.editor.debug_session_context().active_session
        if active is None:
            self.editor.status_message.emit(
                "Runtime inspection requires an active debug session."
            )
            return
        session = self.editor.session

        async def inspect() -> None:
            view_model = await session.debug_runs.inspect_runtime(
                debug_session_id=active.debug_session_id,
            )
            session.main_thread.post(lambda: self._render_runtime_inspection(view_model))

        session.start(inspect)

    def _inspector(self) -> DebugInspectorWindow:
        if self.editor.debug_inspector_window is None:
            self.editor.debug_inspector_window = DebugInspectorWindow(self.editor)
            self.editor.debug_inspector_window.artifact_export_requested.connect(
                self.handle_artifact_export_request
            )
            self.editor.debug_inspector_window.artifact_open_requested.connect(
                self.handle_artifact_open_request
            )
        return self.editor.debug_inspector_window

    def _render_runtime_inspection(self, view_model: DebugViewModel) -> None:
        inspector = self._inspector()
        inspector.set_inspection_view_model(view_model)
        inspector.show()
        inspector.raise_()

    def show_snapshot(self, notification) -> None:
        context = notification.debug_context
        if context.snapshot_store_ref is None or context.snapshot_id is None:
            self.editor.status_message.emit(
                "Debug snapshot event did not include a snapshot store."
            )
            return
        inspector = self._inspector()
        snapshot = notification.snapshot
        if snapshot is not None:
            inspector.set_snapshot(snapshot)
        elif context.snapshot_store_backend is None:
            snapshot = inspector.load_snapshot(
                root_path=context.snapshot_store_ref,
                debug_session_id=context.debug_session_id,
                snapshot_id=context.snapshot_id,
            )
        else:
            snapshot = inspector.load_snapshot_from_store(
                store=FileManagerDebugSnapshotStore(
                    filemanager=self.editor.service_adapter.get_file_manager(),
                    backend=context.snapshot_store_backend,
                    root_path=context.snapshot_store_ref,
                    debug_session_id=context.debug_session_id,
                ),
                snapshot_id=context.snapshot_id,
            )
        self.editor.session.inspect_debug_snapshot(notification, snapshot)
        inspector.show()
        inspector.raise_()
        self.editor.status_message.emit(
            f"Loaded debug snapshot {context.snapshot_id} for "
            f"{notification.progress_event.step_name}"
        )

    def handle_artifact_open_request(self, request) -> None:
        self.editor.status_message.emit(
            "Debug artifact viewer request queued for "
            f"{request.viewer_type.family.display_name}: {request.artifact_ref.name}"
        )

    def handle_artifact_export_request(self, request) -> None:
        scope_id = self.editor.current_plate
        session = self.editor.session
        displayed = session.displayed_debug_session(scope_id) if scope_id else None
        if displayed is None:
            self.editor.status_message.emit(
                "Debug artifact export requires an active debug session."
            )
            return
        export_root = QFileDialog.getExistingDirectory(
            self.editor,
            "Export Debug Artifact",
            str(Path.home()),
        )
        if not export_root:
            return
        session.start(
            session.debug_runs.export_artifact,
            debug_session_id=displayed.debug_session_id,
            artifact_ref=request.artifact_ref,
            export_root=export_root,
            snapshot_store_ref=displayed.snapshot_store_ref,
            snapshot_store_backend=displayed.snapshot_store_backend,
        )


@dataclass(frozen=True, slots=True)
class PipelineEditorCodeWorkflow(ManagerCodeExecutionWorkflow):
    """Applies an edited pipeline document to the current dataset."""

    workflow_key = "pipeline_editor"
    editor: Any

    def migration_namespace(self, code: str, error: Exception) -> dict | None:
        del code, error
        return None

    def apply_namespace(self, namespace: dict) -> bool:
        scope_id = self.editor.current_plate
        if not scope_id:
            raise RuntimeError("Select a dataset before applying a pipeline document.")
        self.editor.session.set_pipeline_document(
            scope_id, PipelineDocumentCodec.from_namespace(namespace)
        )
        return True

    def validate_namespace(self, namespace: dict) -> bool:
        try:
            PipelineDocumentCodec.from_namespace(namespace)
        except (TypeError, ValueError):
            return False
        return True
