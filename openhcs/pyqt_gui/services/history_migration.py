"""Upgrade legacy desktop histories through their declared workflow ownership."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import is_dataclass, replace
from typing import Any

from objectstate.construction_binding import StateConstructionBinding
from objectstate.history_migration import HistoryMigration
from objectstate.lazy_factory import replace_raw
from objectstate.object_state import ObjectState
from pyqt_reactive.services.function_pattern_code_document import (
    FunctionPatternCodeDocumentService,
    FunctionPatternValue,
)
from pyqt_reactive.services.pattern_data_manager import (
    FUNC_EDITOR_PATTERN_TOKENS_META_KEY,
)
from pyqt_reactive.services.scope_token_service import ScopeTokenService

from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.services.pipeline_object_state_binding import (
    PipelineEditorStateRoot,
)
from openhcs.pyqt_gui.services.step_scope_identity import StepEditorScope
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity


class DesktopHistoryUpgrade(HistoryMigration):
    """Recover supported legacy scopes from actual stored step declarations.

    A fresh source document cannot establish historical function occurrence
    identity. Legacy editor membership, step function patterns and their token
    metadata can. Unknown scopes or missing historical declarations are refused;
    the desktop restart owner retains the original recovery files.
    """

    def migrate(
        self,
        document: dict[str, Any],
        constructions: Mapping[str, StateConstructionBinding],
    ) -> dict[str, Any]:
        if "format_version" in document and document["format_version"] != 1:
            raise ValueError(
                "Desktop history upgrade requires a legacy version 1 document."
            )
        for snapshot in document["snapshots"].values():
            states = snapshot["states"]
            historical = self._pipeline_constructions(states, constructions)
            for scope, data in states.items():
                if scope in historical:
                    data["construction"] = historical[scope]
                    continue
                if scope not in constructions:
                    raise ValueError(
                        f"Legacy history has no declared construction for scope {scope!r}."
                    )
                binding = constructions[scope]
                if not is_dataclass(binding.target) or isinstance(binding.target, type):
                    raise ValueError(
                        f"Legacy history lacks historical declaration ownership at {scope!r}."
                    )
                data["construction"] = replace(
                    binding,
                    target=replace_raw(
                        binding.target,
                        **self._top_level_parameters(data["saved_parameters"]),
                    ),
                )
        document["format_version"] = 2
        return document

    @classmethod
    def _pipeline_constructions(
        cls,
        states: Mapping[str, dict[str, Any]],
        constructions: Mapping[str, StateConstructionBinding],
    ) -> dict[str, StateConstructionBinding]:
        result: dict[str, StateConstructionBinding] = {}
        for scope, data in states.items():
            if not PipelineScopeIdentity.matches(scope):
                continue
            if scope not in constructions:
                raise ValueError(
                    f"Legacy pipeline has no current lifecycle binding at {scope!r}."
                )
            editor = PipelineEditorStateRoot(**data["parameters"])
            editor_binding = constructions[scope]
            result[scope] = replace(editor_binding, target=editor)
            identity = PipelineScopeIdentity.from_scope_id(scope)
            for step_scope in editor.step_scope_ids:
                if step_scope not in states:
                    raise ValueError(
                        f"Legacy pipeline declares missing historical step {step_scope!r}."
                    )
                step_identity = StepEditorScope.parse(step_scope)
                if (
                    step_identity.is_function_scope
                    or step_identity.plate_scope != identity.plate_scope
                ):
                    raise ValueError(
                        f"Legacy pipeline contains an invalid step scope {step_scope!r}."
                    )
                step_data = states[step_scope]
                step = FunctionStep(
                    **cls._top_level_parameters(step_data["parameters"])
                )
                ScopeTokenService.restore_object_token(
                    step, step_identity.step_token.raw
                )
                step_state = ObjectState(step, scope_id=step_scope)
                result[step_scope] = replace(
                    step_state.construction_binding(),
                    parent_scope=editor_binding.parent_scope,
                )
                entries = FunctionPatternCodeDocumentService.iter_tokenized_entries(
                    step.func,
                    step_data["meta"][FUNC_EDITOR_PATTERN_TOKENS_META_KEY],
                )
                for entry in entries:
                    if not entry.token:
                        raise ValueError(
                            f"Legacy function occurrence lacks a token in {step_scope!r}."
                        )
                    child_scope = f"{step_scope}::{entry.token}"
                    if child_scope not in states or child_scope in result:
                        raise ValueError(
                            f"Legacy function occurrence is missing or ambiguous at {child_scope!r}."
                        )
                    result[child_scope] = (
                        FunctionPatternCodeDocumentService.create_function_state(
                            scope_id=child_scope,
                            parent_state=step_state,
                            entry=FunctionPatternValue(entry.func, entry.kwargs),
                        ).construction_binding()
                    )
        return result

    @staticmethod
    def _top_level_parameters(parameters: Mapping[str, Any]) -> dict[str, Any]:
        """Preserve typed raw containers; extraction owns their nested structure."""
        return {name: value for name, value in parameters.items() if "." not in name}
