"""Build a dataset's compile/run request from its ObjectState."""

from __future__ import annotations

import logging

from objectstate.object_state import ObjectStateRegistry

from openhcs.authoring.session.compilation import (
    DatasetPipelineRequest,
    pipeline_fingerprint,
)
from openhcs.authoring.session.pipelines import PipelineObjectStateBinding
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.dataset_sources.dataset_scopes import DatasetScope
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator

logger = logging.getLogger(__name__)


def dataset_orchestrator(scope_id: str) -> PipelineOrchestrator:
    orchestrator = ObjectStateRegistry.get_object(scope_id)
    if not isinstance(orchestrator, PipelineOrchestrator):
        raise RuntimeError(
            f"No PipelineOrchestrator registered for dataset scope {scope_id!r}."
        )
    return orchestrator


def dataset_pipeline_config(scope_id: str) -> PipelineConfig:
    """The dataset's PipelineConfig from its ObjectState."""

    state = ObjectStateRegistry.get_by_scope(scope_id)
    if state is None:
        raise RuntimeError(f"Dataset scope {scope_id!r} has no ObjectState.")
    return state.to_object(update_delegate=False)


def dataset_pipeline_request(
    scope_id: str,
    global_config: GlobalPipelineConfig,
) -> DatasetPipelineRequest:
    """Snapshot one dataset's pipeline and configuration for submission."""

    scope = DatasetScope.parse(scope_id)
    orchestrator = dataset_orchestrator(scope_id)
    workspace = orchestrator.input_workspace_preparation_result
    if workspace is not None:
        execution_root = str(workspace.execution_plate_path)
        pipeline_path = (
            None if workspace.pipeline_path is None else str(workspace.pipeline_path)
        )
    else:
        if orchestrator.plate_path is None:
            raise RuntimeError(
                f"PipelineOrchestrator for {scope_id!r} has no execution root."
            )
        execution_root = str(orchestrator.plate_path)
        pipeline_path = None
    if pipeline_path is None and orchestrator.selected_pipeline_path is not None:
        pipeline_path = str(orchestrator.selected_pipeline_path)

    steps = FunctionStepTransportAuthority.normalize_pipeline(
        PipelineObjectStateBinding.steps_for_plate(scope_id)
    )
    for step in steps:
        if step.func is None:
            raise AttributeError(
                f"Step '{step.name}' has func=None. "
                "This usually means the pipeline was loaded from a compiled state."
            )
    logger.info(
        "Pipeline snapshot: dataset=%s steps=%d fingerprint=%s",
        scope_id,
        len(steps),
        pipeline_fingerprint(steps),
    )
    return DatasetPipelineRequest(
        scope=scope,
        name=scope.display_name,
        execution_root=execution_root,
        pipeline_path=pipeline_path,
        steps=steps,
        pipeline_config=dataset_pipeline_config(scope_id),
        global_config=global_config,
    )
