"""Shared helpers for resolving per-plate pipeline configuration."""

from __future__ import annotations


def resolve_pipeline_config_for_plate(host, plate_path: str):
    """Resolve per-plate PipelineConfig from canonical sources.

    Resolution order:
    1) ObjectState scope (authoritative editable config)
    2) live orchestrator object
    3) host.plate_configs fallback
    4) default PipelineConfig()
    """
    from objectstate import ObjectStateRegistry
    from openhcs.core.config import PipelineConfig

    state = ObjectStateRegistry.get_by_scope(plate_path)
    if state is not None:
        return state.to_object(update_delegate=False)

    orchestrator = ObjectStateRegistry.get_object(plate_path)
    if orchestrator is not None:
        return orchestrator.pipeline_config

    saved_config = host.plate_configs.get(str(plate_path))
    if saved_config:
        return saved_config

    return PipelineConfig()
