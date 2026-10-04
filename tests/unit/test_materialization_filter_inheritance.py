from pathlib import Path
from types import SimpleNamespace

from objectstate import ObjectState
from objectstate.lazy_factory import ensure_global_config_context
from objectstate.object_state_registry import ObjectStateRegistry
from openhcs.constants.constants import Backend
from openhcs.constants.input_source import InputSource
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    MaterializedOutputPlan,
)
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyStepMaterializationConfig,
    LazyWellFilterConfig,
    MaterializationBackend,
    PipelineConfig,
    VFSConfig,
)
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.pipeline.materialization_flag_planner import (
    MaterializationFlagPlanner,
)
from openhcs.core.pipeline.path_planner import PathPlannerMaterializationStage
from openhcs.core.steps.function_step import FunctionStep


def _identity(image):
    return image


def _resolved_checkpoint(
    plate_path: Path,
    *,
    checkpoint_filter: str | None = None,
):
    pipeline_config = PipelineConfig(
        well_filter_config=LazyWellFilterConfig(well_filter="A01"),
        path_planning_config=LazyPathPlanningConfig(well_filter=0),
    )
    orchestrator = SimpleNamespace(
        plate_path=plate_path,
        pipeline_config=pipeline_config,
        get_component_keys=lambda _component: ["A01", "B02"],
        create_context=lambda axis_id, *, resolved_config: SimpleNamespace(
            axis_id=axis_id,
            step_axis_filters={},
        ),
    )
    pipeline = [
        FunctionStep(
            func=_identity,
            name="checkpoint",
            step_materialization_config=LazyStepMaterializationConfig(
                enabled=True,
                well_filter=checkpoint_filter,
            ),
        )
    ]
    resolved = PipelineCompiler._resolve_pipeline_once(orchestrator, pipeline)
    resolved_config, _provenance = ObjectState.resolve_saved_object(pipeline_config)
    filters = PipelineCompiler._resolve_global_step_axis_filters(
        orchestrator, resolved, resolved_config
    )
    return orchestrator, resolved_config, resolved, filters


def test_path_zero_keeps_inherited_step_checkpoint_independent(tmp_path) -> None:
    ObjectStateRegistry.clear()
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    orchestrator, effective_config, resolved, filters = _resolved_checkpoint(
        tmp_path / "plate"
    )

    snapshot = resolved.steps[0]
    checkpoint_config = snapshot.step_materialization_config
    assert checkpoint_config.well_filter == 0
    assert filters[0].allows(checkpoint_config, "A01")
    assert not filters[0].allows(checkpoint_config, "B02")

    checkpoint_dir = tmp_path / "checkpoint"
    materialization_stage = PathPlannerMaterializationStage(
        SimpleNamespace(
            ctx=SimpleNamespace(axis_id="A01", step_axis_filters=filters),
            paths=SimpleNamespace(
                build_output_path=lambda _config: checkpoint_dir,
            ),
        )
    )
    assert (
        materialization_stage.materialized_output_dir_for_step(snapshot, 0)
        == checkpoint_dir
    )

    plan = CompiledStepPlan(
        step_index=0,
        step_name="checkpoint",
        step_type="FunctionStep",
        axis_id="A01",
        materialized_output=MaterializedOutputPlan(
            output_dir=checkpoint_dir,
            backend=Backend.MEMORY.value,
            plate_root=str(tmp_path),
            sub_dir="checkpoints",
            analysis_results_dir=str(tmp_path / "checkpoint_results"),
        ),
    )
    context = SimpleNamespace(axis_id="A01", step_plans=[plan])
    MaterializationFlagPlanner.prepare_pipeline_flags(
        context,
        [
            SimpleNamespace(
                processing_config=SimpleNamespace(
                    input_source=InputSource.PREVIOUS_STEP,
                )
            )
        ],
        plate_path=orchestrator.plate_path,
        pipeline_config=SimpleNamespace(
            vfs_config=VFSConfig(
                read_backend=Backend.DISK,
                materialization_backend=MaterializationBackend.DISK,
            ),
            path_planning_config=effective_config.path_planning_config,
        ),
        available_axis_values=("A01", "B02"),
    )

    assert plan.write_backend == Backend.MEMORY.value
    assert plan.materialized_output.backend == Backend.DISK.value


def test_explicit_checkpoint_filter_overrides_inherited_workload(tmp_path) -> None:
    ObjectStateRegistry.clear()
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    orchestrator, _effective_config, resolved, filters = _resolved_checkpoint(
        tmp_path / "plate",
        checkpoint_filter="B02",
    )

    checkpoint_config = resolved.steps[0].step_materialization_config
    assert checkpoint_config.well_filter == "B02"
    assert not filters[0].allows(checkpoint_config, "A01")
    assert filters[0].allows(checkpoint_config, "B02")
