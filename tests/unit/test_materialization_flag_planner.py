from pathlib import Path
from types import SimpleNamespace

from openhcs.constants.constants import Backend
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ObjectLabelsArtifactType,
    MeasurementsArtifactType,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import (
    MaterializationBackend,
    PathPlanningConfig,
    VFSConfig,
)
from openhcs.core.pipeline.materialization_flag_planner import (
    MaterializationFlagPlanner,
)
from openhcs.processing.materialization import MaterializationSpec, ROIOptions


def _pipeline_config(
    *,
    path_planning_config: PathPlanningConfig = PathPlanningConfig(),
) -> SimpleNamespace:
    return SimpleNamespace(
        vfs_config=VFSConfig(
            read_backend=Backend.DISK,
            materialization_backend=MaterializationBackend.DISK,
        ),
        path_planning_config=path_planning_config,
    )


def _step(input_source: InputSource = InputSource.PREVIOUS_STEP) -> SimpleNamespace:
    return SimpleNamespace(processing_config=SimpleNamespace(input_source=input_source))


def test_measurement_tail_materializes_previous_image_step() -> None:
    context = SimpleNamespace(
        axis_id="A01",
        step_plans=[
            CompiledStepPlan(0, "image", "FunctionStep", "A01"),
            CompiledStepPlan(
                1,
                "measure",
                "FunctionStep",
                "A01",
                artifact_outputs={
                    plan.ref(): plan
                    for plan in (
                        ArtifactOutputPlan(
                            "measurements",
                            "/memory/measurements.pkl",
                            MeasurementsArtifactType,
                        ),
                    )
                },
            ),
        ],
    )

    MaterializationFlagPlanner(
        pipeline_config=_pipeline_config(),
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate"),
        available_axis_values=(context.axis_id,),
    ).prepare_pipeline_flags(context, [_step(), _step()])

    assert context.step_plans[0].write_backend == Backend.DISK.value
    assert context.step_plans[1].write_backend == Backend.MEMORY.value


def test_final_image_artifact_step_materializes_images() -> None:
    context = SimpleNamespace(
        axis_id="A01",
        step_plans=[
            CompiledStepPlan(
                0,
                "segment",
                "FunctionStep",
                "A01",
                artifact_outputs={
                    plan.ref(): plan
                    for plan in (
                        ArtifactOutputPlan(
                            "labels",
                            "/memory/labels.pkl",
                            ObjectLabelsArtifactType,
                            materialization=MaterializationSpec(ROIOptions()),
                        ),
                    )
                },
            )
        ],
    )

    MaterializationFlagPlanner(
        pipeline_config=_pipeline_config(),
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate"),
        available_axis_values=(context.axis_id,),
    ).prepare_pipeline_flags(context, [_step()])

    assert context.step_plans[0].write_backend == Backend.DISK.value


def test_final_image_artifact_step_honors_no_materialization_policy() -> None:
    context = SimpleNamespace(
        axis_id="A01",
        step_plans=[
            CompiledStepPlan(
                0,
                "segment",
                "FunctionStep",
                "A01",
                artifact_outputs={
                    plan.ref(): plan
                    for plan in (
                        ArtifactOutputPlan(
                            "labels",
                            "/memory/labels.pkl",
                            ObjectLabelsArtifactType,
                            materialization=None,
                        ),
                    )
                },
            )
        ],
    )

    MaterializationFlagPlanner(
        pipeline_config=_pipeline_config(),
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate"),
        available_axis_values=(context.axis_id,),
    ).prepare_pipeline_flags(context, [_step()])

    assert context.step_plans[0].write_backend == Backend.MEMORY.value


def test_final_uncontracted_step_preserves_legacy_image_materialization() -> None:
    context = SimpleNamespace(
        axis_id="A01",
        step_plans=[CompiledStepPlan(0, "process", "FunctionStep", "A01")],
    )

    MaterializationFlagPlanner(
        pipeline_config=_pipeline_config(),
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate"),
        available_axis_values=(context.axis_id,),
    ).prepare_pipeline_flags(context, [_step()])

    assert context.step_plans[0].write_backend == Backend.DISK.value


def test_path_planning_zero_keeps_final_main_flow_runtime_only() -> None:
    context = SimpleNamespace(
        axis_id="B03",
        step_plans=[CompiledStepPlan(0, "inspect", "FunctionStep", "B03")],
    )

    MaterializationFlagPlanner(
        pipeline_config=_pipeline_config(
            path_planning_config=PathPlanningConfig(well_filter=0)
        ),
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate"),
        available_axis_values=("A01", "B03"),
    ).prepare_pipeline_flags(context, [_step()])

    assert context.step_plans[0].write_backend == Backend.MEMORY.value


def test_path_planning_filter_materializes_only_selected_axis() -> None:
    contexts = {
        axis_id: SimpleNamespace(
            axis_id=axis_id,
            step_plans=[CompiledStepPlan(0, "inspect", "FunctionStep", axis_id)],
        )
        for axis_id in ("A01", "B03")
    }
    pipeline_config = _pipeline_config(
        path_planning_config=PathPlanningConfig(well_filter="B03"),
    )

    for context in contexts.values():
        MaterializationFlagPlanner(
            pipeline_config=pipeline_config,
            microscope_handler=SimpleNamespace(),
            filemanager=object(),
            input_dir=Path("/plate"),
            available_axis_values=("A01", "B03"),
        ).prepare_pipeline_flags(context, [_step()])

    assert contexts["A01"].step_plans[0].write_backend == Backend.MEMORY.value
    assert contexts["B03"].step_plans[0].write_backend == Backend.DISK.value
    assert contexts["A01"].step_plans[0].main_flow_axis_persistence_enabled is False
    assert contexts["B03"].step_plans[0].main_flow_axis_persistence_enabled is True


def test_auto_backend_admission_is_shared_and_new_submission_is_fresh():
    requests = []
    source_backend = "virtual_workspace"
    filemanager = object()
    input_dir = Path("/plate/images")

    def primary_backend(path, manager):
        requests.append((path, manager))
        return source_backend

    handler = SimpleNamespace(get_primary_backend=primary_backend)
    config = _pipeline_config()
    config.vfs_config = VFSConfig(
        read_backend=Backend.AUTO,
        materialization_backend=MaterializationBackend.AUTO,
    )

    def new_submission():
        return MaterializationFlagPlanner(
            pipeline_config=config,
            microscope_handler=handler,
            filemanager=filemanager,
            input_dir=input_dir,
            available_axis_values=("A01", "B03"),
        )

    planner = new_submission()
    for axis in ("A01", "B03"):
        context = SimpleNamespace(
            axis_id=axis,
            step_plans=[CompiledStepPlan(0, "image", "FunctionStep", axis)],
        )
        planner.prepare_pipeline_flags(context, [_step()])
        assert context.step_plans[0].read_backend == "virtual_workspace"
        assert context.step_plans[0].write_backend == "virtual_workspace"
    assert requests == [(input_dir, filemanager)]
    source_backend = "zarr"
    assert planner.resolve_backend(MaterializationBackend.AUTO) == "virtual_workspace"
    assert new_submission().resolve_backend(Backend.AUTO) == "zarr"
    assert requests == [(input_dir, filemanager), (input_dir, filemanager)]


def test_unused_materialization_auto_does_not_query_source():
    config = _pipeline_config(path_planning_config=PathPlanningConfig(well_filter=0))
    config.vfs_config = VFSConfig(
        read_backend=Backend.DISK,
        materialization_backend=MaterializationBackend.AUTO,
    )
    planner = MaterializationFlagPlanner(
        pipeline_config=config,
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate/images"),
        available_axis_values=("A01",),
    )
    context = SimpleNamespace(
        axis_id="A01",
        step_plans=[CompiledStepPlan(0, "image", "FunctionStep", "A01")],
    )
    planner.prepare_pipeline_flags(context, [_step()])
    assert context.step_plans[0].read_backend == "disk"
    assert context.step_plans[0].write_backend == "memory"
