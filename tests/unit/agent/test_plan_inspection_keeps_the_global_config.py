"""Inspecting a plan with another global config leaves the session's states alone."""

from pathlib import Path

import pytest
from objectstate import (
    ObjectStateRegistry,
    get_live_global_config,
    get_saved_global_config,
)

from openhcs.agent.dto.config import ConfigPatch
from openhcs.agent.dto.execution import PipelineSourceArtifactPlanInspectionRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.artifact_plan_inspection_service import (
    AgentProgressQueue,
    ArtifactPlanInspectionService,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
)
from openhcs.agent.services.config_service import ConfigService
from openhcs.core.config import GlobalPipelineConfig, PathPlanningConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from tests.unit.pyqt_gui.session_harness import caller_session

SUFFIX = "path_planning_config.output_dir_suffix"
PIPELINE_SOURCE = """from openhcs.core.config import PipelineConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.smoothing import reducenoise

pipeline_config = PipelineConfig()
pipeline_steps = [FunctionStep(func=(reducenoise, {
    'patch_size': 3, 'patch_distance': 3, 'cutoff_distance': 0.1,
}), name='DeclaredNlm')]
"""


@pytest.fixture
def plate(tmp_path: Path) -> Path:
    root = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(root), grid_size=(1, 1), tile_size=(64, 64),
        wavelengths=1, z_stack_levels=1, wells=["A01"], num_cells=3,
        random_seed=123, include_all_components=True,
    ).generate_dataset()
    return root


@pytest.fixture
def session_with_edits(plate: Path):
    """An open session: global config saved as ``_session`` and edited to ``_unsaved``;
    the plate is one of its datasets, saved with its own suffix ``_dataset``."""

    session_config = GlobalPipelineConfig(
        num_workers=3,
        path_planning_config=PathPlanningConfig(output_dir_suffix="_session"),
    )
    with caller_session(global_config=session_config) as session:
        (dataset_scope,) = session.add_dataset_roots([str(plate)])
        dataset_state = ObjectStateRegistry.get_by_scope(dataset_scope)
        dataset_state.update_parameter(SUFFIX, "_dataset")
        dataset_state.mark_saved()
        global_state = ObjectStateRegistry.global_config_state(GlobalPipelineConfig)
        global_state.update_parameter(SUFFIX, "_unsaved")
        yield global_state, dataset_state


def test_plan_uses_the_requested_global_config_and_the_session_keeps_its_own(
    plate: Path, tmp_path: Path, session_with_edits
):
    global_state, dataset_state = session_with_edits
    global_object = global_state.object_instance
    global_dirty = set(global_state.dirty_fields)
    assert SUFFIX in global_dirty
    dataset_parameters = dict(dataset_state.parameters)
    dataset_dirty = set(dataset_state.dirty_fields)

    config_service = ConfigService()
    requested = config_service.create(
        "GlobalPipelineConfig",
        ConfigPatch(
            config_type="GlobalPipelineConfig",
            values={"path_planning_config": {"output_dir_suffix": "_requested"}},
        ),
    )
    inspection = ArtifactPlanInspectionService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        ),
        config_service=config_service,
    ).inspect(
        PipelineSourceArtifactPlanInspectionRequest.from_fields(
            plate_path=str(plate),
            pipeline_source=PIPELINE_SOURCE,
            global_config_id=requested.config_id,
        )
    )

    assert inspection.errors == ()
    assert inspection.axes == ("A01",)
    assert inspection.progress_event_count == 1
    (step,) = inspection.steps
    assert Path(step.output_dir).parts[-2] == "plate_requested"

    assert ObjectStateRegistry.global_config_state(GlobalPipelineConfig) is global_state
    assert global_state.object_instance is global_object
    assert set(global_state.dirty_fields) == global_dirty
    saved = get_saved_global_config(GlobalPipelineConfig)
    assert saved.num_workers == 3
    assert saved.path_planning_config.output_dir_suffix == "_session"
    live = get_live_global_config(GlobalPipelineConfig)
    assert live.num_workers == 3
    assert live.path_planning_config.output_dir_suffix == "_unsaved"
    assert ObjectStateRegistry.get_by_scope(dataset_state.scope_id) is dataset_state
    assert dict(dataset_state.parameters) == dataset_parameters
    assert set(dataset_state.dirty_fields) == dataset_dirty


def test_compiling_in_the_session_process_is_refused(plate: Path, session_with_edits):
    global_state, _dataset_state = session_with_edits

    with pytest.raises(RuntimeError, match="holds the global config"):
        InProcessCompileInspectionGateway().compile(
            CompileInspectionInput(
                plate=plate,
                pipeline_document=PipelineDocumentCodec.from_source(PIPELINE_SOURCE),
                axis_filter=(),
                global_pipeline_config=GlobalPipelineConfig(),
                progress_queue=AgentProgressQueue(),
            )
        )

    assert ObjectStateRegistry.global_config_state(GlobalPipelineConfig) is global_state
    assert (
        get_live_global_config(GlobalPipelineConfig)
        .path_planning_config.output_dir_suffix
        == "_unsaved"
    )
    assert (
        get_saved_global_config(GlobalPipelineConfig)
        .path_planning_config.output_dir_suffix
        == "_session"
    )
