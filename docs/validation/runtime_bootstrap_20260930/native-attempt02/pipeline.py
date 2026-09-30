# OpenHCS pipeline

from openhcs.constants.constants import (
    Microscope,
    VariableComponents,
)
from openhcs.core.config import (
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazyStepMaterializationConfig,
    LazyVFSConfig,
    MaterializationBackend,
    PipelineConfig,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.custom_functions import inspect_volume_fixture
from pathlib import Path

pipeline_config = PipelineConfig(
    num_workers=1,
    microscope=Microscope.BIOFORMATS,
    use_threading=True,
    vfs_config=LazyVFSConfig(
        materialization_backend=MaterializationBackend.DISK
    ),
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=Path('/home/ts/wt/openhcs-context-bounding-20260929/docs/validation/runtime_bootstrap_20260930/native-attempt02/owned/outputs')
    )
)

pipeline_steps = [
    FunctionStep(
        func=inspect_volume_fixture,
        name='VolumeFixture0',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.Z_INDEX
            ]
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            enabled=True
        )
    ),
    FunctionStep(
        func=(inspect_volume_fixture, {
                'plane_indices': (
                    2,
                    0
                )
            }),
        name='VolumeFixture1',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.Z_INDEX
            ]
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            enabled=True
        )
    ),
    FunctionStep(
        func=inspect_volume_fixture,
        name='VolumeFixture2',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.Z_INDEX
            ]
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            enabled=True
        )
    )
]