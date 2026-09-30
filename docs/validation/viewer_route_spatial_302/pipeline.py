from pathlib import Path
from openhcs.constants import Microscope, VariableComponents
from openhcs.core.config import (
    PipelineConfig, LazyPathPlanningConfig, LazyVFSConfig,
    LazyProcessingConfig, LazyNapariStreamingConfig,
    LazyStepMaterializationConfig, MaterializationBackend,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    num_workers=1, use_threading=True, microscope=Microscope.IMAGEXPRESS,
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=Path("/home/ts/wt/openhcs-issue-batch-20260929/viewer-route-spatial-302-20260930/outputs"),
    ),
    vfs_config=LazyVFSConfig(materialization_backend=MaterializationBackend.DISK),
)
pipeline_steps = [FunctionStep(
    func=(gaussian_blur, {"sigma": 1.0}), name="SameSourceGaussian",
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.Z_INDEX]),
    step_materialization_config=LazyStepMaterializationConfig(enabled=True),
    napari_streaming_config=LazyNapariStreamingConfig(
        enabled=True, port=5592, host="127.0.0.1", transport_mode=TransportMode.TCP, persistent=True,
    ),
)]
