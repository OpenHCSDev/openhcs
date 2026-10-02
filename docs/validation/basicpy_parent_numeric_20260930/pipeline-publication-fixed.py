"""Same 24-site synthetic fit; only the output root differs from predecessor."""

from pathlib import Path

from openhcs.constants import GroupBy, Microscope, VariableComponents
from openhcs.core.config import (
    LazyNapariStreamingConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazyStepMaterializationConfig,
    LazyVFSConfig,
    MaterializationBackend,
    PipelineConfig,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.enhance.basic_processor_jax import (
    basic_flatfield_correction_jax,
)
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    num_workers=1,
    use_threading=True,
    microscope=Microscope.IMAGEXPRESS,
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=Path(
            "/home/ts/wt/openhcs-issue-batch-20260929/"
            "basicpy-publication-fixed-20260930/outputs"
        ),
    ),
    vfs_config=LazyVFSConfig(materialization_backend=MaterializationBackend.DISK),
)
pipeline_steps = [
    FunctionStep(
        func=(
            basic_flatfield_correction_jax,
            {"max_iterations": 100, "working_size": None, "get_darkfield": False},
        ),
        name="BaSiCFit",
        processing_config=LazyProcessingConfig(
            variable_components=[VariableComponents.SITE],
            group_by=GroupBy.CHANNEL,
        ),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=True,
            port=5596,
            host="127.0.0.1",
            transport_mode=TransportMode.TCP,
            persistent=True,
        ),
    ),
]
