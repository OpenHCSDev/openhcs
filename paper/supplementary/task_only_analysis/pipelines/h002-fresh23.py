from pathlib import Path
from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazyProcessingConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyNapariStreamingConfig
from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.custom_functions import h002_centres_v3_association
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    num_workers=1,
    materialize_runtime_artifacts=True,
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.Z_INDEX], group_by=GroupBy.CHANNEL, input_source=InputSource.PIPELINE_START),
    source_bindings_config=LazySourceBindingsConfig(source_stack_components=(AllComponents.Z_INDEX,), source_spatial_domain=VolumeSourceSpatialDomain(), source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.0,1.0,1.0), unit=SourceVoxelSpacingUnit.RELATIVE)),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-h002-h004-fresh23-rotation-20261006/H002_FRESH23_ROTATION_89/attempt05'), output_dir_suffix='_centres'),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
)
pipeline_steps = [FunctionStep(
    name='3D nucleus body centres REPAIR05 local marker association',
    func=(h002_centres_v3_association, dict(threshold=8000.0, sigma_z=1.0, sigma_yx=2.0, marker_prominence=4.0, min_volume=300, marker_connectivity=3, minimum_separation_z=5.0, minimum_separation_yx=10.0)),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False, persistent=True, host='127.0.0.1', port=6023, transport_mode=TransportMode.TCP),
)]
