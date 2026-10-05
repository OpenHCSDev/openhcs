"""New endpoint-well engineering document; never execute during preparation."""

from pathlib import Path

from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents
from openhcs.core.config import (
    PipelineConfig, LazyProcessingConfig, LazyPathPlanningConfig,
    LazySourceBindingsConfig, LazyNapariStreamingConfig,
)
from openhcs.core.source_bindings import (
    MetadataExtractionRule, MetadataSource, SourceFilterClause,
    SourceFilterMatchType, SourceFilterSubject,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.custom_functions import point_shape_volume_fixture_522
from zmqruntime.config import TransportMode

ROOT = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering494/standalone95-selection40')

pipeline_config = PipelineConfig(
    processing_config=LazyProcessingConfig(
        variable_components=[VariableComponents.Z_INDEX], group_by=GroupBy.CHANNEL,
    ),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=ROOT / 'results'),
    source_bindings_config=LazySourceBindingsConfig(
        source_filters=(SourceFilterClause(SourceFilterSubject.EXTENSION, SourceFilterMatchType.IS_TIF),),
        metadata_rules=(MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern=r'(?P<well>[A-H]\d{2})_s(?P<site>\d+)_w(?P<channel>\d+)_z(?P<z_index>\d+)_t(?P<timepoint>\d+)\.tif',
        ),),
        source_stack_components=(AllComponents.Z_INDEX,),
        source_voxel_spacing=SourceVoxelSpacing((2.0, 0.65, 0.65)),
    ),
    napari_streaming_config=LazyNapariStreamingConfig(
        enabled=True, persistent=True, host='127.0.0.1', listen_host='127.0.0.1',
        port=6015, transport_mode=TransportMode.TCP,
    ),
)

pipeline_steps = [FunctionStep(func=point_shape_volume_fixture_522, name='Own selected-member contract522')]
