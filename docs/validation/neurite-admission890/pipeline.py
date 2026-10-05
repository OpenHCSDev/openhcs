"""New complete engineering document; submit only after whole-target/lane handoff.

The acquisition generator is the existing public541 make-source.py. Its input
geometry/values are unchanged. No scientific input or prior operation is reused.
The receiving owner may project paths to its admitted persistent destination.
"""
from pathlib import Path

from openhcs.constants.constants import GroupBy, Microscope, VariableComponents
from openhcs.core.config import (
    LazyNapariStreamingConfig, LazyPathPlanningConfig, LazyProcessingConfig,
    LazySourceBindingsConfig, PipelineConfig,
)
from openhcs.core.source_bindings import (
    MetadataExtractionRule, MetadataSource, NamedSourceBinding,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    PixelCellBodySettings, PixelOutgrowthSettings,
    neurite_outgrowth_metaxpress_pixels,
)

packet = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering890/public01')
pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=1,
    use_threading=True,
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(
            MetadataSource.FILE_NAME,
            r'(?P<well>A\d+)_s(?P<site>\d+)_w(?P<channel>\d+)_z(?P<z_index>\d+)_t(?P<timepoint>\d+)\.tif',
        ),),
        bindings=(NamedSourceBinding(alias='Signal'),),
        source_stack_components=(),
        # Declared engineering acquisition calibration, not a biological estimate.
        # Analysis measurements remain explicitly in pixels.
        source_voxel_spacing=SourceVoxelSpacing((.5, .5)),
    ),
    processing_config=LazyProcessingConfig(
        variable_components=[VariableComponents.CHANNEL], group_by=GroupBy.NONE,
    ),
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=packet / 'results',
    ),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
)
pipeline_steps = [FunctionStep(
    name='OriginalNeuriteAdmissionEvidence',
    func=(neurite_outgrowth_metaxpress_pixels, {
        'neurite_channel_index': 0,
        'cell_body': PixelCellBodySettings(
            approximate_max_width=30, minimum_area=100,
            intensity_above_local_background=100,
        ),
        'outgrowth': PixelOutgrowthSettings(
            maximum_width=3, intensity_above_local_background=100,
            minimum_cell_growth_to_log_as_significant=20,
        ),
    }),
)]
