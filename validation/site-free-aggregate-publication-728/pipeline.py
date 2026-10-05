"""Tiny registered multisite/default-publication receiving document.

Not executed or live-qualified. The receiving owner must pin the whole installed
candidate and release its original native6012/viewer6013 family before use.
"""
from pathlib import Path

from zmqruntime.config import TransportMode

from openhcs.constants.constants import GroupBy, Microscope, VariableComponents
from openhcs.core.config import (
    LazyNapariStreamingConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazySourceBindingsConfig,
    LazyStepMaterializationConfig,
    PipelineConfig,
)
from openhcs.core.source_bindings import (
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
)
from openhcs.core.steps import FunctionStep
from openhcs.processing.backends.assemblers.assemble_stack_cpu import assemble_stack_cpu
from openhcs.processing.backends.assemblers.blending import TileBlendMethod
from openhcs.processing.backends.cellprofiler.intensity import measure_image_intensity
from openhcs.processing.backends.pos_gen.acquisition_positions import acquisition_tile_positions

packet = Path(
    "/home/ts/wt/openhcs-issue-batch-20260929/engineering728/public01"
)
field_processing = LazyProcessingConfig(
    variable_components=[VariableComponents.Z_INDEX], group_by=GroupBy.CHANNEL,
)
site_processing = LazyProcessingConfig(
    variable_components=[VariableComponents.SITE], group_by=GroupBy.CHANNEL,
)
pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=1,
    use_threading=True,
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(
            MetadataSource.FILE_NAME,
            r"(?P<well>A\d+)_s(?P<site>\d+)_w(?P<channel>\d+)_z(?P<z_index>\d+)_t(?P<timepoint>\d+)\.tif",
        ),),
        bindings=(NamedSourceBinding(alias="Signal"),),
        source_stack_components=(),
    ),
    processing_config=field_processing,
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=packet / "results",
    ),
    # This is the existing original engineering94 family, NOT a new lease.
    # Do not submit until the sole receiving owner releases that exact family.
    napari_streaming_config=LazyNapariStreamingConfig(
        enabled=True, port=6013, host="127.0.0.1",
        transport_mode=TransportMode.TCP,
    ),
)
pipeline_steps = [
    FunctionStep(
        name="AcquiredFieldMeasurements",
        func=measure_image_intensity,
        processing_config=field_processing,
        step_materialization_config=LazyStepMaterializationConfig(
            enabled=True, sub_dir="acquired-checkpoints",
        ),
    ),
    FunctionStep(
        name="EmbeddedAcquisitionPositions",
        func=acquisition_tile_positions,
        processing_config=site_processing,
    ),
    FunctionStep(
        name="AssembledField",
        func=(assemble_stack_cpu, {"blend_method": TileBlendMethod.NONE}),
        processing_config=site_processing,
        step_materialization_config=LazyStepMaterializationConfig(
            enabled=True, sub_dir="aggregate-checkpoints",
        ),
    ),
    FunctionStep(
        name="AggregateFieldMeasurements",
        func=measure_image_intensity,
        processing_config=field_processing,
    ),
]
