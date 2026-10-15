"""Assisted detector development, not a replacement of the frozen blind trials.

Two previously reviewed fields; identical author115 settings and preprocessing
in both steps. Only embedded enhancement differs. Input TIFFs stay untouched.
"""
from pathlib import Path

from openhcs.constants.input_source import ReadPipelineStart
from openhcs.core.axes import Ungrouped
from openhcs.core.config import (
    PipelineConfig, LazyPathPlanningConfig, LazyProcessingConfig,
    LazySourceBindingsConfig, LazyNapariStreamingConfig,
)
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource
from openhcs.core.source_bindings import (
    NamedSourceBinding, ComponentSelector, SourceSelector, SourceFilterClause,
    SourceFileName, TextContains, FromFileName, MetadataExtractionRule,
    PairByMetadata, SourceBindingMatchDimension, SourceBindingMatchField,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_step import FunctionStep
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    neurite_outgrowth_metaxpress, MetaXpressCellBodySettings,
    MetaXpressOutgrowthSettings,
)

pipeline_config = PipelineConfig(
    dataset_source=SourceBindingsSource,
    num_workers=1,
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path(
            '/home/ts/.cache/agent-scratch/neurite-detector-20261014/comparison'
        ),
    ),
    materialize_runtime_artifacts=True,
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(
            source=FromFileName,
            pattern=r'^(?P<well>A\d{2})_s0*(?P<site>\d+)_w(?P<channel>[12])_z0*(?P<z_index>1)_t0*(?P<timepoint>1)\.tif$',
        ),),
        bindings=tuple(
            NamedSourceBinding(
                alias=alias,
                selector=SourceSelector(filters=(SourceFilterClause(
                    subject=SourceFileName, match_type=TextContains,
                    value=f'_w{channel}_',
                ),)),
                component_identity=(ComponentSelector(Microscopy.Channel, str(channel)),),
            )
            for alias, channel in [('DAPI', 1), ('FITC', 2)]
        ),
        match_plan=PairByMetadata(dimensions=tuple(
            SourceBindingMatchDimension(fields=tuple(
                SourceBindingMatchField(alias=alias, metadata_field=field)
                for alias in ['DAPI', 'FITC']
            )) for field in ['well', 'site', 'z_index', 'timepoint']
        )),
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
    ),
)
pipeline_steps = [
    FunctionStep(
        name='Embedded enhancement' if enhance else 'Local signal only',
        func=[
            (gaussian_blur, {'sigma': 0.8}),
            (neurite_outgrowth_metaxpress, {
                'neurite_channel_index': 1,
                'use_nuclear_stain': False,
                'cell_body': MetaXpressCellBodySettings(
                    approximate_max_width=35, minimum_area=40,
                    intensity_above_local_background=500,
                    channel_index=1, minimum_inscribed_diameter_px=4,
                ),
                'outgrowth': MetaXpressOutgrowthSettings(
                    maximum_width=4, intensity_above_local_background=100,
                    candidate_threshold_correction_factor=0.7,
                    enhance_neurites=enhance,
                ),
            }),
        ],
        processing_config=LazyProcessingConfig(
            variable_components=[Microscopy.Channel], group_by=Ungrouped,
            input_source=ReadPipelineStart,
        ),
        napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
    )
    for enhance in [True, False]
]
