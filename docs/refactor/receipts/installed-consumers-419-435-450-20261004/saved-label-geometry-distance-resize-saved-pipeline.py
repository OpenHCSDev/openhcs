# OpenHCS pipeline

from openhcs.constants.constants import (
    AllComponents,
    GroupBy,
    Microscope,
    VariableComponents,
)
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import ObjectLabelsArtifactType
from openhcs.core.config import (
    LazyAnalysisConsolidationConfig,
    LazyCompilationDebugConfig,
    LazyDtypeConfig,
    LazyFijiDisplayConfig,
    LazyFijiStreamingConfig,
    LazyNapariDisplayConfig,
    LazyNapariStreamingConfig,
    LazyPathPlanningConfig,
    LazyPlateMetadataConfig,
    LazyProcessingConfig,
    LazySequentialProcessingConfig,
    LazyStepMaterializationConfig,
    LazyStepWellFilterConfig,
    LazyStreamingDefaults,
    LazyTiffConfig,
    LazyVFSConfig,
    LazyWellFilterConfig,
    LazyZarrConfig,
    MultiprocessingStartMethod,
    PipelineConfig,
)
from openhcs.core.source_bindings import (
    ComponentSelector,
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    NamedSourceBinding,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceProjectionRole,
    SourceSelector,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.morphology import MorphOperation
from openhcs.processing.func_registry import get_function
from pathlib import Path
from polystore.config import TiffCompression

pipeline_config = PipelineConfig(
    materialization_results_path=Path('results'),
    materialize_runtime_artifacts=True,
    num_workers=1,
    microscope=Microscope.SOURCE_BINDINGS,
    use_threading=False,
    multiprocessing_start_method=MultiprocessingStartMethod.SPAWN,
    auto_add_output_plate_to_plate_manager=False,
    napari_display_config=LazyNapariDisplayConfig(),
    fiji_display_config=LazyFijiDisplayConfig(),
    well_filter_config=LazyWellFilterConfig(
        well_filter='A01'
    ),
    zarr_config=LazyZarrConfig(),
    tiff_config=LazyTiffConfig(
        compression=TiffCompression.DEFLATE,
        compression_level=9
    ),
    vfs_config=LazyVFSConfig(),
    dtype_config=LazyDtypeConfig(),
    processing_config=LazyProcessingConfig(),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.METADATA,
            dimensions=(
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='SavedImage',
                            metadata_field='well'
                        ),
                        SourceBindingMatchField(
                            alias='SavedIPO',
                            metadata_field='well'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='SavedImage',
                            metadata_field='site'
                        ),
                        SourceBindingMatchField(
                            alias='SavedIPO',
                            metadata_field='site'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='SavedImage',
                            metadata_field='channel'
                        ),
                        SourceBindingMatchField(
                            alias='SavedIPO',
                            metadata_field='channel'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='SavedImage',
                            metadata_field='z_index'
                        ),
                        SourceBindingMatchField(
                            alias='SavedIPO',
                            metadata_field='z_index'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='SavedImage',
                            metadata_field='timepoint'
                        ),
                        SourceBindingMatchField(
                            alias='SavedIPO',
                            metadata_field='timepoint'
                        )
                    )
                )
            )
        ),
        metadata_fields=(),
        source_filters=(),
        bindings=(
            NamedSourceBinding(
                alias='SavedImage',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='A01_SavedIPO_step0.labels.tif'
                        ),
                    )
                ),
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.WELL,
                        value='A01'
                    ),
                    ComponentSelector(
                        component=AllComponents.SITE,
                        value='1'
                    ),
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='2'
                    ),
                    ComponentSelector(
                        component=AllComponents.Z_INDEX,
                        value='1'
                    ),
                    ComponentSelector(
                        component=AllComponents.TIMEPOINT,
                        value='1'
                    )
                )
            ),
            NamedSourceBinding(
                alias='SavedIPO',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='A01_SavedIPO_step0.labels.tif'
                        ),
                    )
                ),
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.WELL,
                        value='A01'
                    ),
                    ComponentSelector(
                        component=AllComponents.SITE,
                        value='1'
                    ),
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='2'
                    ),
                    ComponentSelector(
                        component=AllComponents.Z_INDEX,
                        value='1'
                    ),
                    ComponentSelector(
                        component=AllComponents.TIMEPOINT,
                        value='1'
                    )
                ),
                artifact_kind=ObjectLabelsArtifactType,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            )
        ),
        image_plane_sources=(),
        imported_metadata_tables=(),
        source_stack_components=(),
        source_spatial_domain=SourceSpatialDomain(),
        grouping_metadata_fields=(),
        source_voxel_spacing=SourceVoxelSpacing(
            values_zyx=(
                1.3556,
                1.3556
            )
        )
    ),
    step_source_bindings_config=LazyStepSourceBindingsConfig(),
    sequential_processing_config=LazySequentialProcessingConfig(),
    analysis_consolidation_config=LazyAnalysisConsolidationConfig(),
    plate_metadata_config=LazyPlateMetadataConfig(),
    path_planning_config=LazyPathPlanningConfig(
        well_filter='A01',
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261004/installed-consumer-419-435-450-v7/outputs/saved')
    ),
    step_well_filter_config=LazyStepWellFilterConfig(),
    step_materialization_config=LazyStepMaterializationConfig(
        well_filter='A01',
        enabled=True
    ),
    streaming_defaults=LazyStreamingDefaults(),
    napari_streaming_config=LazyNapariStreamingConfig(
        enabled=False
    ),
    fiji_streaming_config=LazyFijiStreamingConfig(),
    compilation_debug_config=LazyCompilationDebugConfig()
)

pipeline_steps = [
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': (
                    'SavedIPO',
                )
            }),
        name='SavedIPOShape',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_morph'), {
                'operation': MorphOperation.DISTANCE,
                'rescale_values': False,
                'select_the_input_image': 'SavedImage',
                'name_the_output_image': 'SavedDistance'
            }),
        name='SavedIPODistance',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_resize'), {
                'resizing_factor_x': 2.0,
                'resizing_factor_y': 2.0,
                'name_the_output_image': 'ResizedDistance'
            }),
        name='PreparedSavedDistanceResize',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PREVIOUS_STEP
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=False
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.NONE,
                'truncate_low': False,
                'truncate_high': False,
                'name_the_output_image': 'ResizedConsumer'
            }),
        name='ConsumePreparedResize',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PREVIOUS_STEP
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=False
        )
    )
]