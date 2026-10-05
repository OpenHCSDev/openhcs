# OpenHCS pipeline

from openhcs.constants.constants import (
    AllComponents,
    GroupBy,
    Microscope,
    VariableComponents,
)
from openhcs.constants.input_source import InputSource
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
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
)
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
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
        metadata_fields=(),
        source_filters=(),
        bindings=(
            NamedSourceBinding(
                alias='FITC',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='A01_s001_w2_z001_t001.tif'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261004/installed-consumer-419-435-450-v3/outputs/ipo')
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
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'exclude_size': False,
                'exclude_border_objects': False,
                'unclump_method': UnclumpMethod.NONE,
                'watershed_method': WatershedMethod.NONE,
                'threshold_method': CellProfilerThresholdMethod.MANUAL,
                'threshold_smoothing_scale': 0.0,
                'manual_threshold': 0.5,
                'select_the_input_image': 'FITC',
                'name_the_primary_objects_to_be_identified': 'SavedIPO'
            }),
        name='ProduceSavedIPO',
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
    )
]