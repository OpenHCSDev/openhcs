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
    PipelineConfig,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_bindings import (
    ComponentSelector,
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.source_metadata import (
    SourceVoxelSpacing,
    SourceVoxelSpacingUnit,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler.measurement_scope import CellProfilerMeasurementTargetScope
from openhcs.processing.backends.cellprofiler.outlines import LineMode
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
)
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFileFormat,
)
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerThresholdAssignment,
    CellProfilerThresholdMethod,
)
from openhcs.processing.func_registry import get_function
from pathlib import Path

pipeline_config = PipelineConfig(
    materialization_results_path=Path('results'),
    materialize_runtime_artifacts=False,
    microscope=Microscope.AUTO,
    auto_add_output_plate_to_plate_manager=False,
    napari_display_config=LazyNapariDisplayConfig(),
    fiji_display_config=LazyFijiDisplayConfig(),
    well_filter_config=LazyWellFilterConfig(
        well_filter=[
            'A01'
        ]
    ),
    zarr_config=LazyZarrConfig(),
    tiff_config=LazyTiffConfig(),
    vfs_config=LazyVFSConfig(),
    dtype_config=LazyDtypeConfig(),
    processing_config=LazyProcessingConfig(
        variable_components=[
            VariableComponents.SITE
        ],
        group_by=GroupBy.CHANNEL,
        input_source=InputSource.PREVIOUS_STEP
    ),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.ORDER
        ),
        metadata_fields=(
            FieldSpec(
                name='FileLocation',
                dtype=str,
                required=False
            ),
        ),
        source_filters=(
            SourceFilterClause(
                subject=SourceFilterSubject.EXTENSION,
                match_type=SourceFilterMatchType.IS_IMAGE
            ),
            SourceFilterClause(
                subject=SourceFilterSubject.DIRECTORY,
                match_type=SourceFilterMatchType.DOES_NOT_CONTAIN_REGEX,
                value='[\\/]\\.'
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='phase',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.EXTENSION,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='.png'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='1'
                    ),
                ),
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='cho',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.EXTENSION,
                            match_type=SourceFilterMatchType.IS_TIF
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='2'
                    ),
                ),
                source_channel_axis=-1
            )
        ),
        image_plane_sources=(),
        imported_metadata_tables=(),
        source_stack_components=(),
        source_spatial_domain=SourceSpatialDomain(),
        grouping_metadata_fields=(),
        source_voxel_spacing=SourceVoxelSpacing(
            values_zyx=(
                1.0,
                1.0,
                1.0
            ),
            unit=SourceVoxelSpacingUnit.RELATIVE
        )
    ),
    step_source_bindings_config=LazyStepSourceBindingsConfig(),
    sequential_processing_config=LazySequentialProcessingConfig(),
    analysis_consolidation_config=LazyAnalysisConsolidationConfig(),
    plate_metadata_config=LazyPlateMetadataConfig(),
    path_planning_config=LazyPathPlanningConfig(
        well_filter=0,
        output_dir_suffix='_matched_pilot',
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/cp_tutorial_pixel_based_classification/candidate/0')
    ),
    step_well_filter_config=LazyStepWellFilterConfig(),
    step_materialization_config=LazyStepMaterializationConfig(),
    streaming_defaults=LazyStreamingDefaults(),
    napari_streaming_config=LazyNapariStreamingConfig(),
    fiji_streaming_config=LazyFijiStreamingConfig(),
    compilation_debug_config=LazyCompilationDebugConfig()
)

pipeline_steps = [
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_threshold'), {
                    'threshold_method': CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
                    'window_size': 10,
                    'smoothing': 1.3488,
                    'name_the_output_image': 'phaseThresh'
                })
        },
        name='Threshold',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '2': (get_function('openhcs:cellprofiler_color_to_gray'), {
                    'channel_indices': (
                        0,
                    ),
                    'contributions': (
                        1.0,
                    ),
                    'name_the_output_image': 'choSegmented'
                })
        },
        name='ColorToGray',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 40,
                'max_diameter': 100,
                'unclump_method': UnclumpMethod.SHAPE,
                'watershed_method': WatershedMethod.SHAPE,
                'smoothing_filter_size': 5,
                'automatic_suppression': False,
                'maxima_suppression_size': 10.0,
                'low_res_maxima': False,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'threshold_smoothing_scale': 1.0,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'name_the_primary_objects_to_be_identified': 'Cells'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_texture_objects'), {
                'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                'select_images_to_measure': 'phase'
            }),
        name='MeasureTexture',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_overlay_outlines'), {
                    'line_mode': LineMode.THICK,
                    'name_the_output_image': 'ChoOverlay'
                })
        },
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images_with_measurements'), {
                'saved_image_name': 'ChoOverlay',
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': '_outlines',
                'file_format': SaveImagesFileFormat.PNG,
                'bit_depth': SaveImagesBitDepth.UINT8,
                'base_image_folder': 'Elsewhere...|',
                'lossless_compression': False,
                'record_file_and_path': True,
                'select_image_name_for_file_prefix': 'phase'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='phase',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.EXTENSION,
                                match_type=SourceFilterMatchType.EQUALS,
                                value='.png'
                            ),
                        )
                    ),
                    origin=SourceBindingOrigin.PIPELINE_START,
                    component_identity=(
                        ComponentSelector(
                            component=AllComponents.CHANNEL,
                            value='1'
                        ),
                    ),
                    load_as_monochrome=True
                ),
            )
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'add_image_metadata': True,
                'filename_prefix': 'cho_',
                'overwrite_existing_files_without_warning': True
            }),
        name='ExportToSpreadsheet',
        processing_config=LazyProcessingConfig(
            variable_components=[],
            group_by=GroupBy.NONE
        )
    )
]