# OpenHCS pipeline

from openhcs.constants.constants import (
    AllComponents,
    GroupBy,
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
from openhcs.processing.backends.cellprofiler.color import ColorToGrayMode
from openhcs.processing.backends.cellprofiler.crop import CropModule
from openhcs.processing.backends.cellprofiler.grid import (
    DiameterChoice,
    ShapeChoice,
)
from openhcs.processing.backends.cellprofiler.illumination import (
    IlluminationCorrectionMethod,
    IntensityChoice,
    RescaleOption,
    SmoothingMethod,
)
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
    CellProfilerOtsuMethod,
    CellProfilerThresholdMethod,
)
from openhcs.processing.func_registry import get_function
from pathlib import Path
from openhcs.core.dataset_sources.choice import AutoDetectedSource

pipeline_config = PipelineConfig(
    materialization_results_path=Path('results'),
    materialize_runtime_artifacts=False,
    dataset_source=AutoDetectedSource,
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
                value='[\\\\/]\\.'
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='original',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='1.JPG'
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
                source_channel_axis=-1
            ),
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/ExampleYeastPatches/candidate/2')
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
        func=(get_function('openhcs:cellprofiler_crop'), {
                'removal_method': CropModule.RemovalMethod.ALL,
                'left_right_rectangle_positions': (
                    170,
                    1425
                ),
                'top_bottom_rectangle_positions': (
                    150,
                    985
                ),
                'ellipse_center': (
                    500,
                    500
                ),
                'ellipse_x_radius': 400.0,
                'ellipse_y_radius': 200.0,
                'name_the_output_image': 'CropOriginal'
            }),
        name='Crop',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_color_to_gray'), {
                'mode': ColorToGrayMode.COMBINE,
                'name_the_output_image': 'CropGray'
            }),
        name='ColorToGray'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'block_size': 40,
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.CONVEX_HULL,
                'name_the_output_image': 'Illumgray'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'select_the_input_image': 'CropGray',
                'select_the_illumination_function': 'Illumgray',
                'name_the_output_image': 'CorrectedGray'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_closing'), {
                'size': 5,
                'name_the_output_image': 'ClosingGray'
            }),
        name='Closing'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 20,
                'max_diameter': 80,
                'unclump_method': UnclumpMethod.SHAPE,
                'watershed_method': WatershedMethod.SHAPE,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'Prespots'
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
        func=(get_function('openhcs:cellprofiler_display_data_on_image'), {
                'measurement_feature': 'AreaShape_FormFactor',
                'select_the_image_on_which_to_display_the_measurements': 'CorrectedGray',
                'name_the_output_image_that_has_the_measurements_displayed': 'DisplayImage'
            }),
        name='DisplayDataOnImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_display_data_on_image'), {
                'measurement_feature': 'AreaShape_Area',
                'select_the_image_on_which_to_display_the_measurements': 'CorrectedGray',
                'name_the_output_image_that_has_the_measurements_displayed': 'DisplayImage'
            }),
        name='DisplayDataOnImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_filter_objects'), {
                'measurement_features': (
                    'AreaShape_FormFactor',
                    'AreaShape_Area'
                ),
                'measurement_min_values': (
                    0.6,
                    1500.0
                ),
                'measurement_max_values': (
                    1.0,
                    1.0
                ),
                'measurement_use_minimum': (
                    True,
                    True
                ),
                'measurement_use_maximum': (
                    False,
                    False
                ),
                'name_the_output_objects': 'FilterObjects'
            }),
        name='FilterObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_define_grid_automatic'), {
                'first_spot_row': 1,
                'first_spot_col': 1,
                'second_spot_row': 1,
                'second_spot_col': 1,
                'retain_an_image_of_the_grid': False,
                'select_the_image_on_which_to_display_the_grid': 'CorrectedGray',
                'select_the_previously_identified_objects': 'FilterObjects',
                'name_the_grid': 'Grid'
            }),
        name='DefineGrid'
    ),
    FunctionStep(
        func=[
            (get_function('openhcs:cellprofiler_identify_objects_in_grid'), {
                    'shape_choice': ShapeChoice.NATURAL,
                    'diameter_choice': DiameterChoice.AUTOMATIC,
                    'select_the_defined_grid': 'Grid',
                    'select_the_guiding_objects': 'Prespots',
                    'name_the_objects_to_be_identified': 'NaturalSpots'
                }),
            (get_function('openhcs:cellprofiler_identify_objects_in_grid'), {
                    'shape_choice': ShapeChoice.CIRCLE_NATURAL,
                    'diameter_choice': DiameterChoice.AUTOMATIC,
                    'select_the_defined_grid': 'Grid',
                    'select_the_guiding_objects': 'Prespots',
                    'name_the_objects_to_be_identified': 'ForcedSpots'
                })
        ],
        name='IdentifyObjectsInGrid'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': (
                    'NaturalSpots',
                    'ForcedSpots'
                ),
                'select_images_to_measure': 'CorrectedGray'
            }),
        name='MeasureObjectIntensity'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'line_mode': LineMode.THICK,
                'select_image_on_which_to_display_outlines': 'CropGray',
                'select_objects_to_display': 'NaturalSpots',
                'name_the_output_image': 'OutlinedNatural'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'line_mode': LineMode.THICK,
                'select_image_on_which_to_display_outlines': 'CropGray',
                'select_objects_to_display': 'ForcedSpots',
                'name_the_output_image': 'OutlinedForced'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=[
            (get_function('openhcs:cellprofiler_save_images'), {
                    'single_file_name': 'OrigBlue',
                    'append_suffix': True,
                    'filename_suffix': '_NaturalOutline',
                    'file_format': SaveImagesFileFormat.PNG,
                    'bit_depth': SaveImagesBitDepth.UINT8,
                    'base_image_folder': 'Elsewhere...|',
                    'record_file_and_path': False,
                    'select_image_name_for_file_prefix': 'original',
                    'select_the_image_to_save': 'OutlinedNatural'
                }),
            (get_function('openhcs:cellprofiler_save_images'), {
                    'single_file_name': 'OrigBlue',
                    'append_suffix': True,
                    'filename_suffix': '_ForcedOutline',
                    'file_format': SaveImagesFileFormat.PNG,
                    'bit_depth': SaveImagesBitDepth.UINT8,
                    'base_image_folder': 'Elsewhere...|',
                    'record_file_and_path': False,
                    'select_image_name_for_file_prefix': 'original',
                    'select_the_image_to_save': 'OutlinedForced'
                })
        ],
        name='SaveImages',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'add_filename_prefix': False,
                'overwrite_existing_files_without_warning': True
            }),
        name='ExportToSpreadsheet',
        processing_config=LazyProcessingConfig(
            variable_components=[],
            group_by=GroupBy.NONE
        )
    )
]