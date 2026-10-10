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
from openhcs.processing.backends.cellprofiler.alignment import AlignModule
from openhcs.processing.backends.cellprofiler.classification import (
    ClassificationBinChoice,
    SingleMeasurementClassificationRule,
)
from openhcs.processing.backends.cellprofiler.illumination import (
    IlluminationCorrectionMethod,
    IntensityChoice,
    RescaleOption,
    SmoothingMethod,
)
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
)
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFileFormat,
)
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdAssignment
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
                match_type=SourceFilterMatchType.DOES_NOT_START_WITH,
                value='.'
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='OrigColor',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='6-1.jpg'
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
            NamedSourceBinding(
                alias='PlateTemplate',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='PlateTemplate.png'
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
                load_as_monochrome=True,
                load_as_mask=True
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleYeastColonies/candidate/0')
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
            '1': (get_function('openhcs:cellprofiler_color_to_gray'), {
                    'name_the_output_image': (
                        'OrigRed',
                        'OrigGreen',
                        'OrigBlue'
                    )
                })
        },
        name='ColorToGray',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'object_dilation_radius': 0,
                'block_size': 22,
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.GAUSSIAN_FILTER,
                'select_the_input_image': 'OrigRed',
                'name_the_output_image': 'IllumRed'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'object_dilation_radius': 0,
                'block_size': 22,
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.GAUSSIAN_FILTER,
                'select_the_input_image': 'OrigBlue',
                'name_the_output_image': 'IllumBlue'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'object_dilation_radius': 0,
                'block_size': 22,
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.GAUSSIAN_FILTER,
                'select_the_input_image': 'OrigGreen',
                'name_the_output_image': 'IllumGreen'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'select_the_input_image': 'OrigRed',
                'select_the_illumination_function': 'IllumRed',
                'name_the_output_image': 'CorrRed'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'select_the_input_image': 'OrigBlue',
                'select_the_illumination_function': 'IllumBlue',
                'name_the_output_image': 'CorrBlue'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'select_the_input_image': 'OrigGreen',
                'select_the_illumination_function': 'IllumGreen',
                'name_the_output_image': 'CorrGreen'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'after_factor': 0.5,
                'select_the_first_image': 'CorrBlue',
                'select_the_second_image': 'CorrGreen',
                'name_the_output_image': 'CombinedImage'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_align'), {
                'additional_alignment_modes': (
                    AlignModule.AdditionalMode.SIMILARLY,
                ),
                'select_the_first_input_image': 'PlateTemplate',
                'select_the_second_input_image': 'CorrRed',
                'select_the_additional_image': 'CombinedImage',
                'name_the_first_output_image': 'AlignedPlate',
                'name_the_second_output_image': 'AlignedRed',
                'name_the_output_image': 'AlignedCombined'
            }),
        name='Align',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='PlateTemplate',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.EQUALS,
                                value='PlateTemplate.png'
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
                    load_as_monochrome=True,
                    load_as_mask=True
                ),
            )
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'select_the_input_image': 'CombinedImage',
                'select_image_for_mask': 'AlignedPlate',
                'name_the_output_image': 'MaskedCombined'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'select_the_input_image': 'CorrRed',
                'select_image_for_mask': 'AlignedPlate',
                'name_the_output_image': 'MaskedRedPlate'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.SUBTRACT,
                'truncate_low': False,
                'select_the_second_image': 'MaskedCombined',
                'name_the_output_image': 'SubtractedRed'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 1,
                'unclump_method': UnclumpMethod.SHAPE,
                'watershed_method': WatershedMethod.SHAPE,
                'automatic_smoothing': False,
                'smoothing_filter_size': 0,
                'automatic_suppression': False,
                'maxima_suppression_size': 2.0,
                'low_res_maxima': False,
                'threshold_min': 0.001,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'select_the_input_image': 'MaskedRedPlate',
                'name_the_primary_objects_to_be_identified': 'Colonies'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=get_function('openhcs:cellprofiler_measure_object_intensity'),
        name='MeasureObjectIntensity'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_classify_objects_single_measurement'), {
                'classification_rules': (
                    SingleMeasurementClassificationRule(
                        measurement_feature='AreaShape_Area',
                        bin_choice=ClassificationBinChoice.CUSTOM,
                        bin_count=1,
                        custom_thresholds=(
                            0.0,
                            5.0,
                            75.0,
                            1300.0
                        ),
                        bin_names=(
                            'Tiny',
                            'Small',
                            'Large'
                        )
                    ),
                    SingleMeasurementClassificationRule(
                        measurement_feature='Intensity_MeanIntensity_SubtractedRed',
                        bin_choice=ClassificationBinChoice.CUSTOM,
                        wants_low_bin=True,
                        wants_high_bin=True,
                        custom_thresholds=(
                            0.05,
                        ),
                        bin_names=(
                            'White',
                            'Red'
                        )
                    )
                )
            }),
        name='ClassifyObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'select_image_on_which_to_display_outlines': 'MaskedRedPlate',
                'name_the_output_image': 'OutlinedColonies'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigColor',
                'append_suffix': True,
                'filename_suffix': '_outlines',
                'file_format': SaveImagesFileFormat.PNG,
                'bit_depth': SaveImagesBitDepth.UINT8,
                'overwrite': False,
                'base_image_folder': 'Elsewhere...|/Users/veneskey/svn/pipeline/ExampleImages/ExampleYeastColonies_BT_Images',
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'OrigColor',
                'select_the_image_to_save': 'OutlinedColonies'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='OrigColor',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS,
                                value='6-1.jpg'
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
            )
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'calculate_aggregate_means': True,
                'export_all_measurement_types': False,
                'file_selections': (
                    SpreadsheetFileSelection(
                        subjects=(
                            'Image',
                        ),
                        file_name='Image.csv'
                    ),
                    SpreadsheetFileSelection(
                        subjects=(
                            'Colonies',
                        ),
                        file_name='Colonies.csv'
                    )
                ),
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