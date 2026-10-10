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
from openhcs.processing.backends.cellprofiler.illumination import (
    FilterSizeMethod,
    IlluminationCorrectionMethod,
    IntensityChoice,
    RescaleOption,
    SmoothingMethod,
)
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFilenameMethod,
)
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerOtsuMethod,
    CellProfilerThresholdAssignment,
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
                alias='Grayscale',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='--W00001'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleIlluminationCorrection_Example2/candidate/0')
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
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 20,
                'max_diameter': 50,
                'exclude_size': False,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'UncorrectedNuclei'
            }),
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'block_size': 8,
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.MEDIAN_FILTER,
                'filter_size_method': FilterSizeMethod.OBJECT_SIZE,
                'object_width': 16,
                'name_the_output_image': 'SmallBlockIllum'
            }),
        name='CorrectIlluminationCalculate',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'name_the_output_image': 'SmallBlockCorrected'
            }),
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 20,
                'max_diameter': 50,
                'exclude_size': False,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'SmallBlockCorrectedNuclei'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'block_size': 20,
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.MEDIAN_FILTER,
                'filter_size_method': FilterSizeMethod.MANUALLY,
                'manual_filter_size': 50,
                'name_the_output_image': 'LargeBlockIllum'
            }),
        name='CorrectIlluminationCalculate',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'select_the_input_image': 'Grayscale',
                'select_the_illumination_function': 'LargeBlockIllum',
                'name_the_output_image': 'LargeBlockCorrected'
            }),
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 20,
                'max_diameter': 50,
                'exclude_size': False,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'LargeBlockCorrectedNuclei'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'select_the_input_objects': 'UncorrectedNuclei',
                'name_the_output_image': 'OpenHCSReferenceLabels_UncorrectedNuclei'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                'single_file_name': 'reference_labels__UncorrectedNuclei',
                'bit_depth': SaveImagesBitDepth.UINT16,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False,
                'select_the_image_to_save': 'OpenHCSReferenceLabels_UncorrectedNuclei'
            }),
        name='SaveImages'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'select_the_input_objects': 'SmallBlockCorrectedNuclei',
                'name_the_output_image': 'OpenHCSReferenceLabels_SmallBlockCorrectedNuclei'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                'single_file_name': 'reference_labels__SmallBlockCorrectedNuclei',
                'bit_depth': SaveImagesBitDepth.UINT16,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False,
                'select_the_image_to_save': 'OpenHCSReferenceLabels_SmallBlockCorrectedNuclei'
            }),
        name='SaveImages'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'select_the_input_objects': 'LargeBlockCorrectedNuclei',
                'name_the_output_image': 'OpenHCSReferenceLabels_LargeBlockCorrectedNuclei'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                'single_file_name': 'reference_labels__LargeBlockCorrectedNuclei',
                'bit_depth': SaveImagesBitDepth.UINT16,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False,
                'select_the_image_to_save': 'OpenHCSReferenceLabels_LargeBlockCorrectedNuclei'
            }),
        name='SaveImages'
    )
]