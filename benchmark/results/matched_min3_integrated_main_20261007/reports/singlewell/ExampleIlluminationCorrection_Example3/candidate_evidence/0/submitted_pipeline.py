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
    IlluminationCorrectionMethod,
    IntensityChoice,
    RescaleOption,
    SmoothingMethod,
)
from openhcs.processing.backends.cellprofiler.image_geometry import MaskSource
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.morphology import ExpandShrinkMode
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFileFormat,
    SaveImagesFilenameMethod,
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
                alias='OrigWorms',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='ADSAStaphInfection2_A01_w2'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/ExampleIlluminationCorrection_Example3/candidate/0')
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
                'min_diameter': 1,
                'exclude_size': False,
                'unclump_method': UnclumpMethod.NONE,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'Well'
            }),
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                'mode': ExpandShrinkMode.SHRINK_DEFINED_PIXELS,
                'iterations': 5,
                'fill_holes': False,
                'name_the_output_objects': 'ShrunkenWell'
            }),
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.INVERT,
                'name_the_output_image': 'InvertedWorms'
            }),
        name='ImageMath',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'InvertedWorms',
                'select_object_for_mask': 'ShrunkenWell',
                'name_the_output_image': 'MaskedInvertedWorms'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'intensity_choice': IntensityChoice.BACKGROUND,
                'block_size': 2,
                'rescale_option': RescaleOption.NO,
                'name_the_output_image': 'PolynomialIllum'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'method': IlluminationCorrectionMethod.SUBTRACT,
                'select_the_input_image': 'MaskedInvertedWorms',
                'select_the_illumination_function': 'PolynomialIllum',
                'name_the_output_image': 'PolynomialCorrected'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'OrigWorms',
                'select_object_for_mask': 'ShrunkenWell',
                'name_the_output_image': 'MaskedOrigWorms'
            }),
        name='MaskImage',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'smoothing_method': SmoothingMethod.CONVEX_HULL,
                'name_the_output_image': 'ConvexHullIllumWorm'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'select_the_input_image': 'MaskedOrigWorms',
                'select_the_illumination_function': 'ConvexHullIllumWorm',
                'name_the_output_image': 'ConvexHullCorrWorm'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=[
            (get_function('openhcs:cellprofiler_save_images'), {
                    'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                    'single_file_name': 'reference_image__PolynomialCorrected',
                    'file_format': SaveImagesFileFormat.NPY,
                    'bit_depth': SaveImagesBitDepth.FLOAT32,
                    'base_image_folder': 'Elsewhere...|',
                    'record_file_and_path': False,
                    'select_the_image_to_save': 'PolynomialCorrected'
                }),
            (get_function('openhcs:cellprofiler_save_images'), {
                    'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                    'single_file_name': 'reference_image__ConvexHullCorrWorm',
                    'file_format': SaveImagesFileFormat.NPY,
                    'bit_depth': SaveImagesBitDepth.FLOAT32,
                    'base_image_folder': 'Elsewhere...|',
                    'record_file_and_path': False,
                    'select_the_image_to_save': 'ConvexHullCorrWorm'
                })
        ],
        name='SaveImages'
    )
]