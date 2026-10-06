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
from openhcs.processing.backends.cellprofiler.classification import ClassificationBinChoice
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerOtsuMethod,
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
                value='[\\\\/]\\.'
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='OrigBlue',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='d0.tif'
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
                alias='OrigGreen',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='d1.tif'
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
                load_as_monochrome=True
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261006/runtime-artifact-last-consumer-resumed-singlewell-v1/singlewell/capture/cases/ExamplePercentPositive/candidate/0')
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
            '1': (get_function('openhcs:cellprofiler_identify_primary_objects'), {
                    'min_diameter': 8,
                    'max_diameter': 80,
                    'unclump_method': UnclumpMethod.SHAPE,
                    'fill_holes': FillHolesOption.AFTER_DECLUMP,
                    'adaptive_window_size': 50,
                    'name_the_primary_objects_to_be_identified': 'Nuclei'
                }),
            '2': (get_function('openhcs:cellprofiler_identify_primary_objects'), {
                    'min_diameter': 5,
                    'max_diameter': 20,
                    'automatic_smoothing': False,
                    'fill_holes': FillHolesOption.AFTER_DECLUMP,
                    'threshold_min': 0.05,
                    'threshold_method': CellProfilerThresholdMethod.OTSU,
                    'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                    'adaptive_window_size': 50,
                    'name_the_primary_objects_to_be_identified': 'PH3'
                })
        },
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'save_children_with_parents': False
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_filter_objects'), {
                'measurement_features': (
                    'Children_PH3_Count',
                ),
                'measurement_min_values': (
                    1.0,
                ),
                'measurement_max_values': (
                    1.0,
                ),
                'measurement_use_minimum': (
                    True,
                ),
                'measurement_use_maximum': (
                    False,
                ),
                'select_the_object_to_filter': 'Nuclei',
                'name_the_output_objects': 'PH3PosNuclei'
            }),
        name='FilterObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': 'Nuclei',
                'select_images_to_measure': (
                    'OrigGreen',
                    'OrigBlue'
                )
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '2': (get_function('openhcs:cellprofiler_overlay_outlines'), {
                    'outline_colors': (
                        '#00FF40',
                    ),
                    'select_image_on_which_to_display_outlines': 'OrigGreen',
                    'select_objects_to_display': 'Nuclei',
                    'name_the_output_image': 'OrigGreenOverlay'
                })
        },
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_display_data_on_image'), {
                'measurement_feature': 'Intensity_MaxIntensity_OrigGreen',
                'text_color': (
                    1.0,
                    0.0,
                    1.0
                ),
                'select_the_image_on_which_to_display_the_measurements': 'OrigGreenOverlay',
                'select_the_input_objects': 'Nuclei',
                'name_the_output_image_that_has_the_measurements_displayed': 'DisplayImage'
            }),
        name='DisplayDataOnImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_classify_objects_single_measurement'), {
                'measurement_feature': 'Intensity_MaxIntensity_OrigGreen',
                'bin_choice': ClassificationBinChoice.CUSTOM,
                'wants_low_bin': True,
                'wants_high_bin': True,
                'custom_thresholds': (
                    0.2,
                ),
                'bin_names': (
                    'PH3Neg',
                    'PH3Pos'
                ),
                'select_the_object_to_be_classified': 'Nuclei'
            }),
        name='ClassifyObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_calculate_math'), {
                'operand1_feature': 'Count_PH3PosNuclei',
                'operand2_feature': 'Count_Nuclei',
                'operation': ImageMathOperation.DIVIDE,
                'final_multiplicand': 100,
                'output_name': 'PercentPositive',
                'select_the_denominator_objects': 'Nuclei'
            }),
        name='CalculateMath'
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