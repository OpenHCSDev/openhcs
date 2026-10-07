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
from openhcs.processing.backends.cellprofiler.area_occupied import OperandChoice
from openhcs.processing.backends.cellprofiler.classification import ClassificationBinChoice
from openhcs.processing.backends.cellprofiler.colocalization import CostesMethod
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.morphology import ExpandShrinkMode
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerOtsuMethod,
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
                alias='OrigStain1',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='N_R'
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
                alias='OrigStain2',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='N_G'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/ExampleColocalization/candidate/2')
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
            '1': (get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                    'name_the_output_image': 'IllumStain1'
                }),
            '2': (get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                    'name_the_output_image': 'IllumStain2'
                })
        },
        name='CorrectIlluminationCalculate',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                    'name_the_output_image': 'CorrectedStain1'
                }),
            '2': (get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                    'name_the_output_image': 'CorrectedStain2'
                })
        },
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_align'), {
                'name_the_first_output_image': 'Stain1',
                'name_the_second_output_image': 'Stain2'
            }),
        name='Align',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_colocalization'), {
                'costes_method': CostesMethod.ACCURATE,
                'measurement_scope': CellProfilerMeasurementTargetScope.IMAGE
            }),
        name='MeasureColocalization',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE
        )
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_identify_primary_objects'), {
                    'min_diameter': 3,
                    'max_diameter': 15,
                    'threshold_method': CellProfilerThresholdMethod.OTSU,
                    'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                    'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                    'adaptive_window_size': 50,
                    'select_the_input_image': 'Stain1',
                    'name_the_primary_objects_to_be_identified': 'Objects1'
                }),
            '2': (get_function('openhcs:cellprofiler_identify_primary_objects'), {
                    'min_diameter': 3,
                    'max_diameter': 15,
                    'threshold_method': CellProfilerThresholdMethod.OTSU,
                    'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                    'adaptive_window_size': 50,
                    'select_the_input_image': 'Stain2',
                    'name_the_primary_objects_to_be_identified': 'Objects2'
                })
        },
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.CENTROID,
                'save_children_with_parents': False
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                    'mode': ExpandShrinkMode.SHRINK_TO_POINT,
                    'fill_holes': False,
                    'name_the_output_objects': 'ShrunkenObjects1'
                }),
            '2': (get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                    'mode': ExpandShrinkMode.SHRINK_TO_POINT,
                    'fill_holes': False,
                    'name_the_output_objects': 'ShrunkenObjects2'
                })
        },
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                    'iterations': 2,
                    'fill_holes': False,
                    'select_the_input_objects': 'ShrunkenObjects1',
                    'name_the_output_objects': 'ExpandedObjects1'
                }),
            '2': (get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                    'iterations': 2,
                    'fill_holes': False,
                    'select_the_input_objects': 'ShrunkenObjects2',
                    'name_the_output_objects': 'ExpandedObjects2'
                })
        },
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'save_children_with_parents': False,
                'select_the_parent_objects': 'ExpandedObjects1',
                'select_the_child_objects': 'ExpandedObjects2'
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_classify_objects_single_measurement'), {
                'measurement_feature': 'Children_Objects2_Count',
                'bin_choice': ClassificationBinChoice.CUSTOM,
                'wants_low_bin': True,
                'wants_high_bin': True,
                'custom_thresholds': (
                    0.5,
                ),
                'bin_names': (
                    'NotColocalized',
                    'Colocalized'
                ),
                'select_the_object_to_be_classified': 'Objects1'
            }),
        name='ClassifyObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_filter_objects'), {
                'measurement_features': (
                    'Children_Objects2_Count',
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
                'select_the_object_to_filter': 'Objects1',
                'name_the_output_objects': 'ColocalizedObjects'
            }),
        name='FilterObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_objects'), {
                'select_the_input_objects': 'Objects1',
                'select_the_masking_object': 'Objects2',
                'name_the_output_objects': 'ColocalizedRegion'
            }),
        name='MaskObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_image_area_occupied'), {
                'operand_choices': (
                    OperandChoice.OBJECTS,
                    OperandChoice.OBJECTS
                ),
                'select_objects_to_measure': (
                    'ColocalizedRegion',
                    'Objects1'
                )
            }),
        name='MeasureImageAreaOccupied'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_calculate_math'), {
                'operand1_feature': 'AreaOccupied_AreaOccupied_ColocalizedRegion',
                'operand2_feature': 'AreaOccupied_AreaOccupied_Objects1',
                'operation': ImageMathOperation.DIVIDE,
                'output_name': 'Stain1Colocalized'
            }),
        name='CalculateMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'export_all_measurement_types': False,
                'file_selections': (
                    SpreadsheetFileSelection(
                        subjects=(
                            'Image',
                        ),
                        file_name='Image.csv'
                    ),
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