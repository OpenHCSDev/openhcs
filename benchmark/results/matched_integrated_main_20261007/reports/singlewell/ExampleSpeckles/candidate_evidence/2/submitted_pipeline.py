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
from openhcs.processing.backends.cellprofiler.feature_enhancement import NeuriteMethod
from openhcs.processing.backends.cellprofiler.image_geometry import MaskSource
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
)
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
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
                            value='hoe'
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
                            value='h2ax'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleSpeckles/candidate/2')
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
                    'min_diameter': 120,
                    'max_diameter': 300,
                    'unclump_method': UnclumpMethod.SHAPE,
                    'watershed_method': WatershedMethod.SHAPE,
                    'threshold_method': CellProfilerThresholdMethod.OTSU,
                    'adaptive_window_size': 50,
                    'name_the_primary_objects_to_be_identified': 'Nuclei'
                })
        },
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '2': (get_function('openhcs:cellprofiler_enhance_or_suppress_features'), {
                    'radius': 5.0,
                    'neurite_method': NeuriteMethod.TUBENESS,
                    'name_the_output_image': 'EnhancedGreen'
                })
        },
        name='EnhanceOrSuppressFeatures',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'mask_source': MaskSource.OBJECTS,
                'name_the_output_image': 'MaskedGreen'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 4,
                'max_diameter': 35,
                'automatic_smoothing': False,
                'smoothing_filter_size': 4,
                'automatic_suppression': False,
                'maxima_suppression_size': 4.0,
                'threshold_method': CellProfilerThresholdMethod.ROBUST_BACKGROUND,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'h2ax'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': 'Nuclei',
                'select_images_to_measure': 'OrigBlue'
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': 'h2ax',
                'select_images_to_measure': 'OrigGreen'
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'calculate_per_parent_means': True,
                'save_children_with_parents': False
            }),
        name='RelateObjects'
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
                    SpreadsheetFileSelection(
                        subjects=(
                            'Nuclei',
                        ),
                        file_name='Nuclei.csv'
                    ),
                    SpreadsheetFileSelection(
                        subjects=(
                            'h2ax',
                        ),
                        file_name='h2ax.csv'
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