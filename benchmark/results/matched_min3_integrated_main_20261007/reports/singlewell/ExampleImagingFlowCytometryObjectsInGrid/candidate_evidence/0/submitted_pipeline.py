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
from openhcs.interop.cellprofiler.measurement_scope import CellProfilerMeasurementTargetScope
from openhcs.processing.backends.cellprofiler.grid import (
    DiameterChoice,
    ShapeChoice,
)
from openhcs.processing.backends.cellprofiler.image_geometry import MaskSource
from openhcs.processing.backends.cellprofiler.intensity_distribution import IntensityDistributionZernikeMode
from openhcs.processing.backends.cellprofiler.morphology import ExpandShrinkMode
from openhcs.processing.backends.cellprofiler.object_filtering import FilterMethod
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
)
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
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
                alias='BF_image',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch1'
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
                alias='DF_image',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch6'
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
            ),
            NamedSourceBinding(
                alias='Marker_image',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch7'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='3'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/ExampleImagingFlowCytometryObjectsInGrid/candidate/0')
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
            '1': (get_function('openhcs:cellprofiler_define_grid_manual'), {
                    'grid_rows': 30,
                    'grid_columns': 30,
                    'first_spot_x': 27,
                    'first_spot_y': 27,
                    'second_spot_x': 82,
                    'second_spot_y': 82,
                    'second_spot_row': 2,
                    'second_spot_col': 2,
                    'retain_an_image_of_the_grid': False,
                    'name_the_grid': 'Grid'
                })
        },
        name='DefineGrid',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_identify_objects_in_grid'), {
                    'diameter_choice': DiameterChoice.AUTOMATIC,
                    'name_the_objects_to_be_identified': 'Tile_of_grid'
                })
        },
        name='IdentifyObjectsInGrid',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_images_to_measure': 'DF_image'
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_filter_objects'), {
                'measurement_features': (
                    'Intensity_StdIntensity_DF_image',
                ),
                'measurement_min_values': (
                    2e-05,
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
                'name_the_output_objects': 'Filtered_tiles'
            }),
        name='FilterObjects'
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_mask_image'), {
                    'mask_source': MaskSource.OBJECTS,
                    'select_the_input_image': 'BF_image',
                    'select_object_for_mask': 'Filtered_tiles',
                    'name_the_output_image': 'MaskBF'
                })
        },
        name='MaskImage',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_smooth'), {
                'auto_object_size': False,
                'object_size': 3.0,
                'name_the_output_image': 'SmoothedBF'
            }),
        name='Smooth'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_enhance_edges'), {
                'name_the_output_image': 'EdgedImage'
            }),
        name='EnhanceEdges'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_closing'), {
                'size': 5,
                'name_the_output_image': 'MorphBf'
            }),
        name='Closing'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'max_diameter': 45,
                'unclump_method': UnclumpMethod.SHAPE,
                'watershed_method': WatershedMethod.SHAPE,
                'threshold_correction_factor': 1.05,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'bf1'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': 'bf1'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_filter_objects'), {
                'measurement_features': (
                    'AreaShape_FormFactor',
                ),
                'measurement_min_values': (
                    0.2,
                ),
                'measurement_max_values': (
                    1.0,
                ),
                'measurement_use_minimum': (
                    True,
                ),
                'measurement_use_maximum': (
                    True,
                ),
                'select_the_object_to_filter': 'bf1',
                'name_the_output_objects': 'FilteredBF'
            }),
        name='FilterObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': 'FilteredBF'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                'mode': ExpandShrinkMode.SHRINK_DEFINED_PIXELS,
                'fill_holes': False,
                'select_the_input_objects': 'Filtered_tiles',
                'name_the_output_objects': 'Non_empty_tile'
            }),
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'save_children_with_parents': False,
                'select_the_parent_objects': 'Non_empty_tile',
                'select_the_child_objects': 'FilteredBF'
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_filter_objects'), {
                'filter_method': FilterMethod.MAXIMAL_PER_OBJECT,
                'measurement_features': (
                    'AreaShape_Area',
                ),
                'measurement_min_values': (
                    0.0,
                ),
                'measurement_max_values': (
                    1.0,
                ),
                'measurement_use_minimum': (
                    True,
                ),
                'measurement_use_maximum': (
                    True,
                ),
                'select_the_object_to_filter': 'FilteredBF',
                'select_the_objects_that_contain_the_filtered_objects': 'Non_empty_tile',
                'name_the_output_objects': 'BF_cells_on_grid_pre'
            }),
        name='FilterObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_objects_in_grid'), {
                'shape_choice': ShapeChoice.NATURAL,
                'diameter_choice': DiameterChoice.AUTOMATIC,
                'select_the_defined_grid': 'Grid',
                'select_the_guiding_objects': 'BF_cells_on_grid_pre',
                'name_the_objects_to_be_identified': 'BF_cells_on_grid'
            }),
        name='IdentifyObjectsInGrid'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_expand_or_shrink_objects'), {
                'iterations': 8,
                'fill_holes': False,
                'select_the_input_objects': 'BF_cells_on_grid',
                'name_the_output_objects': 'SSC'
            }),
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_overlay_outlines'), {
                    'select_image_on_which_to_display_outlines': 'BF_image',
                    'select_objects_to_display': 'BF_cells_on_grid',
                    'name_the_output_image': 'OrigOverlay'
                })
        },
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'select_object_sets_to_measure': 'BF_cells_on_grid'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_granularity_objects'), {
                'subsample_size': 1.0,
                'spectrum_length': 5,
                'select_object_sets_to_measure': (
                    'BF_cells_on_grid',
                    'SSC'
                ),
                'select_images_to_measure': (
                    'BF_image',
                    'Marker_image',
                    'DF_image'
                )
            }),
        name='MeasureGranularity',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_texture_objects'), {
                'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                'select_object_sets_to_measure': 'BF_cells_on_grid',
                'select_images_to_measure': (
                    'BF_image',
                    'Marker_image'
                )
            }),
        name='MeasureTexture',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_texture_objects'), {
                'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                'select_object_sets_to_measure': 'SSC',
                'select_images_to_measure': 'DF_image'
            }),
        name='MeasureTexture',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': 'BF_cells_on_grid',
                'select_images_to_measure': (
                    'BF_image',
                    'Marker_image'
                )
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': 'SSC',
                'select_images_to_measure': 'DF_image'
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity_distribution'), {
                'wants_zernikes': IntensityDistributionZernikeMode.MAGNITUDES_AND_PHASE,
                'select_objects_to_use_as_centers': 'None',
                'select_object_sets_to_measure': 'BF_cells_on_grid',
                'select_images_to_measure': (
                    'BF_image',
                    'Marker_image'
                )
            }),
        name='MeasureObjectIntensityDistribution',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity_distribution'), {
                'wants_zernikes': IntensityDistributionZernikeMode.MAGNITUDES_AND_PHASE,
                'select_objects_to_use_as_centers': 'None',
                'select_object_sets_to_measure': 'SSC',
                'select_images_to_measure': 'DF_image'
            }),
        name='MeasureObjectIntensityDistribution',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'export_all_measurement_types': False,
                'file_selections': (
                    SpreadsheetFileSelection(
                        subjects=(
                            'BF_cells_on_grid',
                            'SSC'
                        ),
                        file_name='BF_cells_on_grid.csv'
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