# Edit this pipeline and save to apply changes

from openhcs.constants.constants import GroupBy
from openhcs.constants.input_source import InputSource
from openhcs.core.config import LazyProcessingConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler.measurement_scope import CellProfilerMeasurementTargetScope
from openhcs.processing.backends.cellprofiler.edge import enhance_edges
from openhcs.processing.backends.cellprofiler.granularity import measure_granularity_objects
from openhcs.processing.backends.cellprofiler.grid import (
    DiameterChoice,
    ShapeChoice,
    define_grid_manual,
    identify_objects_in_grid,
)
from openhcs.processing.backends.cellprofiler.image_geometry import (
    MaskSource,
    mask_image,
)
from openhcs.processing.backends.cellprofiler.intensity import measure_object_intensity
from openhcs.processing.backends.cellprofiler.intensity_distribution import (
    IntensityDistributionZernikeMode,
    measure_object_intensity_distribution,
)
from openhcs.processing.backends.cellprofiler.morphology import (
    ExpandShrinkMode,
    closing,
    expand_or_shrink_objects,
)
from openhcs.processing.backends.cellprofiler.object_filtering import (
    FilterMethod,
    filter_objects,
)
from openhcs.processing.backends.cellprofiler.outlines import overlay_outlines
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
    identify_primary_objects,
)
from openhcs.processing.backends.cellprofiler.relationships import (
    RelateObjectsDistanceMethod,
    relate_objects,
)
from openhcs.processing.backends.cellprofiler.shape import measure_object_size_shape
from openhcs.processing.backends.cellprofiler.smoothing import smooth
from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
    SpreadsheetFileSelection,
    export_to_spreadsheet,
)
from openhcs.processing.backends.cellprofiler.texture import measure_texture_objects

pipeline_steps = [
    FunctionStep(
        func={
            '1': (define_grid_manual, {
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
            '1': (identify_objects_in_grid, {
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
        func={
            '2': (measure_object_intensity, {
                    'select_object_sets_to_measure': 'Tile_of_grid'
                })
        },
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(filter_objects, {
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
            '1': (mask_image, {
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
        func=(smooth, {
                'auto_object_size': False,
                'object_size': 3.0,
                'name_the_output_image': 'SmoothedBF'
            }),
        name='Smooth'
    ),
    FunctionStep(
        func=(enhance_edges, {
                'name_the_output_image': 'EdgedImage'
            }),
        name='EnhanceEdges'
    ),
    FunctionStep(
        func=(closing, {
                'size': 5,
                'name_the_output_image': 'MorphBf'
            }),
        name='Closing'
    ),
    FunctionStep(
        func=(identify_primary_objects, {
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
        func=(measure_object_size_shape, {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': 'bf1'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(filter_objects, {
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
        func=(measure_object_size_shape, {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': 'FilteredBF'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(expand_or_shrink_objects, {
                'mode': ExpandShrinkMode.SHRINK_DEFINED_PIXELS,
                'fill_holes': False,
                'select_the_input_objects': 'Filtered_tiles',
                'name_the_output_objects': 'Non_empty_tile'
            }),
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func=(relate_objects, {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'save_children_with_parents': False,
                'select_the_parent_objects': 'Non_empty_tile',
                'select_the_child_objects': 'FilteredBF'
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(filter_objects, {
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
        func=(identify_objects_in_grid, {
                'shape_choice': ShapeChoice.NATURAL,
                'diameter_choice': DiameterChoice.AUTOMATIC,
                'select_the_defined_grid': 'Grid',
                'select_the_guiding_objects': 'BF_cells_on_grid_pre',
                'name_the_objects_to_be_identified': 'BF_cells_on_grid'
            }),
        name='IdentifyObjectsInGrid'
    ),
    FunctionStep(
        func=(expand_or_shrink_objects, {
                'iterations': 8,
                'fill_holes': False,
                'select_the_input_objects': 'BF_cells_on_grid',
                'name_the_output_objects': 'SSC'
            }),
        name='ExpandOrShrinkObjects'
    ),
    FunctionStep(
        func={
            '1': (overlay_outlines, {
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
        func=(measure_object_size_shape, {
                'calculate_advanced': False,
                'select_object_sets_to_measure': 'BF_cells_on_grid'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func={
            '1': [
                (measure_granularity_objects, {
                        'subsample_size': 1.0,
                        'spectrum_length': 5,
                        'select_object_sets_to_measure': 'BF_cells_on_grid'
                    }),
                (measure_granularity_objects, {
                        'subsample_size': 1.0,
                        'spectrum_length': 5,
                        'select_object_sets_to_measure': 'SSC'
                    })
            ],
            '3': [
                (measure_granularity_objects, {
                        'subsample_size': 1.0,
                        'spectrum_length': 5,
                        'select_object_sets_to_measure': 'BF_cells_on_grid'
                    }),
                (measure_granularity_objects, {
                        'subsample_size': 1.0,
                        'spectrum_length': 5,
                        'select_object_sets_to_measure': 'SSC'
                    })
            ],
            '2': [
                (measure_granularity_objects, {
                        'subsample_size': 1.0,
                        'spectrum_length': 5,
                        'select_object_sets_to_measure': 'BF_cells_on_grid'
                    }),
                (measure_granularity_objects, {
                        'subsample_size': 1.0,
                        'spectrum_length': 5,
                        'select_object_sets_to_measure': 'SSC'
                    })
            ]
        },
        name='MeasureGranularity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (measure_texture_objects, {
                    'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                    'select_object_sets_to_measure': 'BF_cells_on_grid'
                }),
            '3': (measure_texture_objects, {
                    'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                    'select_object_sets_to_measure': 'BF_cells_on_grid'
                }),
            '2': (measure_texture_objects, {
                    'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                    'select_object_sets_to_measure': 'SSC'
                })
        },
        name='MeasureTexture',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (measure_object_intensity, {
                    'select_object_sets_to_measure': 'BF_cells_on_grid'
                }),
            '3': (measure_object_intensity, {
                    'select_object_sets_to_measure': 'BF_cells_on_grid'
                }),
            '2': (measure_object_intensity, {
                    'select_object_sets_to_measure': 'SSC'
                })
        },
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (measure_object_intensity_distribution, {
                    'wants_zernikes': IntensityDistributionZernikeMode.MAGNITUDES_AND_PHASE,
                    'select_objects_to_use_as_centers': 'None',
                    'select_object_sets_to_measure': 'BF_cells_on_grid'
                }),
            '3': (measure_object_intensity_distribution, {
                    'wants_zernikes': IntensityDistributionZernikeMode.MAGNITUDES_AND_PHASE,
                    'select_objects_to_use_as_centers': 'None',
                    'select_object_sets_to_measure': 'BF_cells_on_grid'
                }),
            '2': (measure_object_intensity_distribution, {
                    'wants_zernikes': IntensityDistributionZernikeMode.MAGNITUDES_AND_PHASE,
                    'select_objects_to_use_as_centers': 'None',
                    'select_object_sets_to_measure': 'SSC'
                })
        },
        name='MeasureObjectIntensityDistribution',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(export_to_spreadsheet, {
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