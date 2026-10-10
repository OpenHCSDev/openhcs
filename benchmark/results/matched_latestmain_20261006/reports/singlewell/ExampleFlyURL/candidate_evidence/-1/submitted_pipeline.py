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
    ImagePlaneSource,
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
from openhcs.processing.backends.cellprofiler.crop import CropModule
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFilenameMethod,
)
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
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
                value='[\\\\\\\\/]\\\\.'
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
                            value='D.TIF'
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
                            value='F.TIF'
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
                alias='OrigRed',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='R.TIF'
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
        image_plane_sources=(
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS002_D.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS002_F.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS002_R.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS076_D.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS076_F.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS076_R.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS218_D.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS218_F.TIF'
            ),
            ImagePlaneSource(
                uri='https://raw.githubusercontent.com/CellProfiler/examples/master/ExampleFly/images/01_POS218_R.TIF'
            )
        ),
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261006/runtime-artifact-last-consumer-resumed-singlewell-v1/singlewell/capture/cases/ExampleFlyURL/candidate/-1')
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
            '1': (get_function('openhcs:cellprofiler_crop'), {
                    'removal_method': CropModule.RemovalMethod.EDGES,
                    'left_right_rectangle_positions': (
                        501,
                        700
                    ),
                    'top_bottom_rectangle_positions': (
                        251,
                        450
                    ),
                    'ellipse_center': (
                        200,
                        500
                    ),
                    'ellipse_x_radius': 400.0,
                    'ellipse_y_radius': 200.0,
                    'name_the_output_image': 'CropBlue'
                })
        },
        name='Crop',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '2': (get_function('openhcs:cellprofiler_crop'), {
                    'crop_shape': CropModule.Shape.CROPPING,
                    'removal_method': CropModule.RemovalMethod.EDGES,
                    'left_right_rectangle_positions': (
                        300,
                        600
                    ),
                    'top_bottom_rectangle_positions': (
                        300,
                        600
                    ),
                    'ellipse_center': (
                        500,
                        500
                    ),
                    'ellipse_x_radius': 400.0,
                    'ellipse_y_radius': 200.0,
                    'name_the_output_image': 'CropGreen'
                }),
            '3': (get_function('openhcs:cellprofiler_crop'), {
                    'crop_shape': CropModule.Shape.CROPPING,
                    'removal_method': CropModule.RemovalMethod.EDGES,
                    'left_right_rectangle_positions': (
                        300,
                        600
                    ),
                    'top_bottom_rectangle_positions': (
                        300,
                        600
                    ),
                    'ellipse_center': (
                        500,
                        500
                    ),
                    'ellipse_x_radius': 400.0,
                    'ellipse_y_radius': 200.0,
                    'name_the_output_image': 'CropRed'
                })
        },
        name='Crop',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'maxima_suppression_size': 5.0,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'log_transform': True,
                'select_the_input_image': 'CropBlue',
                'name_the_primary_objects_to_be_identified': 'Nuclei'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_secondary_objects'), {
                'select_the_input_image': 'CropGreen',
                'select_the_input_objects': 'Nuclei',
                'name_the_objects_to_be_identified': 'Cells'
            }),
        name='IdentifySecondaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_tertiary_objects'), {
                'select_the_larger_identified_objects': 'Cells',
                'select_the_smaller_identified_objects': 'Nuclei',
                'name_the_tertiary_objects_to_be_identified': 'Cytoplasm'
            }),
        name='IdentifyTertiaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': (
                    'Cells',
                    'Nuclei',
                    'Cytoplasm'
                )
            }),
        name='MeasureObjectSizeShape',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cells',
                    'Cytoplasm'
                ),
                'select_images_to_measure': 'CropBlue'
            }),
        name='MeasureObjectIntensity'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_texture_objects'), {
                'measurement_scope': CellProfilerMeasurementTargetScope.BOTH,
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cells',
                    'Cytoplasm'
                ),
                'select_images_to_measure': 'CropBlue'
            }),
        name='MeasureTexture'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_gray_to_color'), {
                'rescale_intensity': False,
                'red_channel': 0,
                'green_channel': 1,
                'blue_channel': 2,
                'select_the_image_to_be_colored_red': 'CropRed',
                'select_the_image_to_be_colored_green': 'CropGreen',
                'select_the_image_to_be_colored_blue': 'CropBlue',
                'name_the_output_image': 'RGBImage'
            }),
        name='GrayToColor',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'filename_method': SaveImagesFilenameMethod.SEQUENTIAL_NUMBERS,
                'single_file_name': 'CroppedFlyImage',
                'append_suffix': True,
                'filename_suffix': 'RGB',
                'bit_depth': SaveImagesBitDepth.UINT8,
                'overwrite': False,
                'base_image_folder': 'Default Input Folder',
                'record_file_and_path': False,
                'select_the_image_to_save': 'RGBImage'
            }),
        name='SaveImages'
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
                            'Nuclei',
                        ),
                        file_name='Nuclei.csv'
                    ),
                    SpreadsheetFileSelection(
                        subjects=(
                            'Cells',
                        ),
                        file_name='Cells.csv'
                    ),
                    SpreadsheetFileSelection(
                        subjects=(
                            'Cytoplasm',
                        ),
                        file_name='Cytoplasm.csv'
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