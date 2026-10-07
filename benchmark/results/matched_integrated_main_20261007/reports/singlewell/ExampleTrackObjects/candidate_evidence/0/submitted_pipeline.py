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
    MetadataExtractionRule,
    MetadataSource,
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
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFileFormat,
    SaveImagesFilenameMethod,
)
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
from openhcs.processing.backends.cellprofiler.thresholding import (
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
            'Sequence1'
        ]
    ),
    zarr_config=LazyZarrConfig(),
    tiff_config=LazyTiffConfig(),
    vfs_config=LazyVFSConfig(),
    dtype_config=LazyDtypeConfig(),
    processing_config=LazyProcessingConfig(
        variable_components=[
            VariableComponents.TIMEPOINT
        ],
        group_by=GroupBy.CHANNEL,
        input_source=InputSource.PREVIOUS_STEP
    ),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern='^(?P<Specimen>.*)_(?P<Stain>.*)_(?P<FrameNumber>[0-9]*)',
                filters=(
                    SourceFilterClause(
                        subject=SourceFilterSubject.FILE,
                        match_type=SourceFilterMatchType.CONTAINS_REGEX,
                        value='GFPHistone'
                    ),
                )
            ),
            MetadataExtractionRule(
                source=MetadataSource.FOLDER_NAME,
                pattern='.*[\\/](?P<Run>.*)$',
                filters=(
                    SourceFilterClause(
                        subject=SourceFilterSubject.FILE,
                        match_type=SourceFilterMatchType.CONTAINS_REGEX,
                        value='GFPHistone'
                    ),
                )
            )
        ),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.ORDER
        ),
        metadata_fields=(
            FieldSpec(
                name='FileLocation',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Frame',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Series',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Specimen',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Stain',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='FrameNumber',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Run',
                dtype=str,
                required=False
            )
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
                alias='OrigColor',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS_REGEX,
                            value='GFPHistone'
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
        grouping_metadata_fields=(
            'Run',
        ),
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleTrackObjects/candidate/0')
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
        func=(get_function('openhcs:cellprofiler_color_to_gray'), {
                'mode': ColorToGrayMode.COMBINE,
                'name_the_output_image': 'OrigGray'
            }),
        name='ColorToGray',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 25,
                'max_diameter': 9999,
                'threshold_min': 0.01,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'Embryos'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=get_function('openhcs:cellprofiler_measure_object_intensity'),
        name='MeasureObjectIntensity'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_track_objects'), {
                'save_color_coded_image': True
            }),
        name='TrackObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'select_image_on_which_to_display_outlines': 'OrigGray',
                'name_the_output_image': 'OutlineImage'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_tile'), {
                'rows': 1,
                'auto_columns': True,
                'tile_assembly_method': 'within_cycles',
                'select_an_input_image': 'OrigColor',
                'select_an_additional_image_to_tile': (
                    'OutlineImage',
                    'TrackedCells'
                ),
                'name_the_output_image': 'AdjacentImage'
            }),
        name='Tile',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                'single_file_name': '\\g<Specimen>-\\g<FrameNumber>',
                'file_format': SaveImagesFileFormat.PNG,
                'output_location': '\\g<Run>',
                'bit_depth': SaveImagesBitDepth.UINT8,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False,
                'select_the_image_to_save': 'AdjacentImage'
            }),
        name='SaveImages'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'add_image_metadata': True,
                'calculate_aggregate_means': True,
                'output_directory': '{Run}',
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
                            'Embryos',
                        ),
                        file_name='Embryos.csv'
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