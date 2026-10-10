# OpenHCS pipeline

from openhcs.constants.constants import (
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
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceProjectionRole,
    SourceSelector,
)
from openhcs.core.source_metadata import (
    SourceVoxelSpacing,
    SourceVoxelSpacingUnit,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.outlines import OutlineSourceKind
from openhcs.processing.backends.cellprofiler.save_images import SaveImagesBitDepth
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
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
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern='^Channel (?P<ChannelNumber>[0-9])-[0-9]{2}-(?P<WellRow>[A-P])-(?P<WellCol>[0-9]{2})'
            ),
            MetadataExtractionRule(
                source=MetadataSource.FOLDER_NAME,
                pattern='(?P<Folder>.*)$'
            )
        ),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.METADATA,
            dimensions=(
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='IllumProtein',
                            metadata_field='Folder'
                        ),
                        SourceBindingMatchField(
                            alias='OrigDNA',
                            metadata_field='Folder'
                        ),
                        SourceBindingMatchField(
                            alias='IllumDNA',
                            metadata_field='Folder'
                        ),
                        SourceBindingMatchField(
                            alias='OrigProtein',
                            metadata_field='Folder'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='OrigDNA',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigProtein',
                            metadata_field='Well'
                        )
                    )
                )
            )
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
                name='ChannelNumber',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='WellRow',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='WellCol',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Folder',
                dtype=str,
                required=False
            )
        ),
        source_filters=(
            SourceFilterClause(
                subject=SourceFilterSubject.EXTENSION,
                match_type=SourceFilterMatchType.IS_IMAGE,
                any_group=0
            ),
            SourceFilterClause(
                subject=SourceFilterSubject.FILE,
                match_type=SourceFilterMatchType.ENDS_WITH,
                value='.npy',
                any_group=0
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='OrigProtein',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Channel 1'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='OrigDNA',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Channel 2'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                source_channel_axis=-1
            ),
            NamedSourceBinding(
                alias='IllumProtein',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='VitraChannel1ILLUM.npy'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            ),
            NamedSourceBinding(
                alias='IllumDNA',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='VitraChannel2ILLUM.npy'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleVitra/candidate/-1')
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
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'select_the_input_image': 'OrigProtein',
                'select_the_illumination_function': 'IllumProtein',
                'name_the_output_image': 'CorrProtein'
            }),
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'select_the_input_image': 'OrigDNA',
                'select_the_illumination_function': 'IllumDNA',
                'name_the_output_image': 'CorrDNA'
            }),
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 5,
                'max_diameter': 30,
                'maxima_suppression_size': 5.0,
                'name_the_primary_objects_to_be_identified': 'Nuclei'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_secondary_objects'), {
                'method': SecondaryMethod.DISTANCE_B,
                'threshold_method': CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
                'distance_to_dilate': 8,
                'fill_holes': False,
                'select_the_input_image': 'CorrProtein',
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
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cells',
                    'Cytoplasm'
                ),
                'select_images_to_measure': 'CorrProtein'
            }),
        name='MeasureObjectIntensity'
    ),
    FunctionStep(
        func=[
            (get_function('openhcs:cellprofiler_calculate_math'), {
                    'operand1_feature': 'Intensity_MeanIntensity_CorrProtein',
                    'operand2_feature': 'Intensity_MeanIntensity_CorrProtein',
                    'operation': ImageMathOperation.DIVIDE,
                    'output_name': 'Ratio1',
                    'select_the_numerator_objects': 'Nuclei',
                    'select_the_denominator_objects': 'Cells'
                }),
            (get_function('openhcs:cellprofiler_calculate_math'), {
                    'operand1_feature': 'Intensity_MeanIntensity_CorrProtein',
                    'operand2_feature': 'Intensity_MeanIntensity_CorrProtein',
                    'operation': ImageMathOperation.DIVIDE,
                    'output_name': 'Ratio2',
                    'select_the_numerator_objects': 'Cytoplasm',
                    'select_the_denominator_objects': 'Cells'
                })
        ],
        name='CalculateMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'outline_source_kinds': (
                    OutlineSourceKind.OBJECTS,
                    OutlineSourceKind.OBJECTS
                ),
                'outline_colors': (
                    'Blue',
                    'Green'
                ),
                'select_image_on_which_to_display_outlines': 'CorrProtein',
                'select_objects_to_display': (
                    'Nuclei',
                    'Cells'
                ),
                'name_the_output_image': 'Outlined'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigProtein',
                'append_suffix': True,
                'filename_suffix': '_Outlined',
                'bit_depth': SaveImagesBitDepth.UINT8,
                'base_image_folder': 'Elsewhere...|/Users/veneskey/svn/pipeline/ExampleImages/ExampleVitraImages',
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'OrigProtein',
                'select_the_image_to_save': 'Outlined'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='OrigProtein',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS,
                                value='Channel 1'
                            ),
                        )
                    ),
                    origin=SourceBindingOrigin.PIPELINE_START,
                    load_as_monochrome=True
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