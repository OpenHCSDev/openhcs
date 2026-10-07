# OpenHCS pipeline

from openhcs.constants.constants import (
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
    ImportedMetadataJoin,
    ImportedMetadataTable,
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
from openhcs.interop.cellprofiler.analyst_export import CellProfilerObjectTableMode
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.save_images import SaveImagesBitDepth
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod
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
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern='^(?P<Plate>.*)_(?P<Well>[A-P][0-9]{2})_s(?P<Site>[0-9])_w(?P<ChannelNumber>[0-9])'
            ),
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
                dtype=int,
                required=False
            ),
            FieldSpec(
                name='Series',
                dtype=int,
                required=False
            ),
            FieldSpec(
                name='Plate',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Well',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Site',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='ChannelNumber',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Dose',
                dtype=float,
                required=False
            ),
            FieldSpec(
                name='PosNegCtrls',
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
                value='[\\/]\\.'
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='rawDNA',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='w2'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='rawGFP',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='w1'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                load_as_monochrome=True
            )
        ),
        image_plane_sources=(),
        imported_metadata_tables=(
            ImportedMetadataTable(
                location='Downloads/TranslocationData/Translocation_doses_and_controls.csv',
                joins=(
                    ImportedMetadataJoin(
                        image_metadata_field='Well',
                        imported_metadata_field='Well'
                    ),
                )
            ),
        ),
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/cp_tutorial_translocation_final/candidate/0')
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
                'smoothing_filter_size': 6,
                'maxima_suppression_size': 6.7,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'adaptive_window_size': 64,
                'number_of_deviations': 1.0,
                'select_the_input_image': 'rawDNA',
                'name_the_primary_objects_to_be_identified': 'Nuclei'
            }),
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_secondary_objects'), {
                'method': SecondaryMethod.DISTANCE_N,
                'threshold_method': CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
                'threshold_correction_factor': 0.1,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'select_the_input_image': 'rawGFP',
                'select_the_input_objects': 'Nuclei',
                'name_the_objects_to_be_identified': 'Cells'
            }),
        name='IdentifySecondaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
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
                    'Cytoplasm',
                    'Nuclei'
                ),
                'select_images_to_measure': 'rawGFP'
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_colocalization_objects'), {
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cytoplasm'
                ),
                'select_images_to_measure': (
                    'rawDNA',
                    'rawGFP'
                )
            }),
        name='MeasureColocalization',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_calculate_math'), {
                'operand1_feature': 'Intensity_MeanIntensity_rawGFP',
                'operand2_feature': 'Intensity_MeanIntensity_rawGFP',
                'operation': ImageMathOperation.DIVIDE,
                'output_name': 'IntensityRatio',
                'select_the_numerator_objects': 'Nuclei',
                'select_the_denominator_objects': 'Cytoplasm'
            }),
        name='CalculateMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_gray_to_color'), {
                'rescale_intensity': False,
                'green_channel': 0,
                'blue_channel': 1,
                'select_the_image_to_be_colored_green': 'rawGFP',
                'select_the_image_to_be_colored_blue': 'rawDNA',
                'name_the_output_image': 'GFPandDNA'
            }),
        name='GrayToColor',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'outline_colors': (
                    '#21FFFF',
                ),
                'select_image_on_which_to_display_outlines': 'GFPandDNA',
                'select_objects_to_display': 'Nuclei',
                'name_the_output_image': 'CellAndNucleiOverlay'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': '_Overlay',
                'bit_depth': SaveImagesBitDepth.UINT8,
                'overwrite': False,
                'base_image_folder': 'Elsewhere...|',
                'lossless_compression': False,
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'rawGFP',
                'select_the_image_to_save': 'CellAndNucleiOverlay'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='rawGFP',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS,
                                value='w1'
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
        func=(get_function('openhcs:cellprofiler_export_to_database'), {
                'table_prefix': 'Expt_',
                'object_table_mode': CellProfilerObjectTableMode.COMBINED,
                'location_object': 'Nuclei',
                'calculate_per_image_mean': True,
                'write_image_thumbnails': True,
                'thumbnail_image_names': (
                    'rawDNA',
                    'rawGFP'
                ),
                'plate_type': '96'
            }),
        name='ExportToDatabase',
        processing_config=LazyProcessingConfig(
            variable_components=[],
            group_by=GroupBy.NONE
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True
        )
    )
]