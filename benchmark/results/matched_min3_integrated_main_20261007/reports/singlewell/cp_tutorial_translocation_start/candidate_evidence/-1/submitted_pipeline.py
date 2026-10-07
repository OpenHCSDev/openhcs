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
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFilenameMethod,
)
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerAveragingMethod,
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/cp_tutorial_translocation_start/candidate/-1')
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
                'min_diameter': 50,
                'max_diameter': 60,
                'smoothing_filter_size': 6,
                'maxima_suppression_size': 6.7,
                'threshold_correction_factor': 4.0,
                'threshold_method': CellProfilerThresholdMethod.ROBUST_BACKGROUND,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'adaptive_window_size': 64,
                'lower_outlier_fraction': 0.02,
                'upper_outlier_fraction': 0.02,
                'averaging_method': CellProfilerAveragingMethod.MODE,
                'number_of_deviations': 0.0,
                'select_the_input_image': 'rawDNA',
                'name_the_primary_objects_to_be_identified': 'Nuclei'
            }),
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'name_the_output_image': 'OpenHCSReferenceLabels_Nuclei'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'filename_method': SaveImagesFilenameMethod.SINGLE_NAME,
                'single_file_name': 'reference_labels__Nuclei',
                'bit_depth': SaveImagesBitDepth.UINT16,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False
            }),
        name='SaveImages'
    )
]