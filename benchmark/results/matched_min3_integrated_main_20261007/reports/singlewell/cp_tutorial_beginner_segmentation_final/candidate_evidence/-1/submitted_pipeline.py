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
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.outlines import OutlineSourceKind
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
)
from openhcs.processing.backends.cellprofiler.save_images import SaveImagesBitDepth
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
            'A14'
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
                pattern='(?P<Plate>.*)_(?P<Well>[A-P]{1}[0-9]{2})_site(?P<Site>[0-9])_Ch(?P<ChannelNumber>[1-5]).tif'
            ),
        ),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.METADATA,
            dimensions=(
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='OrigER',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigMito',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigDNA',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigRNA',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigActin_Golgi_Membrane',
                            metadata_field='Well'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='OrigER',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigMito',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigDNA',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigRNA',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigActin_Golgi_Membrane',
                            metadata_field='Site'
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
                dtype=int,
                required=False
            ),
            FieldSpec(
                name='ChannelNumber',
                dtype=int,
                required=False
            ),
            FieldSpec(
                name='Date',
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
                match_type=SourceFilterMatchType.CONTAINS,
                value='.npy',
                any_group=0
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='OrigDNA',
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
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='OrigER',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch2'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='OrigRNA',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch3'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='OrigActin_Golgi_Membrane',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch4'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='OrigMito',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='Ch5'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/cp_tutorial_beginner_segmentation_final/candidate/-1')
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
                'max_diameter': 150,
                'unclump_method': UnclumpMethod.SHAPE,
                'watershed_method': WatershedMethod.SHAPE,
                'automatic_smoothing': False,
                'smoothing_filter_size': 20,
                'automatic_suppression': False,
                'maxima_suppression_size': 20.0,
                'fill_holes': FillHolesOption.AFTER_DECLUMP,
                'threshold_correction_factor': 0.9,
                'threshold_min': 0.002,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'select_the_input_image': 'OrigDNA',
                'name_the_primary_objects_to_be_identified': 'Nuclei'
            }),
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_secondary_objects'), {
                'threshold_correction_factor': 0.7,
                'threshold_min': 0.003,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'regularization_factor': 0.005,
                'select_the_input_image': 'OrigActin_Golgi_Membrane',
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
                'shrink_primary': False,
                'select_the_larger_identified_objects': 'Cells',
                'select_the_smaller_identified_objects': 'Nuclei',
                'name_the_tertiary_objects_to_be_identified': 'Cytoplasm'
            }),
        name='IdentifyTertiaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_enhance_or_suppress_features'), {
                'radius': 5.0,
                'neurite_method': NeuriteMethod.TUBENESS,
                'select_the_input_image': 'OrigRNA',
                'name_the_output_image': 'FilteredRNA'
            }),
        name='EnhanceOrSuppressFeatures',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'FilteredRNA',
                'select_object_for_mask': 'Nuclei',
                'name_the_output_image': 'RNA_in_Nuclei'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 2,
                'max_diameter': 15,
                'exclude_border_objects': False,
                'watershed_method': WatershedMethod.SHAPE,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'name_the_primary_objects_to_be_identified': 'Nucleoli'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'outline_source_kinds': (
                    OutlineSourceKind.OBJECTS,
                    OutlineSourceKind.OBJECTS
                ),
                'outline_colors': (
                    'Red',
                    'Green'
                ),
                'select_image_on_which_to_display_outlines': 'OrigRNA',
                'select_objects_to_display': (
                    'Nuclei',
                    'Nucleoli'
                ),
                'name_the_output_image': 'SanityCheck'
            }),
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': (
                    'Cells',
                    'Cytoplasm',
                    'Nuclei',
                    'Nucleoli'
                ),
                'select_images_to_measure': (
                    'OrigDNA',
                    'OrigER',
                    'OrigMito',
                    'OrigRNA'
                )
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'select_object_sets_to_measure': (
                    'Cells',
                    'Cytoplasm',
                    'Nuclei',
                    'Nucleoli'
                )
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_colocalization_objects'), {
                'do_costes': False,
                'select_object_sets_to_measure': (
                    'Cells',
                    'Cytoplasm',
                    'Nuclei',
                    'Nucleoli'
                ),
                'select_images_to_measure': (
                    'OrigActin_Golgi_Membrane',
                    'OrigDNA',
                    'OrigER',
                    'OrigMito',
                    'OrigRNA'
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
        func=(get_function('openhcs:cellprofiler_relate_objects_with_saved_children'), {
                'calculate_per_parent_means': True,
                'save_children_with_parents': True,
                'select_the_child_objects': 'Nucleoli',
                'select_the_parent_objects': 'Nuclei',
                'name_the_output_object': 'NucleoliChildObjects'
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': '_overlay',
                'output_location': 'overlay_images',
                'bit_depth': SaveImagesBitDepth.UINT8,
                'overwrite': False,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'OrigRNA',
                'select_the_image_to_save': 'SanityCheck'
            }),
        name='SaveImages',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'overwrite_existing_files_without_warning': False
            }),
        name='ExportToSpreadsheet',
        processing_config=LazyProcessingConfig(
            variable_components=[],
            group_by=GroupBy.NONE
        )
    )
]