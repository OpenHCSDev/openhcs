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
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.outlines import (
    LineMode,
    OutlineSourceKind,
)
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFileFormat,
)
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
                alias='DNA',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='d0.tif'
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
                alias='PH3',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='d1.tif'
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
                alias='cellbody',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='d2.tif'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/ExampleHuman/candidate/-1')
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
                    'min_diameter': 8,
                    'max_diameter': 80,
                    'fill_holes': FillHolesOption.AFTER_DECLUMP,
                    'use_advanced_settings': False,
                    'adaptive_window_size': 50,
                    'name_the_primary_objects_to_be_identified': 'Nuclei'
                }),
            '2': (get_function('openhcs:cellprofiler_identify_primary_objects'), {
                    'min_diameter': 7,
                    'max_diameter': 80,
                    'fill_holes': FillHolesOption.AFTER_DECLUMP,
                    'threshold_method': CellProfilerThresholdMethod.OTSU,
                    'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                    'adaptive_window_size': 50,
                    'name_the_primary_objects_to_be_identified': 'PH3'
                })
        },
        name='IdentifyPrimaryObjects',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'save_children_with_parents': False
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func={
            '3': (get_function('openhcs:cellprofiler_identify_secondary_objects'), {
                    'threshold_method': CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
                    'threshold_correction_factor': 0.8,
                    'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                    'adaptive_window_size': 50,
                    'select_the_input_image': 'cellbody',
                    'select_the_input_objects': 'Nuclei',
                    'name_the_objects_to_be_identified': 'Cells'
                })
        },
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
                    'Nuclei',
                    'Cells',
                    'Cytoplasm'
                ),
                'select_images_to_measure': (
                    'DNA',
                    'PH3'
                )
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cells',
                    'Cytoplasm'
                )
            }),
        name='MeasureObjectSizeShape',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE
        )
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_overlay_outlines'), {
                    'line_mode': LineMode.THICK,
                    'outline_source_kinds': (
                        OutlineSourceKind.OBJECTS,
                        OutlineSourceKind.OBJECTS,
                        OutlineSourceKind.OBJECTS
                    ),
                    'outline_colors': (
                        '#0080FF',
                        'blue',
                        'yellow'
                    ),
                    'select_image_on_which_to_display_outlines': 'DNA',
                    'select_objects_to_display': (
                        'Cells',
                        'Nuclei',
                        'PH3'
                    ),
                    'name_the_output_image': 'OrigOverlay'
                })
        },
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images_with_measurements'), {
                'saved_image_name': 'OrigOverlay',
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': '_Overlay',
                'file_format': SaveImagesFileFormat.PNG,
                'bit_depth': SaveImagesBitDepth.UINT8,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': True,
                'select_image_name_for_file_prefix': 'DNA'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='DNA',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS,
                                value='d0.tif'
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
            )
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
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