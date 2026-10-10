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
    MetadataExtractionRule,
    MetadataSelector,
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
from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.intensity import (
    AutomaticHigh,
    AutomaticLow,
)
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.save_images import SaveImagesBitDepth
from openhcs.processing.backends.cellprofiler.structuring_elements import StructuringElement
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerOtsuMethod,
    CellProfilerThresholdMethod,
)
from openhcs.processing.backends.cellprofiler.watershed import WatershedMethod
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
            VariableComponents.Z_INDEX
        ],
        group_by=GroupBy.CHANNEL,
        input_source=InputSource.PREVIOUS_STEP
    ),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern='^(?P<Plate>.*)_xy(?P<Site>[0-9])_ch(?P<ChannelNumber>[0-9])'
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
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Series',
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Plate',
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
                alias='origDNA',
                selector=SourceSelector(
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='2'
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
                alias='origMito',
                selector=SourceSelector(
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='1'
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
                alias='origMemb',
                selector=SourceSelector(
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='0'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='0'
                    ),
                ),
                load_as_monochrome=True
            )
        ),
        image_plane_sources=(),
        imported_metadata_tables=(),
        source_stack_components=(
            AllComponents.Z_INDEX,
        ),
        source_spatial_domain=VolumeSourceSpatialDomain(),
        grouping_metadata_fields=(),
        source_voxel_spacing=SourceVoxelSpacing(
            values_zyx=(
                1.1153846153846152,
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261006/runtime-artifact-last-consumer-resumed-singlewell-v1/singlewell/capture/cases/cp_tutorial_3d_monolayer/candidate/-1')
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
            '2': (get_function('openhcs:cellprofiler_rescale_intensity'), {
                    'automatic_low': AutomaticLow.CUSTOM,
                    'automatic_high': AutomaticHigh.CUSTOM,
                    'name_the_output_image': 'RescaledDNA'
                })
        },
        name='RescaleIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_resize_volumetric'), {
                'resizing_factor_x': 0.5,
                'resizing_factor_y': 0.5,
                'resizing_factor_z': 1.0,
                'name_the_output_image': 'ResizedDNA'
            }),
        name='Resize'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_medianfilter'), {
                'window_size': 5,
                'name_the_output_image': 'MedianFiltDNA'
            }),
        name='MedianFilter'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_threshold'), {
                'name_the_output_image': 'maskDNA'
            }),
        name='Threshold'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_remove_holes_3d'), {
                'diameter': 20.0,
                'name_the_output_image': 'noHolesMaskDNA'
            }),
        name='RemoveHoles'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_watershed_cellprofiler4'), {
                'use_advanced_settings': False,
                'downsample': 2,
                'footprint': 10,
                'gaussian_sigma': 1.0,
                'name_the_output_object': 'downsizedNuclei'
            }),
        name='Watershed'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_resize_objects_3d'), {
                'factor_x': 2.0,
                'factor_y': 2.0,
                'factor_z': 1.0,
                'name_the_output_object': 'Nuclei'
            }),
        name='ResizeObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_erode_objects'), {
                'structuring_element': StructuringElement.BALL,
                'size': 5,
                'select_the_input_object': 'downsizedNuclei',
                'name_the_output_object': 'erodedDownsizedNuclei'
            }),
        name='ErodeObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_resize_objects_3d'), {
                'factor_x': 2.0,
                'factor_y': 2.0,
                'factor_z': 1.0,
                'select_the_input_object': 'erodedDownsizedNuclei',
                'name_the_output_object': 'erodedResizedNuclei'
            }),
        name='ResizeObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'select_the_input_objects': 'erodedResizedNuclei',
                'name_the_output_image': 'cellSeeds'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func={
            '0': (get_function('openhcs:cellprofiler_threshold'), {
                    'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                    'name_the_output_image': 'MembThreshold'
                })
        },
        name='Threshold',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.INVERT,
                'name_the_output_image': 'MembInvert'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_remove_holes_3d'), {
                'diameter': 20.0,
                'name_the_output_image': 'MembInvertRemoveHoles'
            }),
        name='RemoveHoles'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'factors': (
                    1.0,
                    1.0,
                    1.0
                ),
                'select_the_second_image': 'origMemb',
                'select_the_third_image': 'origMito',
                'name_the_output_image': 'Monolayer'
            }),
        name='ImageMath',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_resize_volumetric'), {
                'resizing_factor_z': 1.0,
                'name_the_output_image': 'DownsizedMonolayer'
            }),
        name='Resize'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_closing'), {
                'size': 17,
                'name_the_output_image': 'ClosedDownsizedMonolayer'
            }),
        name='Closing'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_resize_volumetric'), {
                'resizing_factor_x': 4.0,
                'resizing_factor_y': 4.0,
                'resizing_factor_z': 1.0,
                'name_the_output_image': 'ResizedClosedMonolayer'
            }),
        name='Resize'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_threshold'), {
                'threshold_method': CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
                'name_the_output_image': 'MonolayerMask'
            }),
        name='Threshold'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_mask_image'), {
                'select_the_input_image': 'MembInvertRemoveHoles',
                'select_image_for_mask': 'MonolayerMask',
                'name_the_output_image': 'MembMasked'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_erode_image'), {
                'structuring_element': StructuringElement.BALL,
                'size': 1,
                'slice_by_slice': False,
                'name_the_output_image': 'MembFinal'
            }),
        name='ErodeImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_watershed_cellprofiler4'), {
                'watershed_method': WatershedMethod.MARKERS,
                'use_advanced_settings': False,
                'gaussian_sigma': 1.0,
                'select_the_input_image': 'MembFinal',
                'markers': 'cellSeeds',
                'mask': 'MembFinal',
                'name_the_output_object': 'Cells'
            }),
        name='Watershed'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cells'
                ),
                'select_images_to_measure': (
                    'origDNA',
                    'origMemb'
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
                'calculate_zernikes': False,
                'select_object_sets_to_measure': (
                    'Nuclei',
                    'Cells'
                )
            }),
        name='MeasureObjectSizeShape',
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.NONE
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_objects'), {
                'opacity': 0.2,
                'select_the_input_image': 'RescaledDNA',
                'select_objects_to_display': 'Nuclei'
            }),
        name='OverlayObjects'
    ),
    FunctionStep(
        func={
            '0': (get_function('openhcs:cellprofiler_rescale_intensity'), {
                    'automatic_low': AutomaticLow.CUSTOM,
                    'automatic_high': AutomaticHigh.CUSTOM,
                    'name_the_output_image': 'RescaledMemb'
                })
        },
        name='RescaleIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_objects'), {
                'select_the_input_image': 'RescaledMemb',
                'select_objects_to_display': 'Cells'
            }),
        name='OverlayObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'select_the_input_objects': 'Nuclei',
                'name_the_output_image': 'NucleiImage'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': '_NucleiLabels',
                'bit_depth': SaveImagesBitDepth.UINT16,
                'base_image_folder': 'Elsewhere...|',
                'lossless_compression': False,
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'origDNA',
                'select_the_image_to_save': 'NucleiImage'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='origDNA',
                    selector=SourceSelector(
                        metadata=(
                            MetadataSelector(
                                field='ChannelNumber',
                                value='2'
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
            )
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.UINT16,
                'colormap_value': 'Default',
                'select_the_input_objects': 'Cells',
                'name_the_output_image': 'CellsImage'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': '_CellsLabels',
                'bit_depth': SaveImagesBitDepth.UINT16,
                'base_image_folder': 'Elsewhere...|',
                'lossless_compression': False,
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'origMemb',
                'select_the_image_to_save': 'CellsImage'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='origMemb',
                    selector=SourceSelector(
                        metadata=(
                            MetadataSelector(
                                field='ChannelNumber',
                                value='0'
                            ),
                        )
                    ),
                    origin=SourceBindingOrigin.PIPELINE_START,
                    component_identity=(
                        ComponentSelector(
                            component=AllComponents.CHANNEL,
                            value='0'
                        ),
                    ),
                    load_as_monochrome=True
                ),
            )
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'add_image_metadata': True,
                'filename_prefix': '3d_monolayer_',
                'overwrite_existing_files_without_warning': True
            }),
        name='ExportToSpreadsheet',
        processing_config=LazyProcessingConfig(
            variable_components=[],
            group_by=GroupBy.NONE
        )
    )
]