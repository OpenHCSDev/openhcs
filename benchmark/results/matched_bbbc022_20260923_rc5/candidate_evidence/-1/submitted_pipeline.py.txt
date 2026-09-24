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
    LazyVFSConfig,
    LazyWellFilterConfig,
    LazyZarrConfig,
    PipelineConfig,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImportedMetadataJoin,
    ImportedMetadataTable,
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    MetadataExtractionRule,
    MetadataSelector,
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
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.colocalization import measure_colocalization_objects
from openhcs.processing.backends.cellprofiler.export_to_database import export_to_database
from openhcs.processing.backends.cellprofiler.feature_enhancement import (
    NeuriteMethod,
    enhance_or_suppress_features,
)
from openhcs.processing.backends.cellprofiler.illumination import correct_illumination_apply
from openhcs.processing.backends.cellprofiler.image_geometry import (
    MaskSource,
    mask_image,
)
from openhcs.processing.backends.cellprofiler.intensity import measure_object_intensity
from openhcs.processing.backends.cellprofiler.intensity_distribution import measure_object_intensity_distribution
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.neighbors import (
    DistanceMethod,
    measure_object_neighbors,
)
from openhcs.processing.backends.cellprofiler.primary_objects import (
    UnclumpMethod,
    WatershedMethod,
    identify_primary_objects,
)
from openhcs.processing.backends.cellprofiler.relationships import relate_objects_with_saved_children
from openhcs.processing.backends.cellprofiler.secondary import (
    identify_secondary_objects,
    identify_tertiary_objects,
)
from openhcs.processing.backends.cellprofiler.shape import measure_object_size_shape
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerOtsuMethod,
    CellProfilerThresholdAssignment,
    CellProfilerThresholdMethod,
)
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
            'A01',
            'A12',
            'B01',
            'B12',
            'C01',
            'C12',
            'D01',
            'D12'
        ]
    ),
    zarr_config=LazyZarrConfig(),
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
                pattern='(?P<Well>[A-P][0-9]{2})_s(?P<Site>[0-9])_w(?P<ChannelNumber>[0-9])',
                filters=(
                    SourceFilterClause(
                        subject=SourceFilterSubject.FILE,
                        match_type=SourceFilterMatchType.DOES_NOT_CONTAIN,
                        value='.npy'
                    ),
                )
            ),
            MetadataExtractionRule(
                source=MetadataSource.FOLDER_NAME,
                pattern='(?P<Plate>[0-9]{5})',
                filters=(
                    SourceFilterClause(
                        subject=SourceFilterSubject.FILE,
                        match_type=SourceFilterMatchType.DOES_NOT_CONTAIN,
                        value='.npy'
                    ),
                )
            ),
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern='^(?P<Plate>.*)_Illum',
                filters=(
                    SourceFilterClause(
                        subject=SourceFilterSubject.FILE,
                        match_type=SourceFilterMatchType.CONTAINS,
                        value='.npy'
                    ),
                )
            )
        ),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.METADATA,
            dimensions=(
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='IllumPh_golgi',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='IllumMito',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='OrigPh_golgi',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='IllumER',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='OrigHoechst',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='OrigER',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='IllumSyto',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='OrigSyto',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='OrigMito',
                            metadata_field='Plate'
                        ),
                        SourceBindingMatchField(
                            alias='IllumHoechst',
                            metadata_field='Plate'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='OrigPh_golgi',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigHoechst',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigER',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigSyto',
                            metadata_field='Well'
                        ),
                        SourceBindingMatchField(
                            alias='OrigMito',
                            metadata_field='Well'
                        )
                    )
                ),
                SourceBindingMatchDimension(
                    fields=(
                        SourceBindingMatchField(
                            alias='OrigPh_golgi',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigHoechst',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigER',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigSyto',
                            metadata_field='Site'
                        ),
                        SourceBindingMatchField(
                            alias='OrigMito',
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
                dtype=str,
                required=False
            ),
            FieldSpec(
                name='Series',
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
                name='Plate',
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
                alias='OrigHoechst',
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
                alias='OrigER',
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
                alias='OrigSyto',
                selector=SourceSelector(
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='3'
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
            ),
            NamedSourceBinding(
                alias='OrigPh_golgi',
                selector=SourceSelector(
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='4'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='4'
                    ),
                ),
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='OrigMito',
                selector=SourceSelector(
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='5'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='5'
                    ),
                ),
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='IllumMito',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumMito'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            ),
            NamedSourceBinding(
                alias='IllumPh_golgi',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumPh_golgi'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            ),
            NamedSourceBinding(
                alias='IllumSyto',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumSyto'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            ),
            NamedSourceBinding(
                alias='IllumER',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumER'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            ),
            NamedSourceBinding(
                alias='IllumHoechst',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumHoechst'
                        ),
                    )
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            )
        ),
        image_plane_sources=(),
        imported_metadata_tables=(
            ImportedMetadataTable(
                location='/Users/pryder/Documents/tutorials/AdvancedSegmentation/20585_AE.csv',
                joins=(
                    ImportedMetadataJoin(
                        image_metadata_field='Plate',
                        imported_metadata_field='Image_Metadata_PlateID'
                    ),
                    ImportedMetadataJoin(
                        image_metadata_field='Well',
                        imported_metadata_field='Image_Metadata_CPD_WELL_POSITION'
                    )
                )
            ),
        ),
        source_stack_components=(),
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
        global_output_folder=Path('/home/ts/code/projects/openhcs/benchmark/results/matched_bbbc022_20260923_rc5/candidate/-1')
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
            '1': (correct_illumination_apply, {
                    'select_the_input_image': 'OrigHoechst',
                    'select_the_illumination_function': 'IllumHoechst',
                    'name_the_output_image': 'Hoechst'
                }),
            '2': (correct_illumination_apply, {
                    'select_the_input_image': 'OrigER',
                    'select_the_illumination_function': 'IllumER',
                    'name_the_output_image': 'ER'
                }),
            '5': (correct_illumination_apply, {
                    'select_the_input_image': 'OrigMito',
                    'select_the_illumination_function': 'IllumMito',
                    'name_the_output_image': 'Mito'
                }),
            '4': (correct_illumination_apply, {
                    'select_the_input_image': 'OrigPh_golgi',
                    'select_the_illumination_function': 'IllumPh_golgi',
                    'name_the_output_image': 'Ph_golgi'
                }),
            '3': (correct_illumination_apply, {
                    'select_the_input_image': 'OrigSyto',
                    'select_the_illumination_function': 'IllumSyto',
                    'name_the_output_image': 'Syto'
                })
        },
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(identify_primary_objects, {
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
                'select_the_input_image': 'Hoechst',
                'name_the_primary_objects_to_be_identified': 'Nuclei'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(identify_secondary_objects, {
                'threshold_correction_factor': 0.7,
                'threshold_min': 0.003,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'regularization_factor': 0.005,
                'select_the_input_image': 'Ph_golgi',
                'select_the_input_objects': 'Nuclei',
                'name_the_objects_to_be_identified': 'Cells'
            }),
        name='IdentifySecondaryObjects'
    ),
    FunctionStep(
        func=(identify_tertiary_objects, {
                'shrink_primary': False,
                'select_the_larger_identified_objects': 'Cells',
                'select_the_smaller_identified_objects': 'Nuclei',
                'name_the_tertiary_objects_to_be_identified': 'Cytoplasm'
            }),
        name='IdentifyTertiaryObjects'
    ),
    FunctionStep(
        func=(enhance_or_suppress_features, {
                'radius': 5.0,
                'neurite_method': NeuriteMethod.TUBENESS,
                'select_the_input_image': 'Syto',
                'name_the_output_image': 'FilteredRNA'
            }),
        name='EnhanceOrSuppressFeatures'
    ),
    FunctionStep(
        func=(mask_image, {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'FilteredRNA',
                'select_object_for_mask': 'Nuclei',
                'name_the_output_image': 'SytoNuclei'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(identify_primary_objects, {
                'min_diameter': 3,
                'max_diameter': 15,
                'exclude_border_objects': False,
                'unclump_method': UnclumpMethod.SHAPE,
                'watershed_method': WatershedMethod.SHAPE,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'name_the_primary_objects_to_be_identified': 'Nucleoli'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(mask_image, {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'Mito',
                'select_object_for_mask': 'Cytoplasm',
                'name_the_output_image': 'MaskedMito'
            }),
        name='MaskImage'
    ),
    FunctionStep(
        func=(identify_primary_objects, {
                'min_diameter': 2,
                'max_diameter': 30,
                'exclude_border_objects': False,
                'fill_holes': FillHolesOption.AFTER_DECLUMP,
                'threshold_method': CellProfilerThresholdMethod.OTSU,
                'name_the_primary_objects_to_be_identified': 'Mitochondria'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=[
            (measure_colocalization_objects, {
                    'select_object_sets_to_measure': 'Cytoplasm',
                    'select_images_to_measure': (
                        'Mito',
                        'Syto',
                        'Ph_golgi',
                        'Hoechst',
                        'ER'
                    )
                }),
            (measure_colocalization_objects, {
                    'select_object_sets_to_measure': 'Nuclei',
                    'select_images_to_measure': (
                        'Mito',
                        'Syto',
                        'Ph_golgi',
                        'Hoechst',
                        'ER'
                    )
                }),
            (measure_colocalization_objects, {
                    'select_object_sets_to_measure': 'Cells',
                    'select_images_to_measure': (
                        'Mito',
                        'Syto',
                        'Ph_golgi',
                        'Hoechst',
                        'ER'
                    )
                }),
            (measure_colocalization_objects, {
                    'select_object_sets_to_measure': 'Nucleoli',
                    'select_images_to_measure': (
                        'Mito',
                        'Syto',
                        'Ph_golgi',
                        'Hoechst',
                        'ER'
                    )
                }),
            (measure_colocalization_objects, {
                    'select_object_sets_to_measure': 'Mitochondria',
                    'select_images_to_measure': (
                        'Mito',
                        'Syto',
                        'Ph_golgi',
                        'Hoechst',
                        'ER'
                    )
                })
        ],
        name='MeasureColocalization',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE
        )
    ),
    FunctionStep(
        func={
            '2': [
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'ER'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'ER'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'ER'
                    })
            ],
            '5': [
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Mito'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Mito'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Mito'
                    })
            ],
            '1': [
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Hoechst'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Hoechst'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Hoechst'
                    })
            ],
            '4': [
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Ph_golgi'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Ph_golgi'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Ph_golgi'
                    })
            ],
            '3': [
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Syto'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Syto'
                    }),
                (measure_object_intensity, {
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Syto'
                    })
            ]
        },
        name='MeasureObjectIntensity'
    ),
    FunctionStep(
        func={
            '5': [
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Mito'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Mito'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Mito'
                    })
            ],
            '3': [
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Syto'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cells'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Syto'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cytoplasm'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Syto'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Nuclei'
                    })
            ],
            '1': [
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'Hoechst'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'Hoechst'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'Hoechst'
                    })
            ],
            '2': [
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cells',
                        'select_images_to_measure': 'ER'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Cytoplasm',
                        'select_images_to_measure': 'ER'
                    }),
                (measure_object_intensity_distribution, {
                        'select_objects_to_use_as_centers': 'None',
                        'select_object_sets_to_measure': 'Nuclei',
                        'select_images_to_measure': 'ER'
                    })
            ]
        },
        name='MeasureObjectIntensityDistribution',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '4': [
                (measure_object_size_shape, {
                        'calculate_advanced': False,
                        'select_object_sets_to_measure': 'Cells'
                    }),
                (measure_object_size_shape, {
                        'calculate_advanced': False,
                        'select_object_sets_to_measure': 'Cytoplasm'
                    })
            ],
            '5': (measure_object_size_shape, {
                    'calculate_advanced': False,
                    'select_object_sets_to_measure': 'Mitochondria'
                }),
            '1': (measure_object_size_shape, {
                    'calculate_advanced': False,
                    'select_object_sets_to_measure': 'Nuclei'
                }),
            '3': (measure_object_size_shape, {
                    'calculate_advanced': False,
                    'select_object_sets_to_measure': 'Nucleoli'
                })
        },
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func={
            '4': (measure_object_neighbors, {
                    'distance_method': DistanceMethod.EXPAND,
                    'neighbor_distance': 5,
                    'select_objects_to_measure': 'Cells',
                    'select_neighboring_objects_to_measure': 'Cells'
                }),
            '1': (measure_object_neighbors, {
                    'distance_method': DistanceMethod.EXPAND,
                    'neighbor_distance': 5,
                    'select_objects_to_measure': 'Nuclei',
                    'select_neighboring_objects_to_measure': 'Nuclei'
                }),
            '5': (measure_object_neighbors, {
                    'distance_method': DistanceMethod.EXPAND,
                    'neighbor_distance': 5,
                    'select_objects_to_measure': 'Mitochondria',
                    'select_neighboring_objects_to_measure': 'Mitochondria'
                })
        },
        name='MeasureObjectNeighbors'
    ),
    FunctionStep(
        func={
            '3': (relate_objects_with_saved_children, {
                    'calculate_per_parent_means': True,
                    'save_children_with_parents': True,
                    'select_the_child_objects': 'Nucleoli',
                    'select_the_parent_objects': 'Nuclei',
                    'name_the_output_object': 'NucleoliChildObjects'
                }),
            '5': (relate_objects_with_saved_children, {
                    'calculate_per_parent_means': True,
                    'save_children_with_parents': True,
                    'select_the_parent_objects': 'Cells',
                    'select_the_child_objects': 'Mitochondria',
                    'name_the_output_object': 'MitochondriaChildObjects'
                })
        },
        name='RelateObjects'
    ),
    FunctionStep(
        func=(export_to_database, {
                'sqlite_file': 'BBBC022.db',
                'experiment_name': 'BBBC022',
                'table_prefix': 'MyExpt_',
                'wants_relationship_tables': True,
                'location_object': 'None',
                'plate_type': '384',
                'wants_group_fields': True,
                'group_fields': (
                    (
                        'PerWell',
                        'ImageNumber, Image_Metadata_Plate, Image_Metadata_Well'
                    ),
                )
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