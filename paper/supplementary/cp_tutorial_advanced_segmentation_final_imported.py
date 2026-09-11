# OpenHCS pipeline

from openhcs.constants.constants import (
    AllComponents,
    GroupBy,
    VariableComponents,
)
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import ImageArtifactType
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
    SourceSetRole,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
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

pipeline_config = PipelineConfig(
    materialization_results_path=None,
    materialize_runtime_artifacts=None,
    num_workers=None,
    microscope=None,
    use_threading=None,
    multiprocessing_start_method=None,
    auto_add_output_plate_to_plate_manager=None,
    napari_display_config=LazyNapariDisplayConfig(
        colormap=None,
        variable_size_handling=None,
        site_mode=None,
        channel_mode=None,
        z_index_mode=None,
        timepoint_mode=None,
        well_mode=None
    ),
    fiji_display_config=LazyFijiDisplayConfig(
        lut=None,
        auto_contrast=None,
        site_mode=None,
        channel_mode=None,
        z_index_mode=None,
        timepoint_mode=None,
        well_mode=None
    ),
    well_filter_config=LazyWellFilterConfig(
        well_filter=None,
        well_filter_mode=None
    ),
    zarr_config=LazyZarrConfig(
        compressor=None,
        compression_level=None,
        chunk_strategy=None
    ),
    vfs_config=LazyVFSConfig(
        read_backend=None,
        intermediate_backend=None,
        materialization_backend=None
    ),
    dtype_config=LazyDtypeConfig(
        default_dtype_conversion=None
    ),
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
                        value='.npy',
                        any_group=None
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
                        value='.npy',
                        any_group=None
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
                        value='.npy',
                        any_group=None
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
                value=None,
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
                    components=(),
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='1'
                        ),
                    ),
                    filters=(),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='1'
                    ),
                ),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.PRIMARY_PLANE,
                explicit_source=None,
                load_as_monochrome=True,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='OrigER',
                selector=SourceSelector(
                    components=(),
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='2'
                        ),
                    ),
                    filters=(),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='2'
                    ),
                ),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.PRIMARY_PLANE,
                explicit_source=None,
                load_as_monochrome=True,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='OrigSyto',
                selector=SourceSelector(
                    components=(),
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='3'
                        ),
                    ),
                    filters=(),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='3'
                    ),
                ),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.PRIMARY_PLANE,
                explicit_source=None,
                load_as_monochrome=True,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='OrigPh_golgi',
                selector=SourceSelector(
                    components=(),
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='4'
                        ),
                    ),
                    filters=(),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='4'
                    ),
                ),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.PRIMARY_PLANE,
                explicit_source=None,
                load_as_monochrome=True,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='OrigMito',
                selector=SourceSelector(
                    components=(),
                    metadata=(
                        MetadataSelector(
                            field='ChannelNumber',
                            value='5'
                        ),
                    ),
                    filters=(),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='5'
                    ),
                ),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.PRIMARY_PLANE,
                explicit_source=None,
                load_as_monochrome=True,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='IllumMito',
                selector=SourceSelector(
                    components=(),
                    metadata=(),
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumMito',
                            any_group=None
                        ),
                    ),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
                explicit_source=None,
                load_as_monochrome=False,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='IllumPh_golgi',
                selector=SourceSelector(
                    components=(),
                    metadata=(),
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumPh_golgi',
                            any_group=None
                        ),
                    ),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
                explicit_source=None,
                load_as_monochrome=False,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='IllumSyto',
                selector=SourceSelector(
                    components=(),
                    metadata=(),
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumSyto',
                            any_group=None
                        ),
                    ),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
                explicit_source=None,
                load_as_monochrome=False,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='IllumER',
                selector=SourceSelector(
                    components=(),
                    metadata=(),
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumER',
                            any_group=None
                        ),
                    ),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
                explicit_source=None,
                load_as_monochrome=False,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            ),
            NamedSourceBinding(
                alias='IllumHoechst',
                selector=SourceSelector(
                    components=(),
                    metadata=(),
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='IllumHoechst',
                            any_group=None
                        ),
                    ),
                    inherit_current_scope=True
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(),
                artifact_kind=ImageArtifactType,
                required=True,
                source_set_role=SourceSetRole.MATCHED,
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
                explicit_source=None,
                load_as_monochrome=False,
                load_as_mask=False,
                source_channel_axis=None,
                source_channel_counts=None
            )
        ),
        image_plane_sources=(),
        imported_metadata_tables=(
            ImportedMetadataTable(
                location='20585_AE.csv',
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
            )
        )
    ),
    step_source_bindings_config=LazyStepSourceBindingsConfig(
        enabled=None,
        metadata_rules=None,
        match_plan=None,
        metadata_fields=None,
        source_filters=None,
        bindings=None,
        image_plane_sources=None,
        imported_metadata_tables=None,
        source_stack_components=None,
        grouping_metadata_fields=None,
        source_voxel_spacing=None
    ),
    sequential_processing_config=LazySequentialProcessingConfig(
        sequential_components=None
    ),
    analysis_consolidation_config=LazyAnalysisConsolidationConfig(
        enabled=None,
        metaxpress_style=None,
        file_extensions=None,
        exclude_patterns=None,
        output_filename=None,
        global_summary_filename=None
    ),
    plate_metadata_config=LazyPlateMetadataConfig(
        barcode=None,
        plate_name=None,
        plate_id=None,
        description=None,
        acquisition_user=None,
        z_step=None
    ),
    path_planning_config=LazyPathPlanningConfig(
        well_filter=None,
        well_filter_mode=None,
        output_dir_suffix=None,
        global_output_folder=None,
        sub_dir=None
    ),
    step_well_filter_config=LazyStepWellFilterConfig(
        well_filter=None,
        well_filter_mode=None
    ),
    step_materialization_config=LazyStepMaterializationConfig(
        well_filter=None,
        well_filter_mode=None,
        output_dir_suffix=None,
        global_output_folder=None,
        sub_dir=None,
        enabled=None
    ),
    streaming_defaults=LazyStreamingDefaults(
        well_filter=None,
        well_filter_mode=None,
        enabled=None,
        persistent=None,
        host=None,
        transport_mode=None,
        scope_accent_color=None
    ),
    napari_streaming_config=LazyNapariStreamingConfig(
        well_filter=None,
        well_filter_mode=None,
        colormap=None,
        variable_size_handling=None,
        site_mode=None,
        channel_mode=None,
        z_index_mode=None,
        timepoint_mode=None,
        well_mode=None,
        enabled=None,
        persistent=None,
        host=None,
        transport_mode=None,
        scope_accent_color=None,
        port=None
    ),
    fiji_streaming_config=LazyFijiStreamingConfig(
        well_filter=None,
        well_filter_mode=None,
        lut=None,
        auto_contrast=None,
        site_mode=None,
        channel_mode=None,
        z_index_mode=None,
        timepoint_mode=None,
        well_mode=None,
        enabled=None,
        persistent=None,
        host=None,
        transport_mode=None,
        scope_accent_color=None,
        port=None
    ),
    compilation_debug_config=LazyCompilationDebugConfig(
        enabled=None,
        compiled_execution_bundle_path=None
    )
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
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=InputSource.PIPELINE_START
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
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
        name='IdentifyPrimaryObjects',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        name='IdentifySecondaryObjects',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
    ),
    FunctionStep(
        func=(identify_tertiary_objects, {
                'shrink_primary': False,
                'select_the_larger_identified_objects': 'Cells',
                'select_the_smaller_identified_objects': 'Nuclei',
                'name_the_tertiary_objects_to_be_identified': 'Cytoplasm'
            }),
        name='IdentifyTertiaryObjects',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
    ),
    FunctionStep(
        func=(enhance_or_suppress_features, {
                'radius': 5.0,
                'neurite_method': NeuriteMethod.TUBENESS,
                'select_the_input_image': 'Syto',
                'name_the_output_image': 'FilteredRNA'
            }),
        name='EnhanceOrSuppressFeatures',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
    ),
    FunctionStep(
        func=(mask_image, {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'FilteredRNA',
                'select_object_for_mask': 'Nuclei',
                'name_the_output_image': 'SytoNuclei'
            }),
        name='MaskImage',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        name='IdentifyPrimaryObjects',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
    ),
    FunctionStep(
        func=(mask_image, {
                'mask_source': MaskSource.OBJECTS,
                'select_the_input_image': 'Mito',
                'select_object_for_mask': 'Cytoplasm',
                'name_the_output_image': 'MaskedMito'
            }),
        name='MaskImage',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        name='IdentifyPrimaryObjects',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
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
        name='MeasureObjectIntensity',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=InputSource.PIPELINE_START
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
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
        name='MeasureObjectSizeShape',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        name='MeasureObjectNeighbors',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        name='RelateObjects',
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=None,
            group_by=None,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=None,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
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
        description=None,
        enabled=True,
        debug_pause=False,
        dtype_config=LazyDtypeConfig(
            default_dtype_conversion=None
        ),
        processing_config=LazyProcessingConfig(
            variable_components=[],
            group_by=GroupBy.NONE,
            input_source=None
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            metadata_rules=None,
            match_plan=None,
            metadata_fields=None,
            source_filters=None,
            bindings=None,
            image_plane_sources=None,
            imported_metadata_tables=None,
            source_stack_components=None,
            grouping_metadata_fields=None,
            source_voxel_spacing=None
        ),
        step_well_filter_config=LazyStepWellFilterConfig(
            well_filter=None,
            well_filter_mode=None
        ),
        step_materialization_config=LazyStepMaterializationConfig(
            well_filter=None,
            well_filter_mode=None,
            output_dir_suffix=None,
            global_output_folder=None,
            sub_dir=None,
            enabled=None
        ),
        streaming_defaults=LazyStreamingDefaults(
            well_filter=None,
            well_filter_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            colormap=None,
            variable_size_handling=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        ),
        fiji_streaming_config=LazyFijiStreamingConfig(
            well_filter=None,
            well_filter_mode=None,
            lut=None,
            auto_contrast=None,
            site_mode=None,
            channel_mode=None,
            z_index_mode=None,
            timepoint_mode=None,
            well_mode=None,
            enabled=None,
            persistent=None,
            host=None,
            transport_mode=None,
            scope_accent_color=None,
            port=None
        )
    )
]