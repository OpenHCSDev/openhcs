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
from openhcs.processing.backends.cellprofiler.crop import CropModule
from openhcs.processing.backends.cellprofiler.illumination import (
    RescaleOption,
    SmoothingMethod,
)
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod
from openhcs.processing.backends.cellprofiler.save_images import (
    SaveImagesBitDepth,
    SaveImagesFileFormat,
)
from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
    SpreadsheetColumnSelection,
    SpreadsheetFileSelection,
)
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerOtsuMethod,
    CellProfilerThresholdAssignment,
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
                value='[\\/]\\.'
            )
        ),
        bindings=(
            NamedSourceBinding(
                alias='BrightFieldImage',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS_REGEX,
                            value='_C[0-2][0-9]_w2'
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
                alias='Sytox',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS_REGEX,
                            value='_C[0-2][0-9]_w1'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleUntangleWorms/candidate/-1')
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
            '1': (get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                    'rescale_option': RescaleOption.NO,
                    'smoothing_method': SmoothingMethod.CONVEX_HULL,
                    'name_the_output_image': 'Background'
                })
        },
        name='CorrectIlluminationCalculate',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                    'name_the_output_image': 'IlluminationCorrectedBF'
                })
        },
        name='CorrectIlluminationApply',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.INVERT,
                'name_the_output_image': 'Worms'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_threshold'), {
                'select_the_input_image': 'Background',
                'name_the_output_image': 'WellEdge'
            }),
        name='Threshold'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_erode_image'), {
                'size': 5,
                'name_the_output_image': 'ErodedWellEdge'
            }),
        name='ErodeImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_crop'), {
                'crop_shape': CropModule.Shape.IMAGE,
                'left_right_rectangle_positions': [
                    '0',
                    'end'
                ],
                'top_bottom_rectangle_positions': [
                    '0',
                    'end'
                ],
                'ellipse_center': (
                    500,
                    500
                ),
                'ellipse_x_radius': 400.0,
                'ellipse_y_radius': 200.0,
                'select_the_input_image': 'Worms',
                'select_the_masking_image': 'ErodedWellEdge',
                'name_the_output_image': 'WormsCropped'
            }),
        name='Crop'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 15,
                'max_diameter': 60000,
                'exclude_border_objects': False,
                'unclump_method': UnclumpMethod.NONE,
                'otsu_class_count': CellProfilerOtsuMethod.THREE_CLASS,
                'assign_middle_to_foreground': CellProfilerThresholdAssignment.BACKGROUND,
                'adaptive_window_size': 50,
                'name_the_primary_objects_to_be_identified': 'WormObjects'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
                'image_mode': ImageMode.BINARY,
                'colormap_value': 'Default',
                'name_the_output_image': 'WormObjectsBinary'
            }),
        name='ConvertObjectsToImage'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_untangle_worms_both'), {
                'min_worm_area': 656.2,
                'max_worm_area': 1325.0,
                'cost_threshold': 69.5642080648,
                'min_path_length': 82.7844804516,
                'max_path_length': 170.406784691,
                'median_worm_area': 1098.5,
                'max_radius': 5.78287310277,
                'max_skel_length': 154.91525881,
                'mean_angles': (
                    -5.72667749901e-18,
                    -8.36011313724e-20,
                    9.19612445096e-19,
                    1.58842149608e-18,
                    1.37105855451e-17,
                    -2.29903111274e-18,
                    4.34725883136e-18,
                    -1.42121923333e-18,
                    1.00321357647e-18,
                    -1.67202262745e-19,
                    7.52410182351e-19,
                    -8.36011313724e-19,
                    3.00964072941e-18,
                    7.94210748038e-19,
                    1.21639646147e-17,
                    1.58842149608e-18,
                    1.25401697059e-18,
                    -1.46301979902e-19,
                    -4.93246675097e-18,
                    129.225196479
                ),
                'inv_angles_covariance_matrix': (
                    (
                        16.6850829005,
                        -4.24041217459,
                        -5.84904257737,
                        -0.196478643493,
                        0.390835803917,
                        0.939434600033,
                        1.03292552508,
                        -0.916221863492,
                        1.83623258478,
                        0.351188883283,
                        0.637887596385,
                        2.31312477801,
                        0.652580290851,
                        0.921012787291,
                        -0.628617122415,
                        0.830217111735,
                        0.928192145563,
                        -0.593567740709,
                        1.62810504672,
                        -1.76453752852e-17
                    ),
                    (
                        -4.24041217459,
                        17.7124756716,
                        -9.18829048813,
                        -4.2470008616,
                        -1.19240418025,
                        2.55310033398,
                        3.15109226183,
                        0.169766814433,
                        0.159059914054,
                        0.376689483882,
                        -0.257556687377,
                        0.181441287713,
                        -1.39940235758,
                        -0.885814636753,
                        2.30130481485,
                        -2.00821615855,
                        0.166131604441,
                        -0.0102676805663,
                        -0.593567740709,
                        1.33967048978e-18
                    ),
                    (
                        -5.84904257737,
                        -9.18829048813,
                        36.4595091155,
                        -2.32504623222,
                        -7.78489516875,
                        -3.41091766246,
                        -0.916863729006,
                        6.36417300872,
                        0.726175084396,
                        -1.89568797409,
                        -2.25526187716,
                        1.00052063314,
                        4.66148469233,
                        -1.41658353352,
                        -1.7404013133,
                        5.20452759939,
                        -5.85515258074,
                        0.166131604441,
                        0.928192145563,
                        -6.01803503782e-20
                    ),
                    (
                        -0.196478643493,
                        -4.2470008616,
                        -2.32504623222,
                        25.2306273439,
                        -1.33012594469,
                        -5.62447408259,
                        -0.86424975619,
                        -3.38614344643,
                        -4.20347806851,
                        1.56541877979,
                        3.13464026519,
                        2.05257926711,
                        -1.9073988573,
                        -2.04890956997,
                        -0.0987430716523,
                        -2.51750828297,
                        5.20452759939,
                        -2.00821615855,
                        0.830217111735,
                        3.25975103569e-18
                    ),
                    (
                        0.390835803917,
                        -1.19240418025,
                        -7.78489516875,
                        -1.33012594469,
                        37.9459926172,
                        -6.17735792802,
                        -15.4812875672,
                        -11.8729032413,
                        0.334176124783,
                        6.5765502471,
                        -0.78163004061,
                        -0.34565217659,
                        -0.699826393385,
                        -1.90798639799,
                        -3.56927224969,
                        -0.0987430716523,
                        -1.7404013133,
                        2.30130481485,
                        -0.628617122415,
                        1.76505801017e-17
                    ),
                    (
                        0.939434600033,
                        2.55310033398,
                        -3.41091766246,
                        -5.62447408259,
                        -6.17735792802,
                        31.5101095856,
                        -5.98240078005,
                        -3.31886336806,
                        0.371053692073,
                        -0.602942042676,
                        3.88113131562,
                        0.625846908046,
                        -2.96699303916,
                        3.95532516421,
                        -1.90798639799,
                        -2.04890956997,
                        -1.41658353352,
                        -0.885814636753,
                        0.921012787291,
                        -3.21638268065e-18
                    ),
                    (
                        1.03292552508,
                        3.15109226183,
                        -0.916863729006,
                        -0.86424975619,
                        -15.4812875672,
                        -5.98240078005,
                        47.0550602212,
                        11.5364591321,
                        -12.6769125571,
                        -15.4477644261,
                        2.29987376434,
                        6.87943814721,
                        8.46268328412,
                        -2.96699303916,
                        -0.699826393385,
                        -1.9073988573,
                        4.66148469233,
                        -1.39940235758,
                        0.652580290851,
                        -2.9682421418e-17
                    ),
                    (
                        -0.916221863492,
                        0.169766814433,
                        6.36417300872,
                        -3.38614344643,
                        -11.8729032413,
                        -3.31886336806,
                        11.5364591321,
                        38.556649829,
                        -3.72224377358,
                        -15.4717599582,
                        -4.73745475451,
                        5.33734985131,
                        6.87943814721,
                        0.625846908046,
                        -0.34565217659,
                        2.05257926711,
                        1.00052063314,
                        0.181441287713,
                        2.31312477801,
                        -1.58365713757e-17
                    ),
                    (
                        1.83623258478,
                        0.159059914054,
                        0.726175084396,
                        -4.20347806851,
                        0.334176124783,
                        0.371053692073,
                        -12.6769125571,
                        -3.72224377358,
                        38.8734127595,
                        2.6179202085,
                        -12.1665356178,
                        -4.73745475451,
                        2.29987376434,
                        3.88113131562,
                        -0.78163004061,
                        3.13464026519,
                        -2.25526187716,
                        -0.257556687377,
                        0.637887596385,
                        1.15148988182e-17
                    ),
                    (
                        0.351188883283,
                        0.376689483882,
                        -1.89568797409,
                        1.56541877979,
                        6.5765502471,
                        -0.602942042676,
                        -15.4477644261,
                        -15.4717599582,
                        2.6179202085,
                        48.9077498045,
                        2.6179202085,
                        -15.4717599582,
                        -15.4477644261,
                        -0.602942042676,
                        6.5765502471,
                        1.56541877979,
                        -1.89568797409,
                        0.376689483882,
                        0.351188883283,
                        1.72855907818e-17
                    ),
                    (
                        0.637887596385,
                        -0.257556687377,
                        -2.25526187716,
                        3.13464026519,
                        -0.78163004061,
                        3.88113131562,
                        2.29987376434,
                        -4.73745475451,
                        -12.1665356178,
                        2.6179202085,
                        38.8734127595,
                        -3.72224377358,
                        -12.6769125571,
                        0.371053692073,
                        0.334176124783,
                        -4.20347806851,
                        0.726175084396,
                        0.159059914054,
                        1.83623258478,
                        2.95072325051e-18
                    ),
                    (
                        2.31312477801,
                        0.181441287713,
                        1.00052063314,
                        2.05257926711,
                        -0.34565217659,
                        0.625846908046,
                        6.87943814721,
                        5.33734985131,
                        -4.73745475451,
                        -15.4717599582,
                        -3.72224377358,
                        38.556649829,
                        11.5364591321,
                        -3.31886336806,
                        -11.8729032413,
                        -3.38614344643,
                        6.36417300872,
                        0.169766814433,
                        -0.916221863492,
                        -1.82557518541e-17
                    ),
                    (
                        0.652580290851,
                        -1.39940235758,
                        4.66148469233,
                        -1.9073988573,
                        -0.699826393385,
                        -2.96699303916,
                        8.46268328412,
                        6.87943814721,
                        2.29987376434,
                        -15.4477644261,
                        -12.6769125571,
                        11.5364591321,
                        47.0550602212,
                        -5.98240078005,
                        -15.4812875672,
                        -0.86424975619,
                        -0.916863729006,
                        3.15109226183,
                        1.03292552508,
                        -2.64105333483e-17
                    ),
                    (
                        0.921012787291,
                        -0.885814636753,
                        -1.41658353352,
                        -2.04890956997,
                        -1.90798639799,
                        3.95532516421,
                        -2.96699303916,
                        0.625846908046,
                        3.88113131562,
                        -0.602942042676,
                        0.371053692073,
                        -3.31886336806,
                        -5.98240078005,
                        31.5101095856,
                        -6.17735792802,
                        -5.62447408259,
                        -3.41091766246,
                        2.55310033398,
                        0.939434600033,
                        -1.84061067081e-18
                    ),
                    (
                        -0.628617122415,
                        2.30130481485,
                        -1.7404013133,
                        -0.0987430716523,
                        -3.56927224969,
                        -1.90798639799,
                        -0.699826393385,
                        -0.34565217659,
                        -0.78163004061,
                        6.5765502471,
                        0.334176124783,
                        -11.8729032413,
                        -15.4812875672,
                        -6.17735792802,
                        37.9459926172,
                        -1.33012594469,
                        -7.78489516875,
                        -1.19240418025,
                        0.390835803917,
                        1.61436636327e-17
                    ),
                    (
                        0.830217111735,
                        -2.00821615855,
                        5.20452759939,
                        -2.51750828297,
                        -0.0987430716523,
                        -2.04890956997,
                        -1.9073988573,
                        2.05257926711,
                        3.13464026519,
                        1.56541877979,
                        -4.20347806851,
                        -3.38614344643,
                        -0.86424975619,
                        -5.62447408259,
                        -1.33012594469,
                        25.2306273439,
                        -2.32504623222,
                        -4.2470008616,
                        -0.196478643493,
                        4.74779617843e-18
                    ),
                    (
                        0.928192145563,
                        0.166131604441,
                        -5.85515258074,
                        5.20452759939,
                        -1.7404013133,
                        -1.41658353352,
                        4.66148469233,
                        1.00052063314,
                        -2.25526187716,
                        -1.89568797409,
                        0.726175084396,
                        6.36417300872,
                        -0.916863729006,
                        -3.41091766246,
                        -7.78489516875,
                        -2.32504623222,
                        36.4595091155,
                        -9.18829048813,
                        -5.84904257737,
                        -3.28247984389e-18
                    ),
                    (
                        -0.593567740709,
                        -0.0102676805663,
                        0.166131604441,
                        -2.00821615855,
                        2.30130481485,
                        -0.885814636753,
                        -1.39940235758,
                        0.181441287713,
                        -0.257556687377,
                        0.376689483882,
                        0.159059914054,
                        0.169766814433,
                        3.15109226183,
                        2.55310033398,
                        -1.19240418025,
                        -4.2470008616,
                        -9.18829048813,
                        17.7124756716,
                        -4.24041217459,
                        7.3994528575e-19
                    ),
                    (
                        1.62810504672,
                        -0.593567740709,
                        0.928192145563,
                        0.830217111735,
                        -0.628617122415,
                        0.921012787291,
                        0.652580290851,
                        2.31312477801,
                        0.637887596385,
                        0.351188883283,
                        1.83623258478,
                        -0.916221863492,
                        1.03292552508,
                        0.939434600033,
                        0.390835803917,
                        -0.196478643493,
                        -5.84904257737,
                        -4.24041217459,
                        16.6850829005,
                        -1.35898328726e-17
                    ),
                    (
                        -1.76453752852e-17,
                        1.33967048978e-18,
                        -6.01803503782e-20,
                        3.25975103569e-18,
                        1.76505801017e-17,
                        -3.21638268065e-18,
                        -2.9682421418e-17,
                        -1.58365713757e-17,
                        1.15148988182e-17,
                        1.72855907818e-17,
                        2.95072325051e-18,
                        -1.82557518541e-17,
                        -2.64105333483e-17,
                        -1.84061067081e-18,
                        1.61436636327e-17,
                        4.74779617843e-18,
                        -3.28247984389e-18,
                        7.3994528575e-19,
                        -1.35898328726e-17,
                        0.00705097919049
                    )
                ),
                'radii_from_training': (
                    1.32517565783,
                    2.87253785947,
                    3.82479014873,
                    4.38217485855,
                    4.68057107053,
                    4.88003306367,
                    4.97116681135,
                    5.11679877751,
                    5.13249306169,
                    5.15496930009,
                    5.14866531809,
                    5.18507240404,
                    5.13072717753,
                    5.09788617645,
                    5.05983476738,
                    4.94807701187,
                    4.78831589213,
                    4.45278631852,
                    3.87552692779,
                    2.9099323273,
                    1.37226916049
                ),
                'retain_overlapping_outline': True,
                'overlapping_outline_colormap': 'Default',
                'name_the_output_overlapping_worm_objects': 'OverlappingWorms',
                'name_the_output_non_overlapping_worm_objects': 'NonOverlappingWorms',
                'overlapping_outline_name': 'OverlappedWormOutlines'
            }),
        name='UntangleWorms'
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_overlay_outlines'), {
                    'select_image_on_which_to_display_outlines': 'BrightFieldImage',
                    'select_objects_to_display': 'OverlappingWorms',
                    'name_the_output_image': 'OrigOverlay'
                })
        },
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_save_images'), {
                'single_file_name': 'OrigBlue',
                'append_suffix': True,
                'filename_suffix': 'outlines',
                'file_format': SaveImagesFileFormat.PNG,
                'bit_depth': SaveImagesBitDepth.UINT8,
                'overwrite': False,
                'base_image_folder': 'Elsewhere...|',
                'record_file_and_path': False,
                'select_image_name_for_file_prefix': 'BrightFieldImage',
                'select_the_image_to_save': 'OrigOverlay'
            }),
        name='SaveImages',
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='BrightFieldImage',
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS_REGEX,
                                value='_C[0-2][0-9]_w2'
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
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': 'OverlappingWorms'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
                'select_object_sets_to_measure': 'NonOverlappingWorms',
                'select_images_to_measure': 'Sytox'
            }),
        name='MeasureObjectIntensity',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'select_measurements': True,
                'selected_columns': (
                    SpreadsheetColumnSelection(
                        subject='Image',
                        feature='FileName_BrightFieldImage'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='Location_Center_Y'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='Location_Center_X'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='AreaShape_FormFactor'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='AreaShape_Center_Y'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='AreaShape_Center_Z'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='AreaShape_Center_X'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='AreaShape_Area'
                    ),
                    SpreadsheetColumnSelection(
                        subject='OverlappingWorms',
                        feature='AreaShape_MajorAxisLength'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Intensity_StdIntensity_Sytox'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Intensity_MeanIntensity_Sytox'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Intensity_IntegratedIntensity_Sytox'
                    )
                ),
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
                            'OverlappingWorms',
                            'NonOverlappingWorms'
                        ),
                        file_name='OverlappingWorms.csv'
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