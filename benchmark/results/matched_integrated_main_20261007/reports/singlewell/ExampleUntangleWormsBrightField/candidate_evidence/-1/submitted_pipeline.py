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
from openhcs.processing.backends.cellprofiler.color import ColorToGrayMode
from openhcs.processing.backends.cellprofiler.crop import CropModule
from openhcs.processing.backends.cellprofiler.illumination import (
    RescaleOption,
    SmoothingMethod,
)
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.outlines import OutlineSourceKind
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetFileSelection
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
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
                alias='RawData',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='.png'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/final-integrated-main-official30-v1/capture/cases/ExampleUntangleWormsBrightField/candidate/-1')
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
                'name_the_output_image': 'CombinedGray'
            }),
        name='ColorToGray',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_calculate'), {
                'rescale_option': RescaleOption.NO,
                'smoothing_method': SmoothingMethod.CONVEX_HULL,
                'name_the_output_image': 'BackgroundIllumination'
            }),
        name='CorrectIlluminationCalculate'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_correct_illumination_apply'), {
                'select_the_input_image': 'CombinedGray',
                'select_the_illumination_function': 'BackgroundIllumination',
                'name_the_output_image': 'BgCorrectedWorms'
            }),
        name='CorrectIlluminationApply'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.INVERT,
                'name_the_output_image': 'WormsImage'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_threshold'), {
                'select_the_input_image': 'BackgroundIllumination',
                'name_the_output_image': 'WellContent'
            }),
        name='Threshold'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_erode_image'), {
                'size': 5,
                'name_the_output_image': 'WellContentEroded'
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
                'select_the_input_image': 'WormsImage',
                'select_the_masking_image': 'WellContentEroded',
                'name_the_output_image': 'CropedWormsImage'
            }),
        name='Crop'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 15,
                'max_diameter': 40000,
                'exclude_border_objects': False,
                'unclump_method': UnclumpMethod.NONE,
                'fill_holes': FillHolesOption.NEVER,
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
                'min_worm_area': 601.2,
                'max_worm_area': 1168.0,
                'cost_threshold': 65.0,
                'min_path_length': 84.9572726577,
                'max_path_length': 166.222920888,
                'median_worm_area': 999.0,
                'max_radius': 5.0,
                'max_skel_length': 150.0,
                'mean_angles': (
                    -0.00420057320254,
                    0.00212014377384,
                    -0.0124186742598,
                    -0.0120451940653,
                    -0.00132933404947,
                    -0.0156834917499,
                    -0.000869740925192,
                    0.000354612306615,
                    -0.009181525002,
                    -0.00301255934843,
                    0.0026090575701,
                    -0.00506183230217,
                    0.00330399516609,
                    -0.00821837539609,
                    -0.00908138974122,
                    0.00283069268893,
                    -0.00623037415962,
                    0.0196962027515,
                    0.0351548767452,
                    128.22461197
                ),
                'inv_angles_covariance_matrix': (
                    (
                        16.7385928419,
                        -5.55113553384,
                        -5.33750451118,
                        0.10165939526,
                        2.67971956545,
                        -0.876229774697,
                        0.306618891993,
                        0.771182555506,
                        -2.68813680821,
                        -2.85265101526,
                        -1.62396264386,
                        3.94467723463,
                        0.0888395984124,
                        0.866812066836,
                        -0.41262097432,
                        -0.710524263621,
                        -1.32437348725,
                        -0.915704586347,
                        0.835030936942,
                        -0.00434566982029
                    ),
                    (
                        -5.55113553384,
                        27.6230400115,
                        -3.4329199571,
                        -12.2474220746,
                        -1.40434736481,
                        1.43260264291,
                        1.73511793249,
                        1.59951576636,
                        4.23242951472,
                        1.30169535647,
                        -1.88058955025,
                        -1.49462555017,
                        -1.2049940461,
                        0.571343716269,
                        -2.04537321351,
                        -0.126876940999,
                        -2.51193316923,
                        3.14334175969,
                        0.27206316919,
                        0.0269287702148
                    ),
                    (
                        -5.33750451118,
                        -3.4329199571,
                        39.3953589921,
                        -0.922156860392,
                        -16.772027551,
                        -0.173956442432,
                        3.95151412541,
                        -1.0380945242,
                        4.32001107502,
                        2.71237492792,
                        2.40587626818,
                        -0.870956218544,
                        -5.01038662107,
                        -4.7050557121,
                        2.43406132096,
                        4.96173885359,
                        2.00753611947,
                        -2.80980890364,
                        -1.22731361848,
                        0.0545170911642
                    ),
                    (
                        0.10165939526,
                        -12.2474220746,
                        -0.922156860392,
                        40.5480693211,
                        -5.76973169135,
                        -17.9270183691,
                        -5.11427834774,
                        4.11466303101,
                        3.06846038926,
                        3.23208430992,
                        2.89762859923,
                        1.27955819359,
                        -6.9320512721,
                        2.38405911663,
                        3.54885823085,
                        0.357630431246,
                        -1.86563065206,
                        -1.54529776922,
                        0.511973919842,
                        -0.0364275122817
                    ),
                    (
                        2.67971956545,
                        -1.40434736481,
                        -16.772027551,
                        -5.76973169135,
                        56.7390451345,
                        0.357060597132,
                        -17.8781514956,
                        -10.5842793887,
                        -3.47925165408,
                        4.53055532791,
                        1.54542442298,
                        0.646320869986,
                        2.92715973656,
                        -3.38015581994,
                        -2.15753367406,
                        3.72903715615,
                        1.94108749558,
                        -0.797061530361,
                        -1.78346134088,
                        -0.0695451729323
                    ),
                    (
                        -0.876229774697,
                        1.43260264291,
                        -0.173956442432,
                        -17.9270183691,
                        0.357060597132,
                        58.9813743704,
                        0.190491099408,
                        -26.5999028898,
                        -16.3018890662,
                        -1.72178420091,
                        5.79295683847,
                        5.75532342148,
                        2.19343668985,
                        -7.0439182375,
                        -5.48894320347,
                        2.47875189135,
                        1.26922782757,
                        -0.587035438644,
                        -0.0832951344492,
                        -0.0466479455928
                    ),
                    (
                        0.306618891993,
                        1.73511793249,
                        3.95151412541,
                        -5.11427834774,
                        -17.8781514956,
                        0.190491099408,
                        51.1995162662,
                        2.70922671318,
                        -15.636812129,
                        -13.941997137,
                        -0.948142714743,
                        3.41822096822,
                        1.10440854191,
                        -2.007851742,
                        1.24633894992,
                        -4.16032508718,
                        3.77309985789,
                        -0.742279733415,
                        0.156760160772,
                        0.0801020175114
                    ),
                    (
                        0.771182555506,
                        1.59951576636,
                        -1.0380945242,
                        4.11466303101,
                        -10.5842793887,
                        -26.5999028898,
                        2.70922671318,
                        64.0083602539,
                        13.2228749805,
                        -21.097512585,
                        -15.9235578515,
                        -6.2858845463,
                        -0.166166102908,
                        5.37254897405,
                        3.71499404665,
                        0.698215787586,
                        -1.84974627425,
                        -0.359895186287,
                        1.79499668054,
                        0.0254948710993
                    ),
                    (
                        -2.68813680821,
                        4.23242951472,
                        4.32001107502,
                        3.06846038926,
                        -3.47925165408,
                        -16.3018890662,
                        -15.636812129,
                        13.2228749805,
                        58.9598553994,
                        2.91014246743,
                        -18.6423518525,
                        -12.2871842189,
                        -6.66069213965,
                        0.438316070401,
                        9.2277917484,
                        1.12413059229,
                        0.477071807344,
                        0.988541370616,
                        -0.1863334956,
                        0.00200575734376
                    ),
                    (
                        -2.85265101526,
                        1.30169535647,
                        2.71237492792,
                        3.23208430992,
                        4.53055532791,
                        -1.72178420091,
                        -13.941997137,
                        -21.097512585,
                        2.91014246743,
                        65.0691316053,
                        4.74424340295,
                        -23.1346142244,
                        -12.9180471368,
                        0.799859585587,
                        4.69627145941,
                        7.06613332016,
                        -0.655277687052,
                        -0.753312210472,
                        -1.00109255758,
                        -0.0169611969349
                    ),
                    (
                        -1.62396264386,
                        -1.88058955025,
                        2.40587626818,
                        2.89762859923,
                        1.54542442298,
                        5.79295683847,
                        -0.948142714743,
                        -15.9235578515,
                        -18.6423518525,
                        4.74424340295,
                        56.4363423462,
                        4.75783201526,
                        -13.8242887756,
                        -11.5465063857,
                        -3.19480102258,
                        5.84317113511,
                        3.17776999158,
                        -1.35095777862,
                        0.463372450389,
                        -0.00946310232883
                    ),
                    (
                        3.94467723463,
                        -1.49462555017,
                        -0.870956218544,
                        1.27955819359,
                        0.646320869986,
                        5.75532342148,
                        3.41822096822,
                        -6.2858845463,
                        -12.2871842189,
                        -23.1346142244,
                        4.75783201526,
                        58.5779174371,
                        -3.45846939443,
                        -15.4509068438,
                        -7.27250304504,
                        -3.61407333399,
                        -1.86623520719,
                        1.32901477085,
                        0.153170299923,
                        0.00186701884044
                    ),
                    (
                        0.0888395984124,
                        -1.2049940461,
                        -5.01038662107,
                        -6.9320512721,
                        2.92715973656,
                        2.19343668985,
                        1.10440854191,
                        -0.166166102908,
                        -6.66069213965,
                        -12.9180471368,
                        -13.8242887756,
                        -3.45846939443,
                        51.2147107864,
                        5.10462974407,
                        -16.0446162626,
                        -8.07458025659,
                        3.66306232985,
                        0.187182701826,
                        -0.397037541491,
                        -0.0392459261301
                    ),
                    (
                        0.866812066836,
                        0.571343716269,
                        -4.7050557121,
                        2.38405911663,
                        -3.38015581994,
                        -7.0439182375,
                        -2.007851742,
                        5.37254897405,
                        0.438316070401,
                        0.799859585587,
                        -11.5465063857,
                        -15.4509068438,
                        5.10462974407,
                        54.4476195328,
                        -3.11042834386,
                        -17.9166286947,
                        -7.60661363903,
                        5.88473691066,
                        4.62943064019,
                        0.00956681130485
                    ),
                    (
                        -0.41262097432,
                        -2.04537321351,
                        2.43406132096,
                        3.54885823085,
                        -2.15753367406,
                        -5.48894320347,
                        1.24633894992,
                        3.71499404665,
                        9.2277917484,
                        4.69627145941,
                        -3.19480102258,
                        -7.27250304504,
                        -16.0446162626,
                        -3.11042834386,
                        45.8170062916,
                        -3.03695765438,
                        -12.9304675699,
                        0.996622865847,
                        4.9710585373,
                        0.000951698699348
                    ),
                    (
                        -0.710524263621,
                        -0.126876940999,
                        4.96173885359,
                        0.357630431246,
                        3.72903715615,
                        2.47875189135,
                        -4.16032508718,
                        0.698215787586,
                        1.12413059229,
                        7.06613332016,
                        5.84317113511,
                        -3.61407333399,
                        -8.07458025659,
                        -17.9166286947,
                        -3.03695765438,
                        46.6792378438,
                        -0.123384525226,
                        -10.6147926321,
                        -2.51911186507,
                        -0.00916785140705
                    ),
                    (
                        -1.32437348725,
                        -2.51193316923,
                        2.00753611947,
                        -1.86563065206,
                        1.94108749558,
                        1.26922782757,
                        3.77309985789,
                        -1.84974627425,
                        0.477071807344,
                        -0.655277687052,
                        3.17776999158,
                        -1.86623520719,
                        3.66306232985,
                        -7.60661363903,
                        -12.9304675699,
                        -0.123384525226,
                        40.2803687236,
                        -13.2787111593,
                        -5.39975180253,
                        -0.00256608254872
                    ),
                    (
                        -0.915704586347,
                        3.14334175969,
                        -2.80980890364,
                        -1.54529776922,
                        -0.797061530361,
                        -0.587035438644,
                        -0.742279733415,
                        -0.359895186287,
                        0.988541370616,
                        -0.753312210472,
                        -1.35095777862,
                        1.32901477085,
                        0.187182701826,
                        5.88473691066,
                        0.996622865847,
                        -10.6147926321,
                        -13.2787111593,
                        28.6063135962,
                        -5.25089665416,
                        0.0248300709765
                    ),
                    (
                        0.835030936942,
                        0.27206316919,
                        -1.22731361848,
                        0.511973919842,
                        -1.78346134088,
                        -0.0832951344492,
                        0.156760160772,
                        1.79499668054,
                        -0.1863334956,
                        -1.00109255758,
                        0.463372450389,
                        0.153170299923,
                        -0.397037541491,
                        4.62943064019,
                        4.9710585373,
                        -2.51911186507,
                        -5.39975180253,
                        -5.25089665416,
                        15.84574249,
                        -0.0276920119395
                    ),
                    (
                        -0.00434566982029,
                        0.0269287702148,
                        0.0545170911642,
                        -0.0364275122817,
                        -0.0695451729323,
                        -0.0466479455928,
                        0.0801020175113,
                        0.0254948710993,
                        0.00200575734376,
                        -0.0169611969349,
                        -0.00946310232883,
                        0.00186701884044,
                        -0.0392459261301,
                        0.00956681130485,
                        0.000951698699348,
                        -0.00916785140705,
                        -0.00256608254872,
                        0.0248300709765,
                        -0.0276920119395,
                        0.00632706887286
                    )
                ),
                'radii_from_training': (
                    1.37085542206,
                    2.75701010143,
                    3.53874150126,
                    3.99158577486,
                    4.30881930038,
                    4.4725286588,
                    4.60528322529,
                    4.63565636812,
                    4.71130595748,
                    4.71023600922,
                    4.72549456593,
                    4.73091563899,
                    4.69538765625,
                    4.66212778564,
                    4.61298813656,
                    4.52294976076,
                    4.34824837819,
                    4.0890436258,
                    3.65460455812,
                    2.84863280892,
                    1.40073141458
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
        func=(get_function('openhcs:cellprofiler_color_to_gray'), {
                'channel_indices': (
                    2,
                ),
                'contributions': (
                    1.0,
                ),
                'name_the_output_image': 'OrigBlue'
            }),
        name='ColorToGray',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.INVERT,
                'name_the_output_image': 'InvBlue'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_crop'), {
                'crop_shape': CropModule.Shape.OBJECTS,
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
                'select_the_input_image': 'InvBlue',
                'select_the_objects': 'NonOverlappingWorms',
                'name_the_output_image': 'CropBlue'
            }),
        name='Crop'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
                'min_diameter': 2,
                'max_diameter': 40000,
                'exclude_border_objects': False,
                'unclump_method': UnclumpMethod.NONE,
                'threshold_method': CellProfilerThresholdMethod.MANUAL,
                'adaptive_window_size': 50,
                'manual_threshold': 0.6,
                'name_the_primary_objects_to_be_identified': 'FatRegions'
            }),
        name='IdentifyPrimaryObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
                'calculate_advanced': False,
                'calculate_zernikes': False,
                'select_object_sets_to_measure': 'FatRegions'
            }),
        name='MeasureObjectSizeShape'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_relate_objects'), {
                'calculate_distances': RelateObjectsDistanceMethod.NONE,
                'calculate_per_parent_means': True,
                'save_children_with_parents': False,
                'select_the_parent_objects': 'NonOverlappingWorms',
                'select_the_child_objects': 'FatRegions'
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_overlay_outlines'), {
                'outline_source_kinds': (
                    OutlineSourceKind.OBJECTS,
                    OutlineSourceKind.OBJECTS
                ),
                'outline_colors': (
                    '#26FF2B',
                    '#0800F7'
                ),
                'select_image_on_which_to_display_outlines': 'RawData',
                'select_objects_to_display': (
                    'OverlappingWorms',
                    'FatRegions'
                ),
                'name_the_output_image': 'OrigOverlay'
            }),
        name='OverlayOutlines',
        processing_config=LazyProcessingConfig(
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'export_all_measurement_types': False,
                'file_selections': (
                    SpreadsheetFileSelection(
                        subjects=(
                            'NonOverlappingWorms',
                        ),
                        file_name='NonOverlappingWorms.csv'
                    ),
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