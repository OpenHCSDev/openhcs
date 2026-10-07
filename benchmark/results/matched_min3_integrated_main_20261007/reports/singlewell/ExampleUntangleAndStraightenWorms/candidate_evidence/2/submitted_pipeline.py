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
from openhcs.processing.backends.cellprofiler.illumination import (
    RescaleOption,
    SmoothingMethod,
)
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.outlines import OutlineSourceKind
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsDistanceMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
    SpreadsheetColumnSelection,
    SpreadsheetFileSelection,
)
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.worms import FlipMode
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
                alias='Worms',
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
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='1'
                    ),
                ),
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='GFP',
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
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='2'
                    ),
                ),
                load_as_monochrome=True
            ),
            NamedSourceBinding(
                alias='mCherry',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value='w3'
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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/ExampleUntangleAndStraightenWorms/candidate/2')
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
                    'name_the_output_image': 'IllumCorrWorms'
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
                'name_the_output_image': 'WormsInverted'
            }),
        name='ImageMath'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_threshold'), {
                'name_the_output_image': 'WormsBinary'
            }),
        name='Threshold'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_untangle_worms_both'), {
                'min_worm_area': 567.8,
                'max_worm_area': 1178.0,
                'cost_threshold': 68.1,
                'min_path_length': 81.1857300717,
                'max_path_length': 171.0,
                'overlap_weight': 2.0,
                'median_worm_area': 999.5,
                'max_radius': 5.03140476034,
                'max_skel_length': 155.568542495,
                'mean_angles': (
                    -0.00253156263352,
                    -0.0101121440056,
                    -0.0154208546572,
                    -0.015313335893,
                    -0.00978017584943,
                    -0.0129733791494,
                    0.000108303085178,
                    -0.00472628290539,
                    -0.00280840864752,
                    -0.00576181676747,
                    0.00545458835941,
                    -0.0173633663678,
                    0.000260153331636,
                    -0.00362234980502,
                    -0.00236559882065,
                    0.00436712079091,
                    0.00470092574135,
                    0.0005059225683,
                    0.029895052734,
                    127.847541867
                ),
                'inv_angles_covariance_matrix': (
                    (
                        14.546610578,
                        -5.83618928788,
                        -5.18596109594,
                        -1.21202877916,
                        3.00507236427,
                        1.76531609033,
                        -1.23537280306,
                        0.00187083560629,
                        -1.07896903661,
                        -0.867872906332,
                        -0.665101065129,
                        1.83301767505,
                        0.11004653358,
                        -1.1982095224,
                        1.61421681329,
                        0.00403680275858,
                        -0.288569340962,
                        -0.988597027705,
                        0.52554944564,
                        -0.01440163544
                    ),
                    (
                        -5.83618928788,
                        28.6811552159,
                        -3.68973136691,
                        -12.3558500701,
                        -3.32470680527,
                        4.88496074939,
                        3.20087885125,
                        -0.455512295186,
                        0.289141270442,
                        0.878056164578,
                        -0.579318658062,
                        -2.71735607875,
                        1.01088055918,
                        0.326947484665,
                        -2.69140782141,
                        -0.15782270933,
                        -1.410705712,
                        1.49333034848,
                        0.248198159576,
                        0.0277567127433
                    ),
                    (
                        -5.18596109594,
                        -3.68973136691,
                        34.74971468,
                        -4.39722302803,
                        -13.5436096256,
                        -4.03737219064,
                        3.89149362051,
                        1.1165645768,
                        2.54545022388,
                        1.51080585703,
                        2.75515987134,
                        -2.83192483701,
                        -1.49165244842,
                        -0.478651152986,
                        3.02074885527,
                        1.48333907126,
                        0.646421428703,
                        -1.1307267419,
                        -0.888519454183,
                        0.00222902256089
                    ),
                    (
                        -1.21202877916,
                        -12.3558500701,
                        -4.39722302803,
                        39.6070878094,
                        -0.888934579545,
                        -16.9300231342,
                        -5.66410694472,
                        1.2619260111,
                        4.13479789732,
                        2.44749762332,
                        3.28276560143,
                        3.53727174312,
                        -2.88668816305,
                        0.824898177206,
                        2.39255639826,
                        -0.111237230341,
                        0.618690870796,
                        -0.527801705675,
                        0.179017909646,
                        -0.009835969151
                    ),
                    (
                        3.00507236427,
                        -3.32470680527,
                        -13.5436096256,
                        -0.888934579545,
                        52.4368485816,
                        -1.30609390846,
                        -20.0818774571,
                        -9.85161787758,
                        -0.108862618615,
                        3.91203280393,
                        1.60927840028,
                        3.97963542764,
                        -0.64635713952,
                        -3.43633882989,
                        -2.95586882046,
                        2.91172972032,
                        0.597050529045,
                        -0.859865910971,
                        0.0689163052367,
                        -0.0138768295187
                    ),
                    (
                        1.76531609033,
                        4.88496074939,
                        -4.03737219064,
                        -16.9300231342,
                        -1.30609390846,
                        51.7116430158,
                        1.45986489292,
                        -21.8613498557,
                        -11.3428117835,
                        2.03291485736,
                        1.73718513718,
                        0.688134611949,
                        3.14484206733,
                        -1.47450560499,
                        -3.72465591446,
                        -0.270619812081,
                        -0.673610386363,
                        -0.164058947216,
                        -0.478934900726,
                        -0.0266461370586
                    ),
                    (
                        -1.23537280306,
                        3.20087885125,
                        3.89149362051,
                        -5.66410694472,
                        -20.0818774571,
                        1.45986489292,
                        51.1463996428,
                        0.152877969029,
                        -17.531767971,
                        -13.3467169735,
                        1.30677652162,
                        3.89383810883,
                        3.64605741977,
                        -2.71006307151,
                        0.161498323485,
                        -2.0570455412,
                        -1.5117423376,
                        1.44292053182,
                        0.256364547785,
                        0.0265074231688
                    ),
                    (
                        0.0018708356063,
                        -0.455512295186,
                        1.1165645768,
                        1.2619260111,
                        -9.85161787758,
                        -21.8613498557,
                        0.152877969029,
                        59.6975751528,
                        6.47629600585,
                        -23.9149964929,
                        -11.4747124139,
                        -0.00473407143893,
                        1.41736366059,
                        2.24915819853,
                        3.40773187177,
                        -1.22156416425,
                        -1.08532544769,
                        -1.2093929585,
                        1.23294814874,
                        0.0151492181671
                    ),
                    (
                        -1.07896903661,
                        0.289141270442,
                        2.54545022388,
                        4.13479789732,
                        -0.108862618615,
                        -11.3428117835,
                        -17.531767971,
                        6.47629600585,
                        54.844704126,
                        3.02038894854,
                        -21.1528410968,
                        -8.98859123105,
                        -1.89699776284,
                        0.714646466086,
                        6.82138890608,
                        -1.55619623317,
                        2.1473411589,
                        -1.21177131704,
                        -1.26721007893,
                        -0.0112961121027
                    ),
                    (
                        -0.867872906332,
                        0.878056164578,
                        1.51080585703,
                        2.44749762332,
                        3.91203280393,
                        2.03291485736,
                        -13.3467169735,
                        -23.9149964929,
                        3.02038894854,
                        61.2924114111,
                        4.14317351533,
                        -21.8216724772,
                        -10.6912175776,
                        2.86937794868,
                        4.63190984645,
                        3.01084410079,
                        -1.1447388502,
                        0.621417155408,
                        -0.0962560332384,
                        -0.0240317745733
                    ),
                    (
                        -0.665101065129,
                        -0.579318658062,
                        2.75515987134,
                        3.28276560143,
                        1.60927840028,
                        1.73718513718,
                        1.30677652162,
                        -11.4747124139,
                        -21.1528410968,
                        4.14317351533,
                        54.7321443522,
                        4.73744449713,
                        -16.7616370292,
                        -9.46889538574,
                        -1.94411457688,
                        4.78177320374,
                        2.51415202699,
                        0.402234157447,
                        0.962525581608,
                        0.000595213688426
                    ),
                    (
                        1.83301767505,
                        -2.71735607875,
                        -2.83192483701,
                        3.53727174312,
                        3.97963542764,
                        0.688134611949,
                        3.89383810883,
                        -0.00473407143893,
                        -8.98859123105,
                        -21.8216724772,
                        4.73744449713,
                        56.6026329558,
                        -3.9510609002,
                        -18.5666568573,
                        -8.42547296728,
                        0.576046708517,
                        0.692157717171,
                        1.25177671119,
                        0.190898303118,
                        0.0298654862435
                    ),
                    (
                        0.11004653358,
                        1.01088055918,
                        -1.49165244842,
                        -2.88668816305,
                        -0.64635713952,
                        3.14484206733,
                        3.64605741977,
                        1.41736366059,
                        -1.89699776284,
                        -10.6912175776,
                        -16.7616370292,
                        -3.9510609002,
                        51.4803562191,
                        5.57416916983,
                        -18.1952724876,
                        -6.66665980757,
                        2.82398019397,
                        1.45599151669,
                        -1.23855304394,
                        -0.00368362225774
                    ),
                    (
                        -1.1982095224,
                        0.326947484665,
                        -0.478651152986,
                        0.824898177206,
                        -3.43633882989,
                        -1.47450560499,
                        -2.71006307151,
                        2.24915819853,
                        0.714646466086,
                        2.86937794868,
                        -9.46889538574,
                        -18.5666568573,
                        5.57416916983,
                        49.917909902,
                        -5.37616311985,
                        -16.0300860816,
                        -4.10111805283,
                        2.86969935162,
                        3.4601117817,
                        -0.0104753707823
                    ),
                    (
                        1.61421681329,
                        -2.69140782141,
                        3.02074885527,
                        2.39255639826,
                        -2.95586882046,
                        -3.72465591446,
                        0.161498323485,
                        3.40773187177,
                        6.82138890608,
                        4.63190984645,
                        -1.94411457688,
                        -8.42547296728,
                        -18.1952724876,
                        -5.37616311985,
                        47.5001873677,
                        -2.76149456643,
                        -13.0419140312,
                        -1.7925384217,
                        4.87652948993,
                        -0.0116388255383
                    ),
                    (
                        0.00403680275858,
                        -0.15782270933,
                        1.48333907126,
                        -0.111237230341,
                        2.91172972032,
                        -0.270619812081,
                        -2.0570455412,
                        -1.22156416425,
                        -1.55619623317,
                        3.01084410079,
                        4.78177320374,
                        0.576046708517,
                        -6.66665980757,
                        -16.0300860816,
                        -2.76149456643,
                        41.9699800711,
                        -1.10230358385,
                        -9.0170369209,
                        -2.29284472407,
                        -0.00631354480575
                    ),
                    (
                        -0.288569340962,
                        -1.410705712,
                        0.646421428703,
                        0.618690870796,
                        0.597050529045,
                        -0.673610386363,
                        -1.5117423376,
                        -1.08532544769,
                        2.1473411589,
                        -1.1447388502,
                        2.51415202699,
                        0.692157717171,
                        2.82398019397,
                        -4.10111805283,
                        -13.0419140312,
                        -1.10230358385,
                        31.4955862025,
                        -1.17211538943,
                        -9.31215003794,
                        -0.0114357498771
                    ),
                    (
                        -0.988597027705,
                        1.49333034848,
                        -1.1307267419,
                        -0.527801705675,
                        -0.859865910971,
                        -0.164058947216,
                        1.44292053182,
                        -1.2093929585,
                        -1.21177131704,
                        0.621417155408,
                        0.402234157447,
                        1.25177671119,
                        1.45599151669,
                        2.86969935162,
                        -1.7925384217,
                        -9.0170369209,
                        -1.17211538943,
                        14.5444465998,
                        0.607414028166,
                        0.0164152297629
                    ),
                    (
                        0.52554944564,
                        0.248198159576,
                        -0.888519454183,
                        0.179017909646,
                        0.0689163052367,
                        -0.478934900726,
                        0.256364547785,
                        1.23294814874,
                        -1.26721007893,
                        -0.0962560332384,
                        0.962525581608,
                        0.190898303118,
                        -1.23855304394,
                        3.4601117817,
                        4.87652948993,
                        -2.29284472407,
                        -9.31215003794,
                        0.607414028166,
                        12.1473398973,
                        -0.00485464675705
                    ),
                    (
                        -0.01440163544,
                        0.0277567127433,
                        0.00222902256089,
                        -0.009835969151,
                        -0.0138768295187,
                        -0.0266461370586,
                        0.0265074231688,
                        0.0151492181671,
                        -0.0112961121027,
                        -0.0240317745733,
                        0.000595213688426,
                        0.0298654862435,
                        -0.00368362225774,
                        -0.0104753707823,
                        -0.0116388255383,
                        -0.00631354480575,
                        -0.0114357498771,
                        0.0164152297629,
                        -0.00485464675705,
                        0.00518857361841
                    )
                ),
                'radii_from_training': (
                    1.37138813418,
                    2.7909852365,
                    3.56169394929,
                    4.0155644358,
                    4.3207201932,
                    4.48891561838,
                    4.60925073765,
                    4.66977189573,
                    4.71242809051,
                    4.72237056501,
                    4.72322341263,
                    4.71547932525,
                    4.69032899935,
                    4.66121257586,
                    4.60804098909,
                    4.51788577763,
                    4.34750410715,
                    4.08644366514,
                    3.62122413543,
                    2.8460307156,
                    1.40926236481
                ),
                'retain_overlapping_outline': True,
                'retain_nonoverlapping_outline': True,
                'overlapping_outline_colormap': 'gist_rainbow',
                'name_the_output_overlapping_worm_objects': 'OverlappingWorms',
                'name_the_output_non_overlapping_worm_objects': 'NonOverlappingWorms',
                'overlapping_outline_name': 'OverlappedWormOutlines',
                'nonoverlapping_outline_name': 'NonoverlappedWormOutlines'
            }),
        name='UntangleWorms'
    ),
    FunctionStep(
        func={
            '1': (get_function('openhcs:cellprofiler_overlay_outlines'), {
                    'select_image_on_which_to_display_outlines': 'Worms',
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
        func=(get_function('openhcs:cellprofiler_straighten_worms'), {
                'flip_mode': FlipMode.TOP,
                'number_of_segments': 5,
                'number_of_stripes': 1,
                'select_the_input_untangled_worm_objects': 'NonOverlappingWorms',
                'select_an_input_image_to_straighten': (
                    'mCherry',
                    'GFP'
                ),
                'name_the_output_straightened_worm_objects': 'StraightenedWorms',
                'name_the_output_straightened_image': (
                    'Straightened_mCherry',
                    'Straightened_GFP'
                )
            }),
        name='StraightenWorms',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE,
            input_source=InputSource.PIPELINE_START
        )
    ),
    FunctionStep(
        func={
            '3': (get_function('openhcs:cellprofiler_identify_primary_objects'), {
                    'min_diameter': 5,
                    'unclump_method': UnclumpMethod.NONE,
                    'threshold_method': CellProfilerThresholdMethod.MANUAL,
                    'adaptive_window_size': 50,
                    'manual_threshold': 0.0025,
                    'name_the_primary_objects_to_be_identified': 'HeadMarkers'
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
                'save_children_with_parents': False,
                'select_the_parent_objects': 'NonOverlappingWorms',
                'select_the_child_objects': 'HeadMarkers'
            }),
        name='RelateObjects'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_gray_to_color'), {
                'rescale_intensity': False,
                'red_channel': 0,
                'green_channel': 1,
                'select_the_image_to_be_colored_red': 'Straightened_mCherry',
                'select_the_image_to_be_colored_green': 'Straightened_GFP',
                'name_the_output_image': 'StraightenedRG'
            }),
        name='GrayToColor',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.SITE
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_gray_to_color'), {
                'rescale_intensity': False,
                'red_channel': 0,
                'green_channel': 1,
                'select_the_image_to_be_colored_red': 'mCherry',
                'select_the_image_to_be_colored_green': 'GFP',
                'select_the_image_to_be_colored_blue': 'Leave this black',
                'name_the_output_image': 'OrigRG'
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
                'outline_source_kinds': (
                    OutlineSourceKind.OBJECTS,
                    OutlineSourceKind.OBJECTS
                ),
                'outline_colors': (
                    'red',
                    'green'
                ),
                'select_image_on_which_to_display_outlines': 'OrigRG',
                'select_objects_to_display': (
                    'NonOverlappingWorms',
                    'HeadMarkers'
                ),
                'name_the_output_image': 'OrigOverlay'
            }),
        name='OverlayOutlines'
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
                'select_measurements': True,
                'selected_columns': (
                    SpreadsheetColumnSelection(
                        subject='Image',
                        feature='FileName_GFP'
                    ),
                    SpreadsheetColumnSelection(
                        subject='Image',
                        feature='FileName_mCherry'
                    ),
                    SpreadsheetColumnSelection(
                        subject='Image',
                        feature='FileName_Worms'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_GFP_T1of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_GFP_T2of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_GFP_T3of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_GFP_T4of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_GFP_T5of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_mCherry_T1of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_mCherry_T2of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_mCherry_T3of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_mCherry_T4of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_StdIntensity_Straightened_mCherry_T5of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_GFP_T1of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_GFP_T2of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_GFP_T3of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_GFP_T4of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_GFP_T5of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_mCherry_T1of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_mCherry_T2of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_mCherry_T3of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_mCherry_T4of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Worm_MeanIntensity_Straightened_mCherry_T5of5_L1of1'
                    ),
                    SpreadsheetColumnSelection(
                        subject='NonOverlappingWorms',
                        feature='Children_HeadMarkers_Count'
                    )
                ),
                'export_all_measurement_types': False,
                'file_selections': (
                    SpreadsheetFileSelection(
                        subjects=(
                            'StraightenedWorms',
                        ),
                        file_name='StraightenedWorms.csv'
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