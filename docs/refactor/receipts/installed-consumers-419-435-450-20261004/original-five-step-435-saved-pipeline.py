# OpenHCS pipeline

from openhcs.constants.constants import (
    AllComponents,
    GroupBy,
    Microscope,
    VariableComponents,
)
from openhcs.constants.input_source import InputSource
from openhcs.core.config import (
    LazyNapariStreamingConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazyStepMaterializationConfig,
    LazyTiffConfig,
    LazyWellFilterConfig,
    PipelineConfig,
)
from openhcs.core.source_bindings import (
    ComponentSelector,
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    NamedSourceBinding,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.color import (
    GrayToColorModule,
    ImageChannelType,
)
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.func_registry import get_function
from pathlib import Path
from polystore.config import TiffCompression

path_root = Path('/home/ts/.local/state/openhcs-maintenance/20261004/installed-consumer-419-435-450-v2/outputs')

pipeline_config = PipelineConfig(
    materialization_results_path=path_root / 'input_openhcs' / 'results',
    materialize_runtime_artifacts=True,
    num_workers=1,
    microscope=Microscope.SOURCE_BINDINGS,
    use_threading=False,
    well_filter_config=LazyWellFilterConfig(
        well_filter='A01'
    ),
    tiff_config=LazyTiffConfig(
        compression=TiffCompression.DEFLATE,
        compression_level=9
    ),
    source_bindings_config=LazySourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias='FITC',
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.EQUALS,
                            value='A01_s001_w2_z001_t001.tif'
                        ),
                    )
                ),
                component_identity=(
                    ComponentSelector(
                        component=AllComponents.WELL,
                        value='A01'
                    ),
                    ComponentSelector(
                        component=AllComponents.SITE,
                        value='1'
                    ),
                    ComponentSelector(
                        component=AllComponents.CHANNEL,
                        value='2'
                    ),
                    ComponentSelector(
                        component=AllComponents.Z_INDEX,
                        value='1'
                    ),
                    ComponentSelector(
                        component=AllComponents.TIMEPOINT,
                        value='1'
                    )
                )
            ),
        ),
        source_voxel_spacing=SourceVoxelSpacing(
            values_zyx=(
                1.3556,
                1.3556
            )
        )
    ),
    path_planning_config=LazyPathPlanningConfig(
        well_filter='A01',
        global_output_folder=path_root
    ),
    step_materialization_config=LazyStepMaterializationConfig(
        well_filter='A01',
        enabled=False
    ),
    napari_streaming_config=LazyNapariStreamingConfig(
        enabled=False
    )
)

pipeline_steps = [
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.NONE,
                'factors': (
                    1.0,
                ),
                'truncate_low': False,
                'truncate_high': False,
                'select_the_first_image': 'FITC',
                'name_the_output_image': 'raw_calcein_body_reference'
            }),
        name='RawCalceinNamedIdentityContractProbe',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PIPELINE_START
        ),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias='FITC'
                ),
            )
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=False
        )
    ),
    FunctionStep(
        func=(get_function('skimage:exposure.rescale_intensity'), {
                'in_range': (
                    0.0005951018539711605,
                    0.09155413138017852
                ),
                'out_range': (
                    0.0,
                    1.0
                )
            }),
        name='CapOnlyOutgrowthLaneAtOriginal6000Counts',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PREVIOUS_STEP
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=False
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_image_math'), {
                'operation': ImageMathOperation.NONE,
                'factors': (
                    1.0,
                ),
                'truncate_low': False,
                'truncate_high': False,
                'name_the_output_image': 'capped_calcein_outgrowth'
            }),
        name='NameCappedScalarCalcein',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PREVIOUS_STEP
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=False
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_gray_to_color'), {
                'color_scheme': GrayToColorModule.Scheme.STACK,
                'rescale_intensity': False,
                'image_name': (
                    'raw_calcein_body_reference',
                    'capped_calcein_outgrowth'
                ),
                'name_the_output_image': 'raw_and_cap_channel_last'
            }),
        name='ComposeDeclaredScalarRawAndCappedArtifacts',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PREVIOUS_STEP
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=False
        )
    ),
    FunctionStep(
        func=(get_function('openhcs:cellprofiler_color_to_gray'), {
                'image_type': ImageChannelType.CHANNELS,
                'channel_indices': (
                    0,
                    1
                ),
                'contributions': (
                    1.0,
                    1.0
                ),
                'select_the_input_image': 'raw_and_cap_channel_last',
                'image_name': (
                    'raw_body_processing_role',
                    'capped_outgrowth_processing_role'
                )
            }),
        name='ProjectColorChannelsToAlignedProcessingRoles',
        processing_config=LazyProcessingConfig(
            variable_components=[
                VariableComponents.CHANNEL
            ],
            group_by=GroupBy.NONE,
            input_source=InputSource.PREVIOUS_STEP
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=False
        )
    )
]