# OpenHCS pipeline

from pathlib import Path

from openhcs.constants.constants import AllComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import (
    LazyNapariStreamingConfig,
    LazyProcessingConfig,
    PipelineConfig,
)
from openhcs.core.source_bindings import (
    ComponentSelector,
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.primary_objects import (
    identify_primary_objects,
)
from openhcs.processing.backends.cellprofiler.secondary import (
    identify_secondary_objects,
)
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    materialization_results_path=Path(
        "/home/ts/code/projects/openhcs/mcp_outputs/slas-validation-20260915/"
        "trials/BBBC007/sol-independent-01/development_outputs"
    ),
    materialize_runtime_artifacts=True,
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern=(
                    r"^(?P<Well>[A-H][0-9]{2})_"
                    r"s(?P<Site>[0-9]+)_w(?P<Channel>[0-9]+)_"
                    r"z(?P<ZIndex>[0-9]+)_t(?P<Timepoint>[0-9]+)"
                ),
            ),
        ),
        source_filters=(
            SourceFilterClause(
                subject=SourceFilterSubject.EXTENSION,
                match_type=SourceFilterMatchType.IS_IMAGE,
            ),
        ),
        bindings=(
            NamedSourceBinding(
                alias="DNA",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value="_w1_",
                        ),
                    ),
                ),
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="Actin",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFilterSubject.FILE,
                            match_type=SourceFilterMatchType.CONTAINS,
                            value="_w2_",
                        ),
                    ),
                ),
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        ),
    ),
)

pipeline_steps = [
    FunctionStep(
        func=(identify_primary_objects, {"exclude_border_objects": False}),
        name="Segment DNA nuclei",
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="DNA"),),
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=True,
            persistent=True,
            host="127.0.0.1",
            transport_mode=TransportMode.TCP,
            port=5643,
        ),
    ),
    FunctionStep(
        func=identify_secondary_objects,
        name="Propagate cell boundaries in actin channel",
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="Actin"),),
        ),
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=True,
            persistent=True,
            host="127.0.0.1",
            transport_mode=TransportMode.TCP,
            port=5643,
        ),
    ),
]
