# BBBC013 independent-01 development pipeline

from pathlib import Path

from openhcs.constants.constants import AllComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import (
    GlobalPipelineConfig,
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
from openhcs.processing.backends.cellprofiler.intensity import measure_object_intensity
from openhcs.processing.backends.cellprofiler.primary_objects import (
    identify_primary_objects,
)
from openhcs.processing.backends.cellprofiler.secondary import (
    SecondaryMethod,
    identify_secondary_objects_with_replacement_primary,
    identify_tertiary_objects,
)
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerThresholdMethod,
    CellProfilerThresholdScope,
)
from zmqruntime.config import TransportMode

repository_root = Path("/home/ts/code/projects/openhcs")
development_plate = (
    repository_root
    / "mcp_outputs"
    / "slas-validation-20260915"
    / "inputs"
    / "BBBC013"
    / "development"
)
plate_paths = [development_plate]
global_config = GlobalPipelineConfig()

per_plate_configs = {
    development_plate: PipelineConfig(
        materialization_results_path=(
            repository_root
            / "mcp_outputs"
            / "slas-validation-20260915"
            / "trials"
            / "BBBC013"
            / "sol-independent-01"
            / "development"
            / "outputs"
        ),
        materialize_runtime_artifacts=True,
        source_bindings_config=LazySourceBindingsConfig(
            metadata_rules=(
                MetadataExtractionRule(
                    source=MetadataSource.FILE_NAME,
                    pattern="^(?P<Well>[A-H][0-9]{2})_s(?P<Site>[0-9]+)_w(?P<Channel>[0-9]+)_z(?P<ZIndex>[0-9]+)_t(?P<Timepoint>[0-9]+)",
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
                    alias="GFP",
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS,
                                value="_w1_",
                            ),
                        ),
                    ),
                    component_identity=(
                        ComponentSelector(component=AllComponents.CHANNEL, value="1"),
                    ),
                ),
                NamedSourceBinding(
                    alias="DNA",
                    selector=SourceSelector(
                        filters=(
                            SourceFilterClause(
                                subject=SourceFilterSubject.FILE,
                                match_type=SourceFilterMatchType.CONTAINS,
                                value="_w2_",
                            ),
                        ),
                    ),
                    component_identity=(
                        ComponentSelector(component=AllComponents.CHANNEL, value="2"),
                    ),
                ),
            ),
        ),
    )
}

pipeline_data = {
    development_plate: [
        FunctionStep(
            func=(
                identify_primary_objects,
                {
                    "min_diameter": 10,
                    "max_diameter": 40,
                    "exclude_size": True,
                    "exclude_border_objects": True,
                    "threshold_scope": CellProfilerThresholdScope.GLOBAL,
                    "threshold_method": CellProfilerThresholdMethod.OTSU,
                    "threshold_smoothing_scale": 1.0,
                    "threshold_correction_factor": 1.0,
                    "maximum_object_count": 1000,
                    "name_the_primary_objects_to_be_identified": "Nuclei",
                },
            ),
            name="Segment DRAQ nuclei",
            processing_config=LazyProcessingConfig(
                input_source=InputSource.PIPELINE_START
            ),
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
            func=(
                identify_secondary_objects_with_replacement_primary,
                {
                    "method": SecondaryMethod.DISTANCE_N,
                    "distance_to_dilate": 12,
                    "discard_edge_objects": True,
                    "fill_holes": True,
                    "select_the_input_objects": "Nuclei",
                    "name_the_objects_to_be_identified": "Cells",
                    "name_the_new_primary_objects": "FilteredNuclei",
                },
            ),
            name="Expand nuclei to perinuclear cell regions",
            processing_config=LazyProcessingConfig(
                input_source=InputSource.PIPELINE_START
            ),
            source_bindings=LazyStepSourceBindingsConfig(
                enabled=True,
                bindings=(NamedSourceBinding(alias="GFP"),),
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
            func=(
                identify_tertiary_objects,
                {
                    "shrink_primary": False,
                    "select_the_larger_identified_objects": "Cells",
                    "select_the_smaller_identified_objects": "FilteredNuclei",
                    "name_the_tertiary_objects_to_be_identified": "Cytoplasm",
                },
            ),
            name="Subtract nuclei to form cytoplasmic regions",
            processing_config=LazyProcessingConfig(
                input_source=InputSource.PIPELINE_START
            ),
            source_bindings=LazyStepSourceBindingsConfig(
                enabled=True,
                bindings=(NamedSourceBinding(alias="GFP"),),
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
            func=[
                (
                    measure_object_intensity,
                    {"select_object_sets_to_measure": "FilteredNuclei"},
                ),
                (
                    measure_object_intensity,
                    {"select_object_sets_to_measure": "Cytoplasm"},
                ),
            ],
            name="Measure GFP intensity in matched nuclei and cytoplasm",
            processing_config=LazyProcessingConfig(
                input_source=InputSource.PIPELINE_START
            ),
            source_bindings=LazyStepSourceBindingsConfig(
                enabled=True,
                bindings=(NamedSourceBinding(alias="GFP"),),
            ),
        ),
    ]
}
