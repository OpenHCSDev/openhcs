"""Synthetic paired-channel exporter journey, not a blind biological trial."""

from pathlib import Path

from openhcs.constants import AllComponents, GroupBy, Microscope, VariableComponents
from openhcs.core.config import (
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazySourceBindingsConfig,
    LazyVFSConfig,
    MaterializationBackend,
    PipelineConfig,
)
from openhcs.core.source_bindings import (
    ComponentSelector, MetadataExtractionRule, MetadataSource,
    NamedSourceBinding, SourceFilterClause, SourceFilterMatchType,
    SourceFilterSubject, SourceSelector, LazyStepSourceBindingsConfig,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.object_images import convert_image_to_objects
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod, identify_secondary_objects
from openhcs.processing.backends.cellprofiler.shape import measure_object_size_shape
from openhcs.processing.backends.cellprofiler.spreadsheet_export import export_to_spreadsheet

pipeline_config = PipelineConfig(
    num_workers=1,
    use_threading=True,
    microscope=Microscope.IMAGEXPRESS,
    processing_config=LazyProcessingConfig(
        variable_components=[VariableComponents.SITE], group_by=GroupBy.CHANNEL,
    ),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern=r"(?P<Well>[A-Z]\d{2})_s(?P<Site>\d+)_w(?P<Channel>\d+)_z(?P<ZIndex>\d+)_t(?P<Timepoint>\d+)",
        ),),
        bindings=tuple(
            NamedSourceBinding(
                alias=alias,
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.CHANNEL, channel),),
                    filters=(SourceFilterClause(
                        SourceFilterSubject.FILE, SourceFilterMatchType.CONTAINS,
                        f"_w{channel}_",
                    ),),
                ),
                component_identity=tuple(
                    ComponentSelector(component, value)
                    for component, value in (
                        (AllComponents.CHANNEL, channel),
                        (AllComponents.SITE, "1"),
                        (AllComponents.Z_INDEX, "1"),
                        (AllComponents.TIMEPOINT, "1"),
                    )
                ),
            )
            for alias, channel in (("DNA", "1"), ("Actin", "2"))
        ),
    ),
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=Path("/home/ts/wt/openhcs-issue-batch-20260929/paired-field-parent-20260930/outputs"),
        # This journey's durable result is the typed CSV bundle, not raw copies.
        well_filter=0,
    ),
    vfs_config=LazyVFSConfig(materialization_backend=MaterializationBackend.DISK),
)
pipeline_steps = [
    FunctionStep(
        name="KnownNuclei",
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="DNA"),),
        ),
        func={"1": (convert_image_to_objects, {
            "select_the_input_image": "DNA", "name_the_output_objects": "Nuclei",
            "cast_to_bool": True,
        })},
    ),
    FunctionStep(
        name="KnownCells",
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="Actin"),),
        ),
        func={"2": (identify_secondary_objects, {
            "select_the_input_image": "Actin", "select_the_input_objects": "Nuclei",
            "name_the_objects_to_be_identified": "Cells", "method": SecondaryMethod.DISTANCE_N,
            "distance_to_dilate": 2,
        })},
    ),
    FunctionStep(
        name="CellShapes",
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="Actin"),),
        ),
        func={"2": (measure_object_size_shape, {
            "select_object_sets_to_measure": "Cells",
            "calculate_advanced": False, "calculate_zernikes": False,
        })},
    ),
    FunctionStep(
        name="CompleteCellRows",
        func=(export_to_spreadsheet, {"add_filename_prefix": False}),
    ),
]
