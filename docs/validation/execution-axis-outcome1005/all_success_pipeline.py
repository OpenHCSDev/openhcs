from pathlib import Path

from openhcs.core.config import (
    LazyPathPlanningConfig,
    LazySourceBindingsConfig,
    LazyStepMaterializationConfig,
    PipelineConfig,
)
from openhcs.core.source_bindings import (
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.custom_functions.axis_outcome_probe1005 import axis_outcome_probe1005

pipeline_config = PipelineConfig(
    num_workers=2,
    source_bindings_config=LazySourceBindingsConfig(
        bindings=(NamedSourceBinding(alias="ProbeImage"),),
        metadata_rules=(MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern=r"probe_(?P<well>A0[12])_s(?P<site>1)_w(?P<channel>1)\.tif$",
        ),),
    ),
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=Path("/run/media/ts/hdd/openhcs-engineering/execution-axis1005-20261006/all-success"),
        output_dir_suffix="_all_success",
    ),
)
pipeline_steps = [
    FunctionStep(
        name="PersistBeforeFailure",
        func=(axis_outcome_probe1005, {"fail_above": 2.0}),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True),
    ),
    FunctionStep(
        name="QualifySyntheticAxis",
        func=(axis_outcome_probe1005, {"fail_above": 2.0}),
    ),
]
