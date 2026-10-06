# OpenHCS configuration

from openhcs.core.config import (
    AnalysisConsolidationConfig,
    GlobalPipelineConfig,
    MultiprocessingStartMethod,
    PathPlanningConfig,
    WellFilterConfig,
)
from pathlib import Path

config = GlobalPipelineConfig(
    materialize_runtime_artifacts=False,
    multiprocessing_start_method=MultiprocessingStartMethod.FORK,
    well_filter_config=WellFilterConfig(
        well_filter=[
            'A01'
        ]
    ),
    analysis_consolidation_config=AnalysisConsolidationConfig(
        enabled=False
    ),
    path_planning_config=PathPlanningConfig(
        well_filter=0,
        output_dir_suffix='_matched_pilot',
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261006/runtime-artifact-last-consumer-resumed-singlewell-v1/singlewell/capture/cases/ExampleImagingFlowCytometryObjectsInGrid/candidate/0')
    )
)