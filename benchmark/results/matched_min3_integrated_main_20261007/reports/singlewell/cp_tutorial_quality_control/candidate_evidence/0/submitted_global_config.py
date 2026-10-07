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
        global_output_folder=Path('/home/ts/.local/state/openhcs-maintenance/20261007/min3-integrated-main-official30-v1/capture/cases/cp_tutorial_quality_control/candidate/0')
    )
)