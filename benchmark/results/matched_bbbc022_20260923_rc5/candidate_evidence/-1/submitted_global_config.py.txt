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
    num_workers=2,
    multiprocessing_start_method=MultiprocessingStartMethod.FORK,
    well_filter_config=WellFilterConfig(
        well_filter=[
            'A01',
            'A12',
            'B01',
            'B12',
            'C01',
            'C12',
            'D01',
            'D12'
        ]
    ),
    analysis_consolidation_config=AnalysisConsolidationConfig(
        enabled=False
    ),
    path_planning_config=PathPlanningConfig(
        well_filter=0,
        output_dir_suffix='_matched_pilot',
        global_output_folder=Path('/home/ts/code/projects/openhcs/benchmark/results/matched_bbbc022_20260923_rc5/candidate/-1')
    )
)