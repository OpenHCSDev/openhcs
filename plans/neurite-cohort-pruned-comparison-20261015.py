"""Fixed-settings replay on the matched 20 wells / 180 fields.

Apply the reviewed 10 um continuation pruning, 12 um soma-extension filter,
and 1 px centerline smoothing without changing detection or preprocessing.
This is assisted development, not a new blind trial. Preserve all frozen runs
and the previous cohort replay. Compare references only after execution.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-soma-pruning-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    num_workers=2,
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/cohort-pruned'),
    ),
)
pipeline_steps = previous['pipeline_steps']
