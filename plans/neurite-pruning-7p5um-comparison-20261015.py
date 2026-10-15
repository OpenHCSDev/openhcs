"""Stronger pruning requested after reviewing the 5 µm subpixel result.

Only minimum_branch_length changes: 5 to 7.5 µm (3.69 to 5.53 native pixels).
The two previously inspected fields, detection and 1-pixel geometric smoothing
are unchanged. This is assisted development, not a blind trial; preserve the
5 µm results and inspect lost short biological branches as well as nuisance.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-centerline-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/centerline-7p5um'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], minimum_branch_length=7.5),
    }),
])]
