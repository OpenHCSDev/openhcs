"""Compare 10 µm pruning against corrected 7.5 µm pruning on two development fields.

Only minimum_branch_length changes. Detection and subpixel geometry stay fixed.
Retain the earlier outputs and verify the reported continuous arm still survives.
This is assisted development, not a new library default or a blind evaluation.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-continuation-repair-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/continuation-10um'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], minimum_branch_length=10.0),
    }),
])]
