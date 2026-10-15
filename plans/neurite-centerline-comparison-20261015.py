"""Assisted two-field check of root-fragment pruning and subpixel centreline length.

Same four input TIFFs, preprocessing, detection and 5 µm cutoff as the retained
pruning check. New destination, one worker. Not a blind trial or a new biological
default chosen to match MetaXpress. The 1-pixel geometric smoothing scale is
explicit; zero selects unsmoothed geometry for a controlled comparison.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-branch-pruning-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/centerline-5um'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], minimum_branch_length=5.0,
                             centerline_smoothing_sigma_px=1.0),
    }),
])]
