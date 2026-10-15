"""Assisted two-field comparison of soma-confined process pruning.

Keep 10 µm branch pruning, detection, cell masks and smoothing unchanged.
Require 12 µm spatial reach from the owning soma: the reported A25 cell 84
loop and stubs remain within 11.18 µm, while its long left process exceeds
400 µm and must retain its proximal attachment. This is development evidence,
not a blind run, a default change, or an assertion about vendor internals.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-pruning-10um-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-pruning-12um'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], minimum_soma_extension=12.0),
    }),
])]
