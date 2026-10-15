"""Recheck the reported A25 continuation with the same 7.5 µm cutoff.

Detection, smoothing, inputs and single-worker execution are unchanged. Only
the canonical pruning implementation changes. Keep the faulty predecessor
outputs for a matched raw/graph review; this is assisted development.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-pruning-7p5um-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/continuation-repair-7p5um'),
    ),
)
pipeline_steps = previous['pipeline_steps']
