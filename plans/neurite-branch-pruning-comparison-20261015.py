"""Assisted two-field integration check of a 5 micrometer branch cutoff.

Same inputs, preprocessing and detection as the retained 14 October replay.
Five micrometers is a bounded diagnostic setting, not a fitted biological
default or a claim of matching MetaXpress. Frozen trials are unchanged.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

baseline = run_path('/home/ts/code/projects/openhcs/plans/neurite-cohort-repair-comparison-20261014.py')
pipeline_config = replace(
    baseline['pipeline_config'], num_workers=1,
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/pruning-5um'),
    ),
)
step = baseline['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], minimum_branch_length=5.0),
    }),
])]
