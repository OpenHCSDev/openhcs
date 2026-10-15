"""Four-field sensitivity follow-up: soma pruning 20 um, neurite cutoff 150.

Change only the process-channel local-background cutoff from 200 to 150.
Keep preprocessing, cell detection, branch pruning and smoothing unchanged.
Preserve the 200-cutoff comparison. Assisted development, not a blind run.

Completed A02/s8, A34/s2, A49/s3, A60/s5 through main's MCP runtime.
Execution: e381c938-27fc-447c-8c87-8c86097c20e0 (complete, no error).
Same 755 cell masks pixel-for-pixel. Total length 104077.937 -> 116535.076 um;
branches 1333 -> 1648. Exported graph lengths reconcile with summaries.
Matched saved-artifact review follows the OpenHCS skill; no viewer endpoint
was available. QA: soma-20um-cutoff-150/qa-vs200 in the scratch root below.
A02 retains more faint vertical growth near x600/y500; A60 retains longer
faint extensions. The main supported shafts remain in these reviewed crops.
Small soma-adjacent loops persist and some increase (A02 lower bright body,
A49 around x560/y410). This is a sensitivity candidate, not a loop fix or a
whole-cohort biological acceptance claim. Full-cohort results are unchanged.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-soma-20um-sensitivity-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-20um-cutoff-150'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], intensity_above_local_background=150.0),
    }),
])]
