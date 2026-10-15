"""Requested four-field follow-up: 20 um soma reach, neurite cutoff 200.

Change only the soma-extension cutoff from the prior 40 um / 200 candidate.
Keep the same raw fields, cell-body settings, preprocessing, 10 um branch
pruning and one-pixel centreline smoothing. Preserve previous runs.
This is assisted development, not a new blind trial or library default.

Completed on A02/s8, A34/s2, A49/s3 and A60/s5. Matched review retains
more supported processes than 40 um, but connected soma-adjacent loops remain.
Cell masks are unchanged; exported graph lengths reconcile with summaries.
QA: soma-20um-sensitivity/qa-vs40 under the declared scratch root.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-soma-40um-sensitivity-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-20um-sensitivity'),
    ),
)
step = previous['pipeline_steps'][1]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], minimum_soma_extension=20.0),
    }),
])]
