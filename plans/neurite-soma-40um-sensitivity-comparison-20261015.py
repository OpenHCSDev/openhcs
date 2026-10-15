"""Assisted four-field diagnostic: stronger soma filtering, then lower sensitivity.

Step 0 changes only soma-extension reach from 12 to 40 micrometers.
Step 1 also raises the local neurite response cutoff from 100 to 200.
Both steps restart from the same raw inputs. Cell bodies, Gaussian 0.8,
10 micrometer branch pruning and one-pixel centreline smoothing are unchanged.
These are development candidates, not accepted full-cohort results.

Completed on A02/s8, A34/s2, A49/s3 and A60/s5. Matched raw/graph review
shows loss of supported processes while some connected soma-adjacent loops
remain. Do not promote this aggressive diagnostic to the cohort default.
Review images: soma-40um-sensitivity/qa-moderate under the declared scratch root.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-cohort-pruned-comparison-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    num_workers=1,
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-40um-sensitivity'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [
    step.with_function_spec([
        blur, (analysis, {
            **parameters,
            'outgrowth': replace(
                parameters['outgrowth'], minimum_soma_extension=40.0,
                intensity_above_local_background=cutoff,
            ),
        }),
    ])
    for cutoff in (100.0, 200.0)
]
