"""Four-field sensitivity follow-up: soma pruning 20 um, neurite cutoff 125.

Lower only the process-channel local-background cutoff, from 150 to 125.
Preserve prior outputs and all preprocessing, cell detection, pruning and
smoothing settings. Assisted development, not a new autonomous evaluation.

Completed A02/s8, A34/s2, A49/s3, A60/s5 via main MCP, execution
1c0d5152-eaf7-45df-a0bd-1d820b1b25f2. Body masks identical (755 cells).
Total length: 116535.076 -> 122869.647 um; branches: 1648 -> 1807.
Exported graph geometry agrees with reported lengths. No viewer endpoint;
OpenHCS skill-guided matched saved-artifact review is in
soma-20um-cutoff-125/qa-body-boundaries under the scratch root below.

Not accepted as a soma-loop repair: faint extensions increase, but tiny loops
persist and some increase. A02/s8 owner 135 is the lower bright-body witness:
its mask contains 101 pixels, smaller than the visible diffuse body extent;
its retained graph reaches 38.390 um from that mask, exceeding the 20 um gate.
The existing soma pruner rejects whole components, not local cyclic pieces.
User supplied additional loop examples during this run. These need a separate
body-boundary/local-loop repair, not another global sensitivity increase.
Full-cohort results and library defaults remain unchanged.
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
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-20um-cutoff-125'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], intensity_above_local_background=125.0),
    }),
])]
