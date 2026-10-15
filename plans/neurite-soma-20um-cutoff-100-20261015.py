"""Assisted four-field comparison: lower neurite cutoff 125 -> 100 only.

Keep the soma candidate threshold at 1.0, soma extension at 20 um,
branch pruning at 10 um, and the predecessor's preprocessing and smoothing.
Use the existing sensitivity-input fields A02/s8, A34/s2, A49/s3, A60/s5.
Preserve all earlier outputs. This is not a blind or full-cohort evaluation.

Completed through main's OpenHCS 0.8.7 MCP runtime, execution
97b08199-881a-412f-8b58-14e79123d55d. All 755 soma masks are pixel-identical
to cutoff 125. Across the four fields, length changed from 122869.647 to
129660.659 um, processes from 1959 to 2024, and branches from 1807 to 2008.
Exported graph branch distances reconcile with the summary lengths.

No managed viewer endpoint was available. Matched saved-graph/raw comparisons
are in soma-20um-cutoff-100/qa-vs125 under the declared output parent.
All four crops were inspected: longer faint extensions are retained, while
soma-adjacent loops remain (A02 lower bright body; A49 dense central cluster).
A60's isolated bright body near x570/y325 remains without a traced process.
This is a sensitivity comparison, not an accepted loop repair or a replacement
for the frozen cohort analysis. Soma threshold remains 1.0 throughout.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

previous = run_path('/home/ts/code/projects/openhcs/plans/neurite-soma-20um-cutoff-125-20261015.py')
pipeline_config = replace(
    previous['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-20um-cutoff-100'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
assert parameters['cell_body'].candidate_threshold_correction_factor == 1.0
assert parameters['outgrowth'].intensity_above_local_background == 125.0
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'outgrowth': replace(parameters['outgrowth'], intensity_above_local_background=100.0),
    }),
])]
