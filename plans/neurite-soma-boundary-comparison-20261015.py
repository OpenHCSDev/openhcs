"""Repair bright-core-only soma detection at fixed neurite cutoff 125.

The A02/s8 bright core is about 43,000 raw units, its visible rim 1,750-3,080,
and nearby background about 225 (5x5 sample medians). Lower the compact body's
adaptive threshold multiplier to 0.25, retaining its mean-response, area and
width qualification, marker settings and every neurite parameter. Compare
body extents, neighbouring cells and process exits on the same four fields.
This is an assisted development candidate; preserve all predecessors.

Executed through main-source MCP, execution
7c642dcc-fa60-436f-9d1e-8daf7871f6eb, all four fields complete. Results under
soma-boundary-025/sensitivity-input_openhcs/results; matched raw/mask/graph
reviews in qa-vs125 and the A02 x434,y704 witness in qa-witness.
No live viewer endpoints were available; review uses persisted native outputs.

REJECTED as a replacement recipe. A02 witness mask grows from 101 to 375
pixels, improving its bright-core-only boundary, but the distal loop remains.
Other bodies absorb shaft signal (e.g. A02 x565,y370), and A60 x410,y570
loses its previous body label while tracing appears across the raw body.
The body's downstream width/qualification gate needs stage-specific inspection;
the retained labels alone do not establish which predicate rejected it.
Across A02/s8, A34/s2, A49/s3 and A60/s5: cells 755 -> 872, length
122869.646839 -> 97624.612427 um, branches 1807 -> 1308. No new label
covers a majority of two old bodies, but that overlap check is not biological
proof of cell separation or correct new detections. Exported graph lengths
match reported totals within 0.001 um per field (coordinate serialization).
Leave the library default at 1.0 and preserve the preceding recipe. This
control makes the actual foreground gate editable; it does not establish a
complete soma-loop repair or alter the frozen full-cohort comparison.
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
        global_output_folder=Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014/soma-boundary-025'),
    ),
)
step = previous['pipeline_steps'][0]
blur, (analysis, parameters) = step.function_spec()
pipeline_steps = [step.with_function_spec([
    blur, (analysis, {
        **parameters,
        'cell_body': replace(parameters['cell_body'], candidate_threshold_correction_factor=0.25),
    }),
])]
