"""Repeat the local-only candidate after unifying neurite repair support.

Reuse the paired comparison's exact input declarations and settings. This is
assisted development on already consulted fields, not a blind rerun.

Observed through a fresh source-backed OpenHCS 0.8.7 MCP execution on 2026-10-14:
                 before repair fix          after repair fix
A25 site 7:      32570.514 um, 736 branches   34050.821 um, 760 branches
A34 site 8:      29454.334 um, 660 branches   30028.510 um, 680 branches
Cell counts stayed 127 and 110 respectively. The long A25 shaft within source
y=500:850, x=450:780 was visibly recovered in the saved raw-plus-graph overlay.
These are detected lengths, not manual-ground-truth recall or biological effect
estimates. Small misses and short spurs remain. Native viewer acceptance was
blocked by the installed Napari Image lacking `_slicing_state`; the inspection
used saved artifacts, rendered by render-neurite-comparison-20261014.py.

Artifacts are retained through the named agent-scratch link on the science drive,
not in the frozen blind-run directory. No original input or paper result changed.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig

baseline = run_path(
    '/home/ts/code/projects/openhcs/plans/neurite-enhancement-comparison-20261014.py'
)
pipeline_config = replace(
    baseline['pipeline_config'],
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path(
            '/home/ts/.cache/agent-scratch/neurite-detector-20261014/owner-support'
        ),
    ),
)
pipeline_steps = baseline['pipeline_steps'][1:]
