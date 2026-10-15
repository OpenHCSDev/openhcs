"""Assisted fixed-recipe replay of the 20-well blind treatment cohort.

Use Blind 2's Gaussian 0.8 / FITC soma / local-background-100 recipe unchanged,
with the current detector on main 09a808015. This is not a new blind author or
a replacement for frozen author115. Evaluate the original site-mean protocol
and each drug curve's own zero-dose controls only after execution. No tuning
against reference effects. TIFF compression changes storage, not pixel values.
"""
from dataclasses import replace
from pathlib import Path
from runpy import run_path

from openhcs.core.config import LazyPathPlanningConfig, LazyTiffConfig
from polystore.config import TiffCompression

previous = run_path(
    '/home/ts/code/projects/openhcs/plans/neurite-enhancement-comparison-20261014.py'
)
pipeline_config = replace(
    previous['pipeline_config'],
    num_workers=2,
    tiff_config=LazyTiffConfig(compression=TiffCompression.DEFLATE, compression_level=1),
    path_planning_config=LazyPathPlanningConfig(
        partition_filter=0,
        global_output_folder=Path(
            '/home/ts/.cache/agent-scratch/neurite-detector-20261014/cohort-repaired'
        ),
    ),
)
pipeline_steps = previous['pipeline_steps'][1:]
