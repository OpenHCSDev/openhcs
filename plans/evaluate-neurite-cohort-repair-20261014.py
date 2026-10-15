"""Compare the completed fixed-recipe replay using the paper's existing decoder.

No image processing or parameter tuning. Both runs must contain exactly the
same 180 well/site identities. Two technical wells per dose are descriptive
replicates, not independent biological experiments.
"""
from pathlib import Path
from runpy import run_path
import csv

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

repo = Path('/home/ts/code/projects/openhcs')
scratch = Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014')
science = Path('/run/media/ts/hdd/openhcs-science')
output = scratch / 'cohort-evaluation'
comparison = run_path(str(repo / 'paper/figures/compare_personal_neurite.py'))
comparison['compare'](
    Path('/home/ts/code/projects/mfd/papers/mfd_platform/supplementary_bio/'
         'figure_output_september_outgrowth_20260924/outgrowth_wells.csv'),
    Path('/run/media/ts/0BA20E780BA20E78/slas-private-evaluation-20260915/'
         'neurite-source-key/private_source_key.json'),
    science / 'personal-neurite-graphical-three-20261008/P001_GRAPHICAL_115/'
              'final-attempt/source-plate_openhcs/results',
    output,
    comparison['SiteMeanWellAggregation'](),
    'P001',
    repo / 'paper/supplementary/personal_neurite_autonomous/author115/pipeline.py',
    metrics=comparison['METRICS'],
    workbook=Path('/run/media/ts/0BA20E780BA20E78/axotomy_testing/'
                  '2026-09-04-(complete)/neurite outgrowth/results.xlsx'),
    guided_summaries=scratch / 'cohort-repaired/cohort-input_openhcs/results',
    guided_pipeline=repo / 'plans/neurite-cohort-repair-comparison-20261014.py',
    guided_label='Assisted fixed-recipe replay on main 09a808015; not a new blind trial',
)
with (output / 'treatment_effects.csv').open() as stream:
    effects = list(csv.DictReader(stream))
with (output / 'joined_wells.csv').open() as stream:
    wells = list(csv.DictReader(stream))
conditions = list(dict.fromkeys(row['condition'] for row in effects))
methods = [('metaxpress', 'MetaXpress', '#222222', '-'),
           ('openhcs', 'Frozen Blind 2', '#ae6a00', '--'),
           ('guided_openhcs', 'Corrected engine', '#0072b2', '-')]
for name, metrics in [
    ('per-cell-effects', [('mean_outgrowth', 'Length per cell'),
                         ('branches_per_cell', 'Branches per cell'),
                         ('cell_count', 'Detected cells')]),
    ('total-effects', [('total_outgrowth', 'Total field length'),
                      ('total_branches', 'Total field branches'),
                      ('branches_per_process', 'Branches per primary process')]),
]:
    fig, axes = plt.subplots(len(conditions), len(metrics), figsize=(13, 7),
                             layout='constrained', squeeze=False)
    for axes_row, condition in zip(axes, conditions):
        for axis, (metric, label) in zip(axes_row, metrics):
            rows = sorted((row for row in effects if row['condition'] == condition
                           and row['metric'] == metric), key=lambda row: float(row['dose_uM']))
            for method, title, color, style in methods:
                axis.plot([float(row['dose_uM']) for row in rows],
                          [float(row[f'{method}_fold_change']) for row in rows],
                          marker='o', markersize=4, label=title, color=color, linestyle=style)
                column = metric if method == 'metaxpress' else f'{method}_{metric}'
                control = float(rows[0][f'{method}_control_mean'])
                points = [row for row in wells if row['condition'] == condition]
                axis.scatter([float(row['nominal_dose_uM']) for row in points],
                             [float(row[column]) / control for row in points],
                             color=color, s=12, alpha=.5)
            axis.axhline(1, color='#bbbbbb', linewidth=.7)
            axis.set_title(f'{condition}: {label}')
            axis.set_xlabel('Dose (µM)')
            axis.set_ylabel('Fold of own DMSO control')
            axis.set_xticks([0, 5, 10, 20, 40])
            axis.spines[['top', 'right']].set_visible(False)
    axes[0, 0].legend(frameon=False, fontsize=9)
    fig.suptitle('Same 20 wells / 180 fields; fixed Blind 2 recipe on corrected engine\n'
                 'Nine-field well means; two technical wells per dose; algorithm comparison, not manual truth',
                 fontsize=11)
    fig.savefig(output / f'{name}.png', dpi=180)
    fig.savefig(output / f'{name}.pdf')
    plt.close(fig)

for condition in conditions:
    print(condition)
    for row in effects:
        if row['condition'] == condition and float(row['dose_uM']) > 0 and row['metric'] in (
            'mean_outgrowth', 'total_outgrowth', 'branches_per_cell',
            'total_branches', 'branches_per_process', 'cell_count',
        ):
            print(row['dose_uM'], row['metric'],
                  {title: round(100 * float(row[f'{method}_fractional_change']), 2)
                   for method, title, _, _ in methods})
