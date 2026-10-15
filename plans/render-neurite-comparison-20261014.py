"""Render saved MCP-run graphs against their input pixels; no detection here."""
from pathlib import Path
import csv

import openhcs  # source dependency paths
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
import tifffile
from polystore.roi import load_rois_from_zip

root = Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014')
results = root / 'comparison/input_openhcs/results'
for well, site, limits in [('A25', 7, (84, 600)), ('A34', 8, (72, 700))]:
    stem = f'{well}_s{site:03d}_w2_z001_t001'
    raw = tifffile.imread(root / 'input' / f'{stem}.tif').squeeze()
    graphs = [load_rois_from_zip(results / f'{stem}_neurite_morphology_step{step}.graph.roi.zip')
              for step in (0, 1)]
    for crop_name, bounds in [('field', (0, 1024, 0, 1024)),
                              ('shaft', (430, 760, 190, 760))]:
        fig, axes = plt.subplots(1, 3, figsize=(15, 6), layout='constrained')
        for column, axis in enumerate(axes):
            axis.imshow(raw, cmap='gray', vmin=limits[0], vmax=limits[1], interpolation='nearest')
            if column:
                segments = [shape.coordinates[:, ::-1]
                            for roi in graphs[column - 1] for shape in roi.shapes]
                axis.add_collection(LineCollection(segments, colors='#ff3da5', linewidths=.7))
            y0, y1, x0, x1 = bounds
            axis.set_xlim(x0, x1)
            axis.set_ylim(y1, y0)
            axis.set_title(['Raw FITC', 'Embedded enhancement', 'Local signal only'][column])
            axis.set_xlabel('Source x (pixels)')
        axes[0].set_ylabel('Source y (pixels)')
        fig.suptitle(f'{well} site {site}: identical input, body settings and preprocessing; display {limits}')
        fig.savefig(root / f'{well}-{crop_name}-comparison.png', dpi=160)
        plt.close(fig)
    for step in (0, 1):
        path = results / f'{well}_site-{site}_z_index-1_timepoint-1_neurite_outgrowth_summary_step{step}_details.csv'
        row = next(csv.DictReader(path.open()))
        print(well, step, {key: row[key] for key in ('number_of_cells', 'total_outgrowth', 'total_branches')})

    # These checkpoint filenames are overwritten by the second step in this
    # runtime; they diagnose the local-only result, not both candidates.
    checkpoint_dir = root / 'comparison/input_openhcs/images'
    stages = ['candidate_mask', 'local_response', 'initial_owned_trace',
              'secondary_ownership', 'repaired_owned_trace']
    fig, axes = plt.subplots(2, 3, figsize=(15, 10), layout='constrained')
    for axis, stage in zip(axes.flat, ['raw', *stages]):
        data = raw if stage == 'raw' else tifffile.imread(
            checkpoint_dir / f'{stem}_neurite_{stage}.checkpoint.tif'
        ).squeeze()
        if stage == 'raw':
            axis.imshow(data, cmap='gray', vmin=limits[0], vmax=limits[1])
        elif stage == 'local_response':
            axis.imshow(data, cmap='magma', vmin=0, vmax=200)
        else:
            axis.imshow(data > 0, cmap='gray', vmin=0, vmax=1)
        axis.set_xlim(450, 780)
        axis.set_ylim(850, 500)
        axis.set_title(stage)
    fig.savefig(root / f'{well}-local-only-stages.png', dpi=150)
    plt.close(fig)

    repaired_results = root / 'owner-support/input_openhcs/results'
    if repaired_results.exists():
        repaired_graph = load_rois_from_zip(
            repaired_results / f'{stem}_neurite_morphology_step0.graph.roi.zip'
        )
        for crop_name, bounds in [('field', (0, 1024, 0, 1024)),
                                  ('repair-shaft', (500, 850, 450, 780))]:
            fig, axes = plt.subplots(1, 3, figsize=(15, 7), layout='constrained')
            for column, axis in enumerate(axes):
                axis.imshow(raw, cmap='gray', vmin=limits[0], vmax=limits[1],
                            interpolation='nearest')
                if column:
                    graph = graphs[1] if column == 1 else repaired_graph
                    segments = [shape.coordinates[:, ::-1]
                                for roi in graph for shape in roi.shapes]
                    axis.add_collection(LineCollection(segments, colors='#ff3da5', linewidths=.7))
                y0, y1, x0, x1 = bounds
                axis.set_xlim(x0, x1)
                axis.set_ylim(y1, y0)
                axis.set_title(['Raw FITC', 'Before repair-support fix',
                                'Shared accepted-shaft support'][column])
            fig.suptitle(f'{well} site {site}: same settings, local-only admission')
            fig.savefig(root / f'{well}-{crop_name}-owner-support.png', dpi=160)
            plt.close(fig)
        path = repaired_results / f'{well}_site-{site}_z_index-1_timepoint-1_neurite_outgrowth_summary_step0_details.csv'
        row = next(csv.DictReader(path.open()))
        print(well, 'owner-support', {key: row[key] for key in
                                    ('number_of_cells', 'total_outgrowth', 'total_branches')})
