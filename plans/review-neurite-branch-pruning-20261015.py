"""Review persisted outputs of the MCP pruning check; no image analysis rerun.

The managed Napari route previously failed on Image._slicing_state. These are
explicit saved-artifact comparisons, not a claim of native-viewer acceptance.
"""
import argparse
import csv
import json
from pathlib import Path
import zipfile

import openhcs  # source dependency paths
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
import numpy as np
import tifffile
from polystore.roi import load_rois_from_zip

root = Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--before', default='cohort-repaired/cohort-input_openhcs/results')
parser.add_argument('--after', default='pruning-5um')
parser.add_argument('--label', default='5 µm pruning')
parser.add_argument('--check-geometry', action='store_true')
args = parser.parse_args()
before = root / args.before
after = root / args.after / 'input_openhcs/results'
output = root / args.after / 'review'
output.mkdir(parents=True, exist_ok=True)
rows = []
for well, site, dim in [('A25', 7, (84, 600)), ('A34', 8, (72, 700))]:
    stem = f'{well}_s{site:03d}_w2_z001_t001'
    fitc = tifffile.imread(root / 'input' / f'{stem}.tif').squeeze()
    dapi = tifffile.imread(root / 'input' / f'{stem.replace("_w2_", "_w1_")}.tif').squeeze()
    moderate = np.percentile(fitc, [1, 98])
    dapi_window = np.percentile(dapi, [1, 99.5])
    paths = [folder / f'{stem}_neurite_morphology_step0.graph.roi.zip' for folder in (before, after)]
    graphs = [load_rois_from_zip(path) for path in paths]
    segments = [[shape.coordinates[:, ::-1] for roi in graph for shape in roi.shapes] for graph in graphs]
    for method, folder, path, graph in zip(('before', args.after), (before, after), paths, graphs):
        name = f'{well}_site-{site}_z_index-1_timepoint-1_neurite_outgrowth'
        with (folder / f'{name}_summary_step0_details.csv').open() as stream:
            row = next(csv.DictReader(stream))
        with (folder / f'{name}_cells_step0_details.csv').open() as stream:
            cells = list(csv.DictReader(stream))
        assert len(cells) == int(row['number_of_cells'])
        assert sum(int(c['branches']) for c in cells) == int(row['total_branches'])
        with zipfile.ZipFile(path) as archive:
            edges = json.loads(archive.read('__polystore_roi_metadata__.json'))
        assert np.isclose(sum(e['branch_distance'] for e in edges.values()), float(row['total_outgrowth']))
        if args.check_geometry and method != 'before':
            # ImageJ stores coordinates as float32; CSV lengths use float64.
            # Check every edge, not just cancellation in the field sum.
            for roi in graph:
                measured = sum(np.linalg.norm(np.diff(shape.coordinates.astype(float), axis=0), axis=1).sum()
                               for shape in roi.shapes) * 1.3556
                assert np.isclose(measured, roi.metadata['branch_distance'], rtol=1e-5, atol=2e-4), (roi.metadata['edge_id'], measured, roi.metadata['branch_distance'])
        result = dict(well=well, site=site, method=method,
                      **{key: row[key] for key in ('number_of_cells', 'total_outgrowth', 'total_branches', 'total_processes')})
        rows.append(result)
        print(result, flush=True)
    crops = [('field', (0, 1024, 0, 1024)), ('shaft', (450, 780, 500, 850))]
    if well == 'A25':
        crops.append(('reported-loop', (540, 655, 735, 825)))
        crops.append(('fragment', (608, 625, 762, 781)))
        crops.append(('diagonal-shaft', (550, 570, 737, 765)))
    for label, (x0, x1, y0, y1) in crops:
        fig, axes = plt.subplots(2, 3, figsize=(14, 9), layout='constrained')
        for i, axis in enumerate(axes.flat):
            if i == 0:
                axis.imshow(dapi, cmap='gray', vmin=dapi_window[0], vmax=dapi_window[1], interpolation='nearest')
            elif i < 5:
                window = moderate if i == 1 else dim
                axis.imshow(fitc, cmap='gray', vmin=window[0], vmax=window[1], interpolation='nearest')
            else:
                axis.set_facecolor('black')
            if i >= 3:
                axis.add_collection(LineCollection(segments[0 if i == 3 else 1], colors='#ff3da5', linewidths=.8))
            axis.set(xlim=(x0, x1), ylim=(y1, y0))
            axis.set_title(['Raw DAPI', 'Raw FITC moderate', 'Raw FITC dim',
                            'Before + dim raw', f'{args.label} + dim raw', f'{args.label}: graph only'][i])
        fig.suptitle(f'{well} site {site}; source pixels; 1.3556 µm/px; gamma 1\n'
                     f'FITC moderate {tuple(map(float, moderate.round(2)))}, dim {dim}; DAPI {tuple(map(float, dapi_window.round(2)))}')
        fig.savefig(output / f'{well}-{label}.png', dpi=160)
        plt.close(fig)
with (output / 'measurements.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
