"""Matched saved-artifact review; no detector work and no synthetic annotations.

The native viewer is unavailable owing to its Napari slicing-state API error.
Render persisted graph coordinates directly against the unchanged input TIFFs.
Four fields/crop centers were selected in the frozen author's prior review,
not by their new effect sizes. Display fits never enter the detector.
"""
from pathlib import Path
import argparse
import csv
import openhcs
import numpy as np
import tifffile
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
from polystore.roi import load_rois_from_zip

root = Path('/home/ts/.cache/agent-scratch/neurite-detector-20261014')
old = Path('/run/media/ts/hdd/openhcs-science/personal-neurite-graphical-three-20261008/'
           'P001_GRAPHICAL_115/final-attempt/source-plate_openhcs/results')
new = root / 'cohort-repaired/cohort-input_openhcs/results'
output = root / 'cohort-evaluation/qa'
states = []
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--well', action='append', help='Render only these already completed selected wells.')
parser.add_argument('--before', type=Path, default=old)
parser.add_argument('--after', type=Path, default=new)
parser.add_argument('--output', type=Path, default=output)
parser.add_argument('--before-label', default='Frozen Blind 2')
parser.add_argument('--after-label', default='Corrected engine')
args = parser.parse_args()
old, new, output = args.before, args.after, args.output
output.mkdir(parents=True, exist_ok=True)
for well, site, x, y in [('A49', 3, 450, 490), ('A02', 8, 520, 540),
                          ('A34', 2, 520, 550), ('A60', 5, 500, 420)]:
    if args.well and well not in args.well:
        continue
    stem = f'{well}_s{site:03d}_w2_z001_t001'
    fitc = tifffile.imread(root / 'cohort-input' / f'{stem}.tif').squeeze()
    dapi = tifffile.imread(root / 'cohort-input' / f'{stem.replace("_w2_", "_w1_")}.tif').squeeze()
    fitc_limits = np.percentile(fitc, [1, 98])
    dim_limits = np.percentile(fitc, [1, 90])
    dapi_limits = np.percentile(dapi, [1, 99.5])
    graphs = [load_rois_from_zip(folder / f'{stem}_neurite_morphology_step0.graph.roi.zip')
              for folder in (old, new)]
    segments = [[shape.coordinates[:, ::-1] for roi in graph for shape in roi.shapes]
                for graph in graphs]
    fig, axes = plt.subplots(2, 3, figsize=(15, 10), layout='constrained')
    titles = ['Raw DAPI', 'Raw FITC', 'Raw FITC, dim window',
              f'{args.before_label} + dim raw', f'{args.after_label} + dim raw', f'{args.after_label}: graph only']
    for i, axis in enumerate(axes.flat):
        if i == 0:
            axis.imshow(dapi, cmap='gray', vmin=dapi_limits[0], vmax=dapi_limits[1])
        elif i < 5:
            limits = dim_limits if i >= 2 else fitc_limits
            axis.imshow(fitc, cmap='gray', vmin=limits[0], vmax=limits[1])
        else:
            axis.set_facecolor('black')
        if i >= 3:
            axis.add_collection(LineCollection(segments[0 if i == 3 else 1],
                                               colors='#ff3da5', linewidths=.65))
        axis.set_xlim(x - 200, x + 200)
        axis.set_ylim(y + 200, y - 200)
        axis.set_title(titles[i])
    fig.suptitle(f'{well} site {site}; source crop center x={x}, y={y}; native pixels\n'
                 f'FITC {tuple(np.round(fitc_limits, 2).tolist())}, dim {tuple(np.round(dim_limits, 2).tolist())}; '
                 f'DAPI {tuple(np.round(dapi_limits, 2).tolist())}; gamma 1; original 1.3556 µm/px', fontsize=11)
    fig.savefig(output / f'{well}-s{site}-matched.png', dpi=150)
    plt.close(fig)
    states.append(dict(well=well, site=site, x=x, y=y, fitc_low=fitc_limits[0],
                       fitc_high=fitc_limits[1], fitc_dim_high=dim_limits[1],
                       dapi_low=dapi_limits[0], dapi_high=dapi_limits[1]))
with (output / 'display-windows.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=list(states[0]))
    writer.writeheader()
    writer.writerows(states)
print(f'Rendered {len(states)} matched saved-artifact reviews to {output}')
