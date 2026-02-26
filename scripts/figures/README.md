# Figure Generation Scripts

This directory contains scripts for generating various figures, plots, and visualizations from imaging data and analysis results.

## Scripts

### `generate_xy_xz_composite_figures.py`
Creates composite figures showing XY, XZ, and YZ max projections for each well.

**Features:**
- Pairs XY, XZ, and YZ max projection images
- Creates figures with a two-column layout (XY left, XZ/YZ stacked right)
- Includes well identification in titles
- Optional metadata mapping to append labels to titles
- Automatic column labels (HA-OXIME/matrigel with Time A/B/C)
- Optional well notation toggle for titles/filenames (R##C## or A01)
- Optional tiled mosaic output aligned by well position
- Output filenames include group labels when available

**Usage:**
```bash
python scripts/figures/generate_xy_xz_composite_figures.py \
    --input-dir /path/to/max_project \
    --output-dir /path/to/output

# Optional metadata mapping
python scripts/figures/generate_xy_xz_composite_figures.py \
    --input-dir /path/to/max_project \
    --output-dir /path/to/output \
    --metadata-csv /path/to/metadata.csv

# Optional tiled mosaic output
python scripts/figures/generate_xy_xz_composite_figures.py \
    --input-dir /path/to/max_project \
    --output-dir /path/to/output \
    --mosaic-output /path/to/output/mosaic.png

# Optional well notation toggle
python scripts/figures/generate_xy_xz_composite_figures.py \
    --input-dir /path/to/max_project \
    --output-dir /path/to/output \
    --well-format a01
```

---

### `generate_figure_overlays.py`
Generates figure overlays showing analyzed wells with ROIs (Regions of Interest) overlaid on images.

**Features:**
- Matches ROI files (.roi.zip) to corresponding images
- Filters wells based on analysis configuration (excludes excluded wells)
- Overlays polygon ROIs with labels on images
- Supports multiprocessing for faster processing
- Includes channel information and well annotations

**Usage:**
```bash
python scripts/figures/generate_figure_overlays.py \
    --plate-dir /path/to/plate1 \
    --plate-dir /path/to/plate2 \
    --config /path/to/config.xlsx \
    --results /path/to/results.csv
```

---

### `generate_automated_plots.py`
Generates automated bar plots with statistical analysis from compiled results files.

**Features:**
- Reads plot configuration from config.xlsx (plot_config sheet)
- Creates bar plots with error bars (SEM)
- Includes scatter points for individual data points
- Runs statistical tests (ANOVA, pairwise t-tests)
- Adds significance markers (*, **, ***, ns)
- Processes three data types: normalized, raw per replicate, and raw per well

**Usage:**
```bash
python scripts/figures/generate_automated_plots.py \
    --config /path/to/config.xlsx \
    --results-dir /path/to/compiled_results \
    --output-dir /path/to/plots
```

---

### `generate_figure_mosaics.py`
Creates mosaic/grid images from individual figure overlays, grouping by condition.

**Features:**
- Groups figures by experimental condition
- Creates grid layouts (roughly square)
- Sorts images by channel and replicate
- Outputs high-resolution mosaics (300 DPI)

**Usage:**
```bash
python scripts/figures/generate_figure_mosaics.py \
    --figures-dir /path/to/figures \
    --output-dir /path/to/mosaics
```

## Workflow

Typical figure generation workflow:

1. **Generate overlays**: Use `generate_figure_overlays.py` to create individual well figures with ROIs
2. **Create composites**: Use `generate_xy_xz_composite_figures.py` for projection comparisons
3. **Build mosaics**: Use `generate_figure_mosaics.py` to create condition summary grids
4. **Plot statistics**: Use `generate_automated_plots.py` for quantitative analysis plots

## Dependencies

All scripts require:
- Python 3.x
- matplotlib
- numpy
- PIL/Pillow
- pandas (for automated plots)
- scipy (for statistical tests)
- openhcs package (for ROI handling)

## Related

See also `../napari-plugins/` for napari plugins for creating orthogonal projections and exporting layers directly from napari.
