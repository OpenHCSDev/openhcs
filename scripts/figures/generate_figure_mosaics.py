#!/usr/bin/env python3
"""
Generate mosaic images from individual figure overlays.

Groups figures by condition and channel, creating grid layouts showing all wells
for each condition-channel combination.

Usage:
    python scripts/generate_figure_mosaics.py \
        --figures-dir /path/to/figures \
        --output-dir /path/to/mosaics
"""

import argparse
import logging
from pathlib import Path
from collections import defaultdict
import re

import numpy as np
from PIL import Image
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def parse_filename(filename: str) -> dict:
    """
    Parse figure filename to extract metadata.
    
    Filename format: r02c02f001p001-ch2sk1fk1fl1_N1_DMSO_Control_0_CONTROL_DAPI.png
    
    Returns:
        Dict with keys: well_id, replicate, condition, channel
    """
    stem = filename.replace('.png', '')
    parts = stem.split('_')
    
    # Extract well ID (e.g., r02c02f001p001-ch2sk1fk1fl1)
    well_id = parts[0]
    
    # Extract replicate (e.g., N1, N2, N3)
    replicate = parts[1]
    
    # Extract channel (last part after all underscores)
    channel = parts[-1]
    
    # Extract condition (everything between replicate and channel)
    # Join all parts between replicate and channel, excluding the dose number
    condition_parts = []
    for i in range(2, len(parts) - 1):
        # Skip single digit parts (dose numbers like "0", "1")
        if not (len(parts[i]) == 1 and parts[i].isdigit()):
            condition_parts.append(parts[i])
    condition = '_'.join(condition_parts)
    
    return {
        'well_id': well_id,
        'replicate': replicate,
        'condition': condition,
        'channel': channel,
        'filename': filename
    }


def create_mosaic(image_paths: list, output_path: Path, title: str):
    """
    Create a mosaic grid from a list of image paths.
    
    Args:
        image_paths: List of paths to images
        output_path: Where to save the mosaic
        title: Title for the mosaic
    """
    if not image_paths:
        logger.warning(f"No images to create mosaic for: {title}")
        return
    
    # Load all images
    images = [Image.open(p) for p in image_paths]
    
    # Calculate grid dimensions (try to make it roughly square)
    n_images = len(images)
    n_cols = int(np.ceil(np.sqrt(n_images)))
    n_rows = int(np.ceil(n_images / n_cols))
    
    # Create figure
    fig = plt.figure(figsize=(n_cols * 4, n_rows * 4))
    fig.suptitle(title, fontsize=16, fontweight='bold', y=0.98)

    # Create grid with very tight spacing
    gs = gridspec.GridSpec(n_rows, n_cols, figure=fig,
                          hspace=0.05, wspace=0.03,
                          top=0.95, bottom=0.01, left=0.01, right=0.99)
    
    # Add images to grid
    for idx, img in enumerate(images):
        row = idx // n_cols
        col = idx % n_cols

        ax = fig.add_subplot(gs[row, col])
        ax.imshow(img)
        ax.axis('off')
    
    # Save mosaic at high resolution (300 DPI)
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    
    logger.info(f"   ✓ Saved mosaic: {output_path.name} ({n_images} images)")


def main():
    parser = argparse.ArgumentParser(description='Generate mosaic images from figure overlays')
    parser.add_argument('--figures-dir', type=Path, required=True,
                       help='Directory containing individual figure images')
    parser.add_argument('--output-dir', type=Path, default=None,
                       help='Output directory for mosaics (default: figures-dir/mosaics)')
    
    args = parser.parse_args()
    
    # Set default output directory
    if args.output_dir is None:
        args.output_dir = args.figures_dir / 'mosaics'
    
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    logger.info(f"\n{'='*60}")
    logger.info("Figure Mosaic Generation")
    logger.info(f"{'='*60}")
    logger.info(f"Figures directory: {args.figures_dir}")
    logger.info(f"Output directory: {args.output_dir}")

    # Find all figure images in *_figures directories only
    # Use manual iteration instead of rglob due to potential filesystem issues
    figure_files = []
    for plate_dir in args.figures_dir.iterdir():
        if plate_dir.is_dir():
            for subdir in plate_dir.iterdir():
                if subdir.is_dir() and subdir.name.endswith('_figures'):
                    figure_files.extend(subdir.glob('*.png'))

    figure_files = sorted(figure_files)
    logger.info(f"Found {len(figure_files)} figure images")

    # Group by condition only (not channel)
    groups = defaultdict(list)
    for fig_path in figure_files:
        metadata = parse_filename(fig_path.name)
        key = metadata['condition']
        groups[key].append(fig_path)

    logger.info(f"Grouped into {len(groups)} conditions")
    logger.info(f"\n{'='*60}")
    logger.info("Generating mosaics")
    logger.info(f"{'='*60}\n")

    # Create mosaics for each group
    for condition, image_paths in sorted(groups.items()):
        # Sort images by channel first, then by replicate
        def sort_key(path):
            metadata = parse_filename(path.name)
            return (metadata['channel'], metadata['replicate'])

        sorted_paths = sorted(image_paths, key=sort_key)

        # Create title
        title = f"{condition.replace('_', ' ')}"

        # Create output filename
        output_filename = f"mosaic_{condition}.png"
        output_path = args.output_dir / output_filename

        # Create mosaic
        create_mosaic(sorted_paths, output_path, title)

    logger.info(f"\n{'='*60}")
    logger.info("✅ Mosaic generation complete!")
    logger.info(f"Mosaics saved to: {args.output_dir}")
    logger.info(f"{'='*60}")


if __name__ == '__main__':
    main()

