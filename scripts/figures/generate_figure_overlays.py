#!/usr/bin/env python3
"""
Generate figure overlays for analyzed wells.

For each image subdirectory with a corresponding results subdirectory:
1. Find all .roi.zip files in the results directory
2. Match each .roi.zip to its corresponding image file
3. Check if the well is used in analysis (not excluded)
4. If yes, create a figure with the image (uint8) and ROIs overlaid with labels

Usage:
    python generate_figure_overlays.py --plate-dir /path/to/plate_folder
"""

import argparse
import json
import logging
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from multiprocessing import Pool, cpu_count

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend for multiprocessing
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import Polygon
from skimage import io
from skimage.exposure import rescale_intensity

# Add openhcs to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from openhcs.core.roi import load_rois_from_zip, PolygonShape
from openhcs.formats.experimental_analysis import read_plate_layout, load_plate_groups

logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)


def load_metadata(plate_dir: Path) -> dict:
    """Load openhcs_metadata.json from plate directory."""
    metadata_path = plate_dir / "openhcs_metadata.json"
    if not metadata_path.exists():
        raise FileNotFoundError(f"Metadata file not found: {metadata_path}")
    
    with open(metadata_path, 'r') as f:
        return json.load(f)


def convert_standard_to_opera_phenix_well_id(well_id: str) -> str:
    """
    Convert standard well ID (B03) to Opera Phenix format (R02C03).

    Args:
        well_id: Standard format well ID (e.g., B03)

    Returns:
        Opera Phenix format well ID (e.g., R02C03)
    """
    import re

    # Match standard format: Letter + digits
    match = re.match(r'([A-Z])(\d+)', well_id.upper())
    if match:
        row_letter = match.group(1)
        col_num = int(match.group(2))

        # Convert letter to row number (A=1, B=2, etc.)
        row_num = ord(row_letter) - ord('A') + 1

        # Format as Opera Phenix well ID
        return f"R{row_num:02d}C{col_num:02d}"

    # If not standard format, return as-is
    return well_id


def get_used_wells_from_config(
    config_path: Path,
    results_csv_path: Path,
    plate_name: str
) -> set:
    """
    Get set of wells that are used in analysis (not excluded) from config.xlsx.

    Args:
        config_path: Path to config.xlsx
        results_csv_path: Path to MetaXpress results CSV
        plate_name: Name of the plate to check

    Returns:
        Set of well IDs (in OperaPhenix format) that are not excluded
    """
    import re

    # Load experimental layout and plate groups
    scope, layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints = read_plate_layout(config_path)
    plate_groups = load_plate_groups(config_path)

    # Parse results CSV to get plate ID for this plate name
    plate_id = None
    replicate = None

    with open(results_csv_path, 'r') as f:
        current_plate_name = None
        for line in f:
            parts = line.strip().split(',')
            if not parts:
                continue

            if parts[0] == 'Plate Name':
                current_plate_name = parts[1]
            elif parts[0] == 'Plate ID' and current_plate_name == plate_name:
                plate_id = parts[1]
                break

    if not plate_id:
        logger.warning(f"Could not find plate ID for plate name: {plate_name}")
        return set()

    # Find which replicate this plate belongs to
    for rep, groups in plate_groups.items():
        for group_id, group_plate_id in groups.items():
            if str(group_plate_id) == str(plate_id):
                replicate = rep
                group_id_for_plate = int(group_id)
                break
        if replicate:
            break

    if not replicate:
        logger.warning(f"Could not find replicate for plate ID: {plate_id}")
        return set()

    # Build set of used wells (not excluded)
    used_wells = set()

    # Get wells from experimental layout
    replicate_layout = layout.get(replicate, {})
    for condition, doses in replicate_layout.items():
        for dose, well_plate_tuples in doses.items():
            for well, plate_group in well_plate_tuples:
                if int(plate_group) == group_id_for_plate:
                    # Convert to OperaPhenix format
                    opera_well = convert_standard_to_opera_phenix_well_id(well)
                    used_wells.add(opera_well)

    # Add control wells
    if ctrl_positions and replicate in ctrl_positions:
        for well, plate_group in ctrl_positions[replicate]:
            if int(plate_group) == group_id_for_plate:
                opera_well = convert_standard_to_opera_phenix_well_id(well)
                used_wells.add(opera_well)

    # Remove excluded wells
    if excluded_positions and replicate in excluded_positions:
        for well, plate_group in excluded_positions[replicate]:
            if int(plate_group) == group_id_for_plate:
                # Excluded wells are already in OperaPhenix format, don't convert
                used_wells.discard(well)

    return used_wells


def find_image_results_pairs(plate_dir: Path, metadata: dict) -> List[Tuple[str, str]]:
    """
    Find pairs of image and results subdirectories.
    
    Returns:
        List of (image_subdir, results_subdir) tuples
    """
    subdirs = metadata.get('subdirectories', {})
    pairs = []
    
    for subdir_name in subdirs.keys():
        # Check if there's a corresponding results directory
        results_subdir = f"{subdir_name}_results"
        results_path = plate_dir / results_subdir
        
        if results_path.exists() and results_path.is_dir():
            pairs.append((subdir_name, results_subdir))
    
    return pairs


def match_roi_to_image(roi_zip_path: Path, image_dir: Path) -> Optional[Path]:
    """
    Find the image file that corresponds to a .roi.zip file.
    
    The image filename (minus extension) should be a substring of the roi.zip filename.
    
    Args:
        roi_zip_path: Path to .roi.zip file
        image_dir: Directory containing image files
    
    Returns:
        Path to matching image file, or None if not found
    """
    # Get roi filename without .roi.zip extension
    roi_stem = roi_zip_path.name.replace('.roi.zip', '')
    
    # Find all image files in the directory
    image_extensions = ['.tif', '.tiff', '.png', '.jpg']
    for img_path in image_dir.iterdir():
        if img_path.suffix.lower() in image_extensions:
            # Check if image stem is substring of roi stem
            img_stem = img_path.stem
            if img_stem in roi_stem:
                return img_path
    
    return None


def extract_well_from_filename(filename: str) -> Optional[str]:
    """
    Extract well ID from filename.

    Handles both standard (A01) and OperaPhenix (R01C01) formats.
    """
    import re

    # Try OperaPhenix format first (r##c##)
    match = re.search(r'[Rr](\d+)[Cc](\d+)', filename)
    if match:
        row_num = int(match.group(1))
        col_num = int(match.group(2))
        return f"R{row_num:02d}C{col_num:02d}"

    # Try standard format (A01, B02, etc.)
    match = re.search(r'([A-Z])(\d+)', filename.upper())
    if match:
        return match.group(0)

    return None


def extract_channel_number_from_filename(filename: str) -> Optional[int]:
    """
    Extract channel number from filename.

    Examples:
        r02c02f001p001-ch2sk1fk1fl1 -> 2
        r02c02f001p001-ch3sk1fk1fl1 -> 3
    """
    import re

    match = re.search(r'-ch(\d+)', filename.lower())
    if match:
        return int(match.group(1))

    return None


def get_channel_name_from_metadata(metadata: dict, subdir_name: str, channel_number: int) -> Optional[str]:
    """
    Get channel name from metadata.

    Args:
        metadata: Full metadata dict
        subdir_name: Subdirectory name (e.g., "cellbody", "images")
        channel_number: Channel number (1-indexed)

    Returns:
        Channel name (e.g., "Alexa 647", "DAPI") or None
    """
    subdirs = metadata.get('subdirectories', {})
    subdir_data = subdirs.get(subdir_name, {})
    channels = subdir_data.get('channels', {})

    # Channels are stored as strings in metadata
    channel_key = str(channel_number)
    return channels.get(channel_key)


def convert_to_uint8(image: np.ndarray) -> np.ndarray:
    """Convert image to uint8 with rescaling."""
    # Rescale to 0-255 range
    image_rescaled = rescale_intensity(image, out_range=(0, 255))
    return image_rescaled.astype(np.uint8)


def process_single_roi_file(args):
    """
    Process a single ROI file (worker function for multiprocessing).

    Args:
        args: Tuple of (roi_zip_path, image_dir, figures_dir, well_annotations,
                       used_wells, metadata, image_subdir)

    Returns:
        Tuple of (success: bool, output_filename: str or None, error_msg: str or None)
    """
    roi_zip_path, image_dir, figures_dir, well_annotations, used_wells, metadata, image_subdir = args

    try:
        # Extract well ID from filename
        well_id = extract_well_from_filename(roi_zip_path.name)
        if not well_id:
            return (False, None, f"Could not extract well ID from: {roi_zip_path.name}")

        # Check if well is used in analysis
        if well_id not in used_wells:
            return (False, None, None)  # Silently skip excluded wells

        # Find matching image file
        image_path = match_roi_to_image(roi_zip_path, image_dir)
        if not image_path:
            return (False, None, None)  # Silently skip if no matching image

        # Verify image file actually exists
        if not image_path.exists():
            return (False, None, None)  # Silently skip if image doesn't exist

        # Load ROIs
        rois = load_rois_from_zip(roi_zip_path)

        # Get well annotation for label
        well_annotation = well_annotations.get(well_id, well_id)

        # Extract channel number from filename and get channel name from metadata
        channel_number = extract_channel_number_from_filename(roi_zip_path.name)
        channel_name = None
        if channel_number:
            channel_name = get_channel_name_from_metadata(metadata, image_subdir, channel_number)
            # If no channel name in metadata, fall back to "Ch#"
            if not channel_name:
                channel_name = f"Ch{channel_number}"

        # Extract just the annotation part (after the colon) for filename
        if ': ' in well_annotation:
            annotation_part = well_annotation.split(': ', 1)[1]
        else:
            annotation_part = well_annotation

        # Create output path with annotation and channel name in filename
        if channel_name:
            output_filename = f"{image_path.stem}_{annotation_part}_{channel_name}.png"
        else:
            output_filename = f"{image_path.stem}_{annotation_part}.png"
        output_path = figures_dir / output_filename

        # Create figure overlay
        create_figure_overlay(image_path, rois, well_annotation, channel_name, output_path)

        return (True, output_filename, None)

    except Exception as e:
        return (False, None, f"Failed to process {roi_zip_path.name}: {e}")


def create_figure_overlay(
    image_path: Path,
    rois: List,
    well_annotation: str,
    channel_name: Optional[str],
    output_path: Path
) -> None:
    """
    Create a figure with image and ROI overlays.

    Args:
        image_path: Path to image file
        rois: List of ROI objects
        well_annotation: Well annotation string (e.g., "R02C02: N1_DMSO_Control_0_CONTROL")
        channel_name: Channel name (e.g., "Ch2", "Ch3")
        output_path: Path to save figure
    """
    # Load image
    image = io.imread(image_path)

    # Convert to uint8
    if image.dtype != np.uint8:
        image = convert_to_uint8(image)

    # Create figure
    fig, ax = plt.subplots(figsize=(12, 10), dpi=150)

    # Display image
    ax.imshow(image, cmap='gray')
    ax.axis('off')

    # Overlay ROIs - just colored outlines, no individual labels
    for idx, roi in enumerate(rois):
        for shape in roi.shapes:
            if isinstance(shape, PolygonShape):
                # Create polygon patch
                coords = shape.coordinates  # (y, x) format
                coords_xy = coords[:, [1, 0]]  # Convert to (x, y) for matplotlib

                polygon = Polygon(
                    coords_xy,
                    fill=False,
                    edgecolor='yellow',
                    linewidth=1.0,
                    alpha=0.7
                )
                ax.add_patch(polygon)

    # Build title with well annotation and channel
    title_parts = [well_annotation]
    if channel_name:
        title_parts.append(channel_name)
    title = " | ".join(title_parts)

    ax.set_title(title, fontsize=17, weight='bold', pad=10)

    # Save figure
    output_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_path, bbox_inches='tight', dpi=150)
    plt.close(fig)

    logger.info(f"   Saved figure: {output_path.name}")


def process_plate(plate_dir: Path, config_path: Path, results_csv_path: Path) -> None:
    """
    Process a single plate directory to generate figure overlays.

    Args:
        plate_dir: Path to plate directory
        config_path: Path to config.xlsx
        results_csv_path: Path to MetaXpress results CSV
    """
    logger.info(f"\n📦 Processing plate: {plate_dir.name}")

    # Load metadata
    try:
        metadata = load_metadata(plate_dir)
    except FileNotFoundError as e:
        logger.error(f"   {e}")
        return

    # Get wells used in analysis from config.xlsx
    used_wells = get_used_wells_from_config(config_path, results_csv_path, plate_dir.name)
    logger.info(f"   Found {len(used_wells)} wells used in analysis (from config.xlsx)")

    # Get well annotations for labels
    well_annotations = {}
    subdirs = metadata.get('subdirectories', {})
    if subdirs:
        first_subdir = next(iter(subdirs.values()))
        well_annotations = first_subdir.get('wells', {})

    # Find image/results pairs
    pairs = find_image_results_pairs(plate_dir, metadata)
    logger.info(f"   Found {len(pairs)} image/results subdirectory pairs")

    if not pairs:
        logger.warning("   No image/results pairs found")
        return

    # Process each pair
    total_figures = 0
    for image_subdir, results_subdir in pairs:
        logger.info(f"\n   🔍 Processing: {image_subdir} -> {results_subdir}")

        image_dir = plate_dir / image_subdir
        results_dir = plate_dir / results_subdir
        figures_dir = plate_dir / f"{image_subdir}_figures"

        # Find all .roi.zip files
        roi_files = list(results_dir.glob('*.roi.zip'))
        logger.info(f"      Found {len(roi_files)} ROI files")

        if not roi_files:
            continue

        # Prepare arguments for multiprocessing
        args_list = [
            (roi_zip_path, image_dir, figures_dir, well_annotations, used_wells, metadata, image_subdir)
            for roi_zip_path in roi_files
        ]

        # Process ROI files in parallel
        num_workers = max(1, cpu_count() - 1)  # Leave one CPU free
        logger.info(f"      Processing with {num_workers} workers...")

        with Pool(num_workers) as pool:
            results = pool.map(process_single_roi_file, args_list)

        # Count successes and log errors
        for success, output_filename, error_msg in results:
            if success:
                total_figures += 1
                logger.info(f"      ✓ Saved: {output_filename}")
            elif error_msg:
                logger.error(f"      ✗ {error_msg}")

    logger.info(f"\n✅ Generated {total_figures} figure overlays for {plate_dir.name}")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Generate figure overlays for analyzed wells with ROIs"
    )
    parser.add_argument(
        '--plate-dir',
        type=Path,
        action='append',
        help='Path to plate directory containing openhcs_metadata.json (can be specified multiple times)'
    )
    parser.add_argument(
        '--config',
        type=Path,
        required=True,
        help='Path to config.xlsx file'
    )
    parser.add_argument(
        '--results',
        type=Path,
        required=True,
        help='Path to MetaXpress results CSV file'
    )

    args = parser.parse_args()

    if not args.plate_dir:
        logger.error("No plate directories specified. Use --plate-dir to specify at least one directory.")
        sys.exit(1)

    if not args.config.exists():
        logger.error(f"Config file not found: {args.config}")
        sys.exit(1)

    if not args.results.exists():
        logger.error(f"Results CSV not found: {args.results}")
        sys.exit(1)

    # Process each plate directory
    for plate_dir in args.plate_dir:
        if not plate_dir.exists():
            logger.error(f"Plate directory not found: {plate_dir}")
            continue

        if not plate_dir.is_dir():
            logger.error(f"Not a directory: {plate_dir}")
            continue

        process_plate(plate_dir, args.config, args.results)

    logger.info("\n✅ All plates processed!")


if __name__ == '__main__':
    main()

