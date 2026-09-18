#!/usr/bin/env python3
"""
Annotate wells in OpenHCS metadata files with experimental condition information.

This script reads experimental layout from a config file and MetaXpress results CSV,
then adds experimental annotations (N/replicate, condition, dose) to wells in
openhcs_metadata.json files.

Usage:
    python annotate_wells_with_experimental_metadata.py \
        --results /path/to/metaxpress_style_summary.csv \
        --config /path/to/config.xlsx \
        --batch-dir /path/to/batch_directory
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional

# Add openhcs to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from openhcs.formats.experimental_analysis import read_plate_layout, load_plate_groups
from polystore.metadata_writer import AtomicMetadataWriter, get_metadata_path


def convert_standard_to_opera_phenix_well_id(well_id: str) -> str:
    """
    Convert standard well ID (B03) to Opera Phenix format (R02C03).

    Args:
        well_id: Standard format well ID (e.g., B03)

    Returns:
        Opera Phenix format well ID (e.g., R02C03)
    """
    # Match standard format: Letter + digits
    match = re.match(r"([A-Z])(\d+)", well_id.upper())
    if match:
        row_letter = match.group(1)
        col_num = int(match.group(2))

        # Convert letter to row number (A=1, B=2, etc.)
        row_num = ord(row_letter) - ord("A") + 1

        # Format as Opera Phenix well ID
        return f"R{row_num:02d}C{col_num:02d}"

    # If not standard format, return as-is
    return well_id


def parse_metaxpress_csv(csv_path: Path) -> Dict[str, Dict[str, List[str]]]:
    """
    Parse MetaXpress CSV to extract plate IDs, plate names, and wells.

    Returns:
        Dict mapping plate_id -> {"plate_name": str, "wells": List[str]}
    """
    import pandas as pd

    plates = {}
    current_plate_id = None
    current_plate_name = None

    with open(csv_path, "r") as f:
        for line in f:
            parts = line.strip().split(",")
            if not parts:
                continue

            # Look for Plate Name
            if parts[0] == "Plate Name":
                current_plate_name = parts[1]

            # Look for Plate ID
            elif parts[0] == "Plate ID":
                current_plate_id = parts[1]
                if current_plate_id and current_plate_name:
                    plates[current_plate_id] = {
                        "plate_name": current_plate_name,
                        "wells": [],
                    }

            # Look for well data (starts with R##C##)
            elif parts[0].startswith("R") and "C" in parts[0] and current_plate_id:
                well = parts[0]
                plates[current_plate_id]["wells"].append(well)

    return plates


def build_well_annotations(
    plate_id: str,
    replicate: str,
    layout: Dict,
    ctrl_positions: Optional[Dict],
    excluded_positions: Optional[Dict],
    plate_groups: Dict,
) -> Dict[str, str]:
    """
    Build well annotations for a specific plate.

    Args:
        plate_id: Plate ID from MetaXpress CSV
        replicate: Replicate name (e.g., "N1")
        layout: Experimental layout from read_plate_layout
        ctrl_positions: Control well positions
        excluded_positions: Excluded well positions
        plate_groups: Plate groups mapping from load_plate_groups

    Returns:
        Dict mapping well_name -> annotation_string
    """
    annotations = {}

    # Get replicate's layout and plate groups
    replicate_layout = layout.get(replicate, {})
    replicate_groups = plate_groups.get(replicate, {})

    # Build reverse mapping: plate_id -> group_id for this replicate
    group_id_for_plate = None
    for group_id, group_plate_id in replicate_groups.items():
        if str(group_plate_id) == str(plate_id):
            group_id_for_plate = int(group_id)
            break

    if group_id_for_plate is None:
        return annotations  # No matching group for this plate

    # Build annotations from experimental layout
    for condition, doses in replicate_layout.items():
        for dose, well_plate_tuples in doses.items():
            for well, plate_group in well_plate_tuples:
                # Check if this well belongs to this plate's group
                if int(plate_group) == group_id_for_plate:
                    annotation = f"{replicate}_{condition}_{dose}"
                    annotations[well] = annotation

    # Mark control wells
    if ctrl_positions and replicate in ctrl_positions:
        for well, plate_group in ctrl_positions[replicate]:
            if int(plate_group) == group_id_for_plate:
                # Override with control annotation if already exists
                if well in annotations:
                    annotations[well] = f"{annotations[well]}_CONTROL"
                else:
                    annotations[well] = f"{replicate}_CONTROL"

    # Mark excluded wells
    if excluded_positions and replicate in excluded_positions:
        for well, plate_group in excluded_positions[replicate]:
            if int(plate_group) == group_id_for_plate:
                annotations[well] = f"{replicate}_EXCLUDED"

    return annotations


def detect_microscope_format(metadata_path: Path) -> str:
    """
    Detect microscope format from metadata file by examining image filenames.

    Args:
        metadata_path: Path to openhcs_metadata.json

    Returns:
        'opera_phenix' or 'imagexpress' or 'unknown'
    """
    with open(metadata_path, "r") as f:
        metadata = json.load(f)

    # Check image filenames to detect format
    subdirs = metadata.get("subdirectories", {})
    if subdirs:
        first_subdir = next(iter(subdirs.values()))
        image_files = first_subdir.get("image_files", [])

        if image_files:
            # Check first image filename
            first_image = image_files[0].lower()

            # OperaPhenix format: r##c##f###p###-ch#sk#fk#fl#.tif
            if re.search(r"r\d+c\d+f\d+p\d+-ch\d+sk\d+", first_image):
                return "opera_phenix"

            # ImageXpress format: typically has _s#_w# or similar
            # This is a fallback - if not OperaPhenix, assume ImageXpress
            return "imagexpress"

    return "unknown"


def update_metadata_with_annotations(
    metadata_path: Path, well_annotations: Dict[str, str]
) -> None:
    """
    Update openhcs_metadata.json with well annotations.

    Updates the "wells" field in each subdirectory to replace None values with
    experimental condition annotations.

    Converts well IDs to match the microscope format (OperaPhenix uses R02C03, ImageXpress uses B03).

    Args:
        metadata_path: Path to openhcs_metadata.json
        well_annotations: Dict mapping well_name -> annotation_string (in standard format like B03)
    """
    from polystore.atomic import atomic_update_json

    # Detect microscope format
    microscope_format = detect_microscope_format(metadata_path)

    # Convert well IDs if needed
    if microscope_format == "opera_phenix":
        # Convert standard well IDs (B03) to OperaPhenix format (R02C03)
        converted_annotations = {
            convert_standard_to_opera_phenix_well_id(well): annotation
            for well, annotation in well_annotations.items()
        }
        print(f"   Converted well IDs to OperaPhenix format (e.g., B03 -> R02C03)")
    else:
        # Keep standard format for ImageXpress
        converted_annotations = well_annotations

    def update_func(data):
        """Update wells field in all subdirectories with experimental annotations."""
        if data is None:
            data = {}

        # Update wells field in each subdirectory
        subdirs = data.get("subdirectories", {})
        for subdir_name, subdir_data in subdirs.items():
            wells = subdir_data.get("wells", {})
            if wells:
                # Update all wells that have annotations (replace existing values)
                for well_id in wells.keys():
                    if well_id in converted_annotations:
                        # Always include well ID in the display string
                        wells[well_id] = f"{well_id}: {converted_annotations[well_id]}"

        # Also store at top level for easy access
        data["experimental_annotations"] = converted_annotations

        return data

    # Use atomic update to safely add the field
    atomic_update_json(metadata_path, update_func, lock_timeout=30.0)
    print(
        f"✅ Updated {metadata_path} with {len(converted_annotations)} well annotations"
    )


def main():
    parser = argparse.ArgumentParser(
        description="Annotate wells in OpenHCS metadata with experimental conditions"
    )
    parser.add_argument(
        "--results",
        required=True,
        type=Path,
        help="Path to MetaXpress-style results CSV",
    )
    parser.add_argument(
        "--config",
        required=True,
        type=Path,
        help="Path to experimental config Excel file",
    )
    parser.add_argument(
        "--batch-dir",
        required=True,
        type=Path,
        help="Path to batch directory containing plate folders",
    )

    args = parser.parse_args()

    # Validate inputs
    if not args.results.exists():
        print(f"❌ Results CSV not found: {args.results}")
        sys.exit(1)

    if not args.config.exists():
        print(f"❌ Config file not found: {args.config}")
        sys.exit(1)

    if not args.batch_dir.exists():
        print(f"❌ Batch directory not found: {args.batch_dir}")
        sys.exit(1)

    print("📊 Parsing experimental configuration...")

    # Parse config file
    (
        scope,
        layout,
        conditions,
        ctrl_positions,
        excluded_positions,
        per_well_datapoints,
    ) = read_plate_layout(args.config)
    plate_groups = load_plate_groups(args.config)

    print(f"   Found {len(layout)} replicates")
    print(f"   Found {len(conditions)} conditions")

    # Parse MetaXpress CSV
    print("\n📄 Parsing MetaXpress results CSV...")
    plates = parse_metaxpress_csv(args.results)
    print(f"   Found {len(plates)} plates")

    # Build reverse mapping: plate_id -> replicate
    plate_id_to_replicate = {}
    for replicate, groups in plate_groups.items():
        for group_id, plate_id in groups.items():
            if plate_id is not None:
                plate_id_to_replicate[str(plate_id)] = replicate

    print("\n🔍 Processing plates...")

    # Process each plate
    for plate_id, plate_info in plates.items():
        plate_name = plate_info["plate_name"]
        wells = plate_info["wells"]

        # Find replicate for this plate
        replicate = plate_id_to_replicate.get(plate_id)
        if not replicate:
            print(
                f"⚠️  Skipping plate {plate_id} ({plate_name}): No replicate mapping found"
            )
            continue

        print(f"\n📦 Plate: {plate_name}")
        print(f"   Plate ID: {plate_id}")
        print(f"   Replicate: {replicate}")
        print(f"   Wells: {len(wells)}")

        # Build well annotations
        well_annotations = build_well_annotations(
            plate_id,
            replicate,
            layout,
            ctrl_positions,
            excluded_positions,
            plate_groups,
        )

        print(f"   Annotations: {len(well_annotations)}")

        # Find metadata file
        plate_path = args.batch_dir / plate_name
        if not plate_path.exists():
            print(f"   ⚠️  Plate directory not found: {plate_path}")
            continue

        metadata_path = get_metadata_path(plate_path)
        if not metadata_path.exists():
            print(f"   ⚠️  Metadata file not found: {metadata_path}")
            continue

        # Update metadata
        update_metadata_with_annotations(metadata_path, well_annotations)

    print("\n✅ Done!")


if __name__ == "__main__":
    main()
