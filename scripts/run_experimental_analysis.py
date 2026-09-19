#!/usr/bin/env python3
"""
Easy-to-use script for running OpenHCS experimental analysis.

This script consolidates MetaXpress/CX5 results with experimental configuration
to produce normalized results and heatmaps.

Usage:
    python scripts/run_experimental_analysis.py <directory>

    Where <directory> contains:
    - config.xlsx (experimental configuration)
    - metaxpress_style_summary.csv (consolidated results from OpenHCS)

    Output files will be created in the same directory:
    - compiled_results_normalized.xlsx
    - heatmaps.xlsx

Example:
    python scripts/run_experimental_analysis.py /path/to/experiment/2025-10-24
"""

import sys
import re
from pathlib import Path
import pandas as pd


def convert_opera_phenix_to_standard_well_id(well_id: str) -> str:
    """
    Convert Opera Phenix well ID (R02C03) to standard format (B03).

    Args:
        well_id: Opera Phenix format well ID (e.g., R02C03)

    Returns:
        Standard format well ID (e.g., B03)
    """
    # Match Opera Phenix format: R##C##
    match = re.match(r"[Rr](\d+)[Cc](\d+)", well_id)
    if match:
        row_num = int(match.group(1))
        col_num = int(match.group(2))

        # Convert row number to letter (1=A, 2=B, etc.)
        row_letter = chr(ord("A") + row_num - 1)

        # Format as standard well ID
        return f"{row_letter}{col_num:02d}"

    # If not Opera Phenix format, return as-is
    return well_id


def convert_summary_well_ids(csv_path: Path) -> Path:
    """
    Convert Opera Phenix well IDs in summary CSV to standard format.

    Handles multiple summaries (multiple plates) in the same CSV file.
    Creates a new file with _converted suffix.

    Args:
        csv_path: Path to metaxpress_style_summary.csv

    Returns:
        Path to converted CSV file
    """
    # Read the entire CSV as text to preserve MetaXpress header
    with open(csv_path, "r") as f:
        lines = f.readlines()

    # Find ALL "Well" header rows (one per plate/summary)
    well_row_indices = []
    for i, line in enumerate(lines):
        if line.startswith("Well,"):
            well_row_indices.append(i)

    if not well_row_indices:
        # No Well column found, return original
        return csv_path

    # Check if any data rows have Opera Phenix format
    needs_conversion = False
    for well_row_idx in well_row_indices:
        if well_row_idx + 1 < len(lines):
            first_data_line = lines[well_row_idx + 1]
            first_well = first_data_line.split(",")[0].strip()
            if re.match(r"[Rr]\d+[Cc]\d+", first_well):
                needs_conversion = True
                break

    if not needs_conversion:
        return csv_path

    print(f"Converting Opera Phenix well IDs to standard format...")
    print(f"  Found {len(well_row_indices)} summary section(s)")

    # Convert line by line, tracking which section we're in
    converted_lines = []
    in_data_section = False

    for i, line in enumerate(lines):
        # Check if this is a "Well," header row
        if line.startswith("Well,"):
            converted_lines.append(line)
            in_data_section = True
            continue

        # Check if we're in a data section
        if in_data_section:
            # Empty line or new header section ends data section
            if not line.strip() or (
                line.startswith("Barcode,") or line.startswith("Plate Name,")
            ):
                converted_lines.append(line)
                in_data_section = False
                continue

            # Convert data row
            parts = line.split(",", 1)  # Split only on first comma
            if len(parts) >= 2:
                well_id = parts[0].strip()
                rest = parts[1]

                # Convert well ID if it matches Opera Phenix format
                if re.match(r"[Rr]\d+[Cc]\d+", well_id):
                    converted_well = convert_opera_phenix_to_standard_well_id(well_id)
                    converted_lines.append(f"{converted_well},{rest}")
                else:
                    converted_lines.append(line)
            else:
                converted_lines.append(line)
        else:
            # Not in data section, keep line as-is
            converted_lines.append(line)

    # Save to new file
    converted_path = csv_path.parent / f"{csv_path.stem}_converted{csv_path.suffix}"
    with open(converted_path, "w") as f:
        f.writelines(converted_lines)

    print(f"  Saved converted file: {converted_path.name}")
    return converted_path


def convert_config_well_ids(config_path: Path) -> Path:
    """
    Convert Opera Phenix well IDs in config.xlsx to standard format.

    Converts well IDs in:
    - Controls row
    - Exclude Wells row

    Creates a new file with _converted suffix.

    Args:
        config_path: Path to config.xlsx

    Returns:
        Path to converted config file
    """
    import openpyxl

    # Load workbook
    wb = openpyxl.load_workbook(config_path)

    # Check if conversion is needed
    needs_conversion = False

    # Check drug_curve_map sheet for Opera Phenix format wells
    if "drug_curve_map" in wb.sheetnames:
        ws = wb["drug_curve_map"]
        for row in ws.iter_rows():
            for cell in row:
                if cell.value and isinstance(cell.value, str):
                    if re.match(r"[Rr]\d+[Cc]\d+", cell.value):
                        needs_conversion = True
                        break
            if needs_conversion:
                break

    if not needs_conversion:
        return config_path

    print(f"Converting Opera Phenix well IDs in config.xlsx...")

    # Convert drug_curve_map sheet
    if "drug_curve_map" in wb.sheetnames:
        ws = wb["drug_curve_map"]
        for row in ws.iter_rows():
            for cell in row:
                if cell.value and isinstance(cell.value, str):
                    if re.match(r"[Rr]\d+[Cc]\d+", cell.value):
                        cell.value = convert_opera_phenix_to_standard_well_id(
                            cell.value
                        )

    # Save to new file
    converted_path = (
        config_path.parent / f"{config_path.stem}_converted{config_path.suffix}"
    )
    wb.save(converted_path)

    print(f"  Saved converted config: {converted_path.name}")
    return converted_path


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        print("\nError: Missing directory argument")
        sys.exit(1)

    # Get directory from command line
    directory = Path(sys.argv[1])

    if not directory.exists():
        print(f"Error: Directory not found: {directory}")
        sys.exit(1)

    # Define expected input files
    config_file = directory / "config.xlsx"
    results_file = directory / "metaxpress_style_summary.csv"

    # Check if input files exist
    if not config_file.exists():
        print(f"Error: Config file not found: {config_file}")
        print("Expected: config.xlsx in the specified directory")
        sys.exit(1)

    if not results_file.exists():
        print(f"Error: Results file not found: {results_file}")
        print("Expected: metaxpress_style_summary.csv in the specified directory")
        sys.exit(1)

    # Define output files
    compiled_results = directory / "compiled_results_normalized.xlsx"
    heatmaps = directory / "heatmaps.xlsx"

    print("=" * 60)
    print("OpenHCS Experimental Analysis")
    print("=" * 60)
    print(f"Directory: {directory}")
    print(f"Config:    {config_file.name}")
    print(f"Results:   {results_file.name}")
    print("=" * 60)

    # Convert Opera Phenix well IDs if needed
    converted_results_file = convert_summary_well_ids(results_file)
    converted_config_file = convert_config_well_ids(config_file)

    # Import and run analysis
    try:
        from openhcs.formats.experimental_analysis import run_experimental_analysis

        print("\nRunning experimental analysis...")
        run_experimental_analysis(
            results_path=str(converted_results_file),
            config_file=str(converted_config_file),
            compiled_results_path=str(compiled_results),
            heatmap_path=str(heatmaps),
        )

        print("\n" + "=" * 60)
        print("✓ Analysis complete!")
        print("=" * 60)
        print(f"Compiled results: {compiled_results.name}")
        print(f"Heatmaps:         {heatmaps.name}")
        print("=" * 60)

    except Exception as e:
        print(f"\n✗ Error during analysis: {e}")
        import traceback

        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
