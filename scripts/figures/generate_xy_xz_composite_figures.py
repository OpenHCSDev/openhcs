#!/usr/bin/env python3
"""
Generate composite figures showing XY, XZ, and YZ max projections.

For each well, creates a figure with:
- Left panel: XY max projection composite (full height)
- Right top: XZ max projection composite
- Right bottom: YZ max projection composite

Usage:
    python scripts/figures/generate_xy_xz_composite_figures.py \
        --input-dir /path/to/max_project \
        --output-dir /path/to/output
"""

import argparse
import csv
import logging
from dataclasses import dataclass
from pathlib import Path
import re
from typing import Dict, Iterable, Optional, List, Tuple, Union

import matplotlib

matplotlib.use("Agg")  # Use non-interactive backend
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import numpy as np
from PIL import Image
import tifffile

# Set up logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class ColumnGroupSpec:
    name: str
    count: int
    mode: str


@dataclass(frozen=True)
class MosaicTile:
    well_id: str
    row: int
    col: int
    path: Path


@dataclass(frozen=True)
class FigureConfig:
    filename_pattern: re.Pattern
    well_pattern: re.Pattern
    required_projections: Tuple[str, ...]
    input_extensions: Tuple[str, ...]
    output_format: str
    output_suffix: str
    output_well_format: str
    figure_size: Tuple[int, int]
    dpi: int
    title_format: str
    panel_titles: Dict[str, str]
    metadata_well_column: str
    metadata_label_column: str
    column_group_specs: Tuple[ColumnGroupSpec, ...]
    time_label_prefix: str
    mosaic_background: Tuple[int, int, int, int]


DEFAULT_CONFIG = FigureConfig(
    filename_pattern=re.compile(
        r"source_images_timepoint_(\d+)_site_(\d+)_well_(R\d+C\d+)_(XY|XZ|YZ)_max_composite",
        re.IGNORECASE,
    ),
    well_pattern=re.compile(r"R(\d+)C(\d+)", re.IGNORECASE),
    required_projections=("XY", "XZ", "YZ"),
    input_extensions=(".tif", ".tiff", ".png", ".jpg", ".jpeg"),
    output_format="png",
    output_suffix="composite_figure",
    output_well_format="rnc",
    figure_size=(16, 9),
    dpi=150,
    title_format="Well {well_display}",
    panel_titles={
        "XY": "XY Max Projection",
        "XZ": "XZ Max Projection",
        "YZ": "YZ Max Projection",
    },
    metadata_well_column="well",
    metadata_label_column="label",
    column_group_specs=(
        ColumnGroupSpec(name="HA-OXIME", count=5, mode="first"),
        ColumnGroupSpec(name="matrigel", count=3, mode="last"),
    ),
    time_label_prefix="Time",
    mosaic_background=(0, 0, 0, 255),
)


def parse_filename(filename: str, config: FigureConfig) -> Optional[Dict[str, str]]:
    """Parse filename to extract well metadata."""
    match = config.filename_pattern.search(filename)

    if not match:
        return None

    return {
        "timepoint": match.group(1),
        "site": match.group(2),
        "well": match.group(3).upper(),
        "projection": match.group(4).upper(),
    }


def load_image(image_path: Path) -> Union[Image.Image, np.ndarray]:
    """Load an image from disk."""
    suffix = image_path.suffix.lower()
    if suffix in (".tif", ".tiff"):
        data = tifffile.imread(image_path)
        if data.ndim == 3 and data.shape[0] in (3, 4) and data.shape[-1] not in (3, 4):
            data = np.moveaxis(data, 0, -1)
        return data
    return Image.open(image_path)


def build_title(
    metadata: Dict[str, str], label: Optional[str], config: FigureConfig
) -> str:
    """Build the figure title with optional label."""
    metadata_display = dict(metadata)
    metadata_display["well_display"] = format_well_id(metadata["well"], config)
    base = config.title_format.format(**metadata_display)
    if label:
        return f"{base} - {label}"
    return base


def parse_well_position(
    well_id: str, config: FigureConfig
) -> Optional[Tuple[int, int]]:
    """Parse well ID into (row, col)."""
    match = config.well_pattern.search(well_id)
    if not match:
        return None
    return int(match.group(1)), int(match.group(2))


def index_to_letters(index: int) -> str:
    """Convert zero-based index to Excel-style letters (A, B, ..., AA)."""
    index += 1
    letters = ""
    while index > 0:
        index, remainder = divmod(index - 1, 26)
        letters = chr(ord("A") + remainder) + letters
    return letters


def row_number_to_letters(row_number: int) -> str:
    """Convert 1-based row number to letters (1 -> A)."""
    if row_number < 1:
        return ""
    return index_to_letters(row_number - 1)


def letters_to_row_number(letters: str) -> int:
    """Convert row letters to 1-based row number (A -> 1)."""
    value = 0
    for char in letters.upper():
        if not "A" <= char <= "Z":
            return 0
        value = value * 26 + (ord(char) - ord("A") + 1)
    return value


def normalize_well_id(well_id: str, config: FigureConfig) -> str:
    """Normalize well ID to R##C## format when possible."""
    cleaned = well_id.strip().upper()
    if config.well_pattern.search(cleaned):
        return cleaned

    match = re.match(r"^([A-Z]+)(\d+)$", cleaned)
    if not match:
        return cleaned

    row_letters = match.group(1)
    col_number = int(match.group(2))
    row_number = letters_to_row_number(row_letters)
    if row_number == 0:
        return cleaned

    return f"R{row_number:02d}C{col_number:02d}"


def format_well_id(well_id: str, config: FigureConfig) -> str:
    """Format well ID as R##C## or A01 style."""
    if config.output_well_format == "rnc":
        return well_id
    position = parse_well_position(well_id, config)
    if not position:
        return well_id
    row_letters = row_number_to_letters(position[0])
    return f"{row_letters}{position[1]:02d}"


def slugify_label(label: str) -> str:
    """Convert a label into a filename-friendly slug."""
    slug = re.sub(r"[^A-Za-z0-9_-]+", "_", label.strip())
    return slug.strip("_")


def build_column_group_map(columns: List[int], config: FigureConfig) -> Dict[int, str]:
    """Assign labels to columns based on group specs."""
    column_labels: Dict[int, str] = {}
    remaining = sorted(columns)

    for spec in config.column_group_specs:
        if not remaining:
            break

        if spec.mode == "first":
            group_columns = remaining[: spec.count]
            remaining = remaining[spec.count :]
        elif spec.mode == "last":
            group_columns = remaining[-spec.count :]
            remaining = remaining[: -spec.count]
        else:
            logger.warning(f"Unknown column group mode: {spec.mode}")
            continue

        for index, column in enumerate(group_columns):
            time_label = index_to_letters(index)
            column_labels[column] = (
                f"{spec.name} {config.time_label_prefix} {time_label}"
            )

    return column_labels


def build_column_labels(wells: Dict[str, dict], config: FigureConfig) -> Dict[str, str]:
    """Create well -> label mapping from column grouping rules."""
    columns = []
    for payload in wells.values():
        well_id = payload["metadata"]["well"]
        position = parse_well_position(well_id, config)
        if position:
            columns.append(position[1])

    column_map = build_column_group_map(sorted(set(columns)), config)
    well_labels: Dict[str, str] = {}
    for payload in wells.values():
        well_id = payload["metadata"]["well"]
        position = parse_well_position(well_id, config)
        if not position:
            continue
        label = column_map.get(position[1])
        if label:
            well_labels[well_id] = label

    return well_labels


def create_composite_figure(
    xy_path: Path,
    xz_path: Path,
    yz_path: Path,
    output_path: Path,
    metadata: Dict[str, str],
    label: Optional[str],
    config: FigureConfig,
) -> None:
    """Create a figure with XY, XZ, and YZ projections in a 2-column layout."""
    xy_img = load_image(xy_path)
    xz_img = load_image(xz_path)
    yz_img = load_image(yz_path)

    fig = plt.figure(figsize=config.figure_size)
    grid = GridSpec(2, 2, figure=fig, width_ratios=[1, 1], height_ratios=[1, 1])

    ax_xy = fig.add_subplot(grid[:, 0])
    ax_xz = fig.add_subplot(grid[0, 1])
    ax_yz = fig.add_subplot(grid[1, 1])

    ax_xy.imshow(xy_img)
    ax_xy.set_title(config.panel_titles.get("XY", "XY"), fontsize=14, weight="bold")
    ax_xy.axis("off")

    ax_xz.imshow(xz_img)
    ax_xz.set_title(config.panel_titles.get("XZ", "XZ"), fontsize=14, weight="bold")
    ax_xz.axis("off")

    ax_yz.imshow(yz_img)
    ax_yz.set_title(config.panel_titles.get("YZ", "YZ"), fontsize=14, weight="bold")
    ax_yz.axis("off")

    fig.suptitle(build_title(metadata, label, config), fontsize=16, weight="bold")

    plt.tight_layout()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_path, bbox_inches="tight", dpi=config.dpi)
    plt.close(fig)


def discover_images(input_dir: Path, config: FigureConfig) -> Iterable[Path]:
    """Find all candidate composite images in the input directory."""
    for ext in config.input_extensions:
        yield from input_dir.glob(f"*{ext}")


def build_well_key(metadata: Dict[str, str]) -> str:
    """Create a stable key for grouping by well/site/timepoint."""
    return (
        f"{metadata['well']}_site_{metadata['site']}_timepoint_{metadata['timepoint']}"
    )


def group_by_well(images: Iterable[Path], config: FigureConfig) -> Dict[str, dict]:
    """Group projection images by well and projection type."""
    wells: Dict[str, dict] = {}
    for img_path in images:
        metadata = parse_filename(img_path.name, config)
        if not metadata:
            logger.warning(f"Could not parse filename: {img_path.name}")
            continue

        well_key = build_well_key(metadata)
        wells.setdefault(well_key, {"metadata": metadata, "projections": {}})
        wells[well_key]["projections"][metadata["projection"]] = img_path

    return wells


def filter_complete_wells(
    wells: Dict[str, dict], config: FigureConfig
) -> Dict[str, dict]:
    """Filter wells that have all required projections."""
    complete = {}
    for well_key, payload in wells.items():
        projections = payload["projections"]
        missing = [p for p in config.required_projections if p not in projections]
        if missing:
            logger.warning(f"Missing projection for {well_key}: {missing}")
            continue
        complete[well_key] = payload
    return complete


def read_metadata_mapping(
    metadata_csv: Optional[Path], config: FigureConfig
) -> Dict[str, str]:
    """Read a mapping of well -> label from a CSV file."""
    if not metadata_csv:
        return {}

    if not metadata_csv.exists():
        logger.error(f"Metadata CSV not found: {metadata_csv}")
        return {}

    mapping: Dict[str, str] = {}
    with metadata_csv.open("r", newline="") as csvfile:
        reader = csv.DictReader(csvfile)
        if not reader.fieldnames:
            logger.error(f"Metadata CSV has no header: {metadata_csv}")
            return {}

        for row in reader:
            well = row.get(config.metadata_well_column)
            label = row.get(config.metadata_label_column)
            if not well or not label:
                continue
            normalized = normalize_well_id(well, config)
            mapping[normalized] = label.strip()

    return mapping


def build_output_path(
    output_dir: Path,
    metadata: Dict[str, str],
    label: Optional[str],
    config: FigureConfig,
) -> Path:
    """Build output filepath for a well figure."""
    well_display = format_well_id(metadata["well"], config)
    stem_parts = []
    if label:
        label_slug = slugify_label(label)
        if label_slug:
            stem_parts.append(label_slug)
    stem_parts.append(
        f"{well_display}_site_{metadata['site']}_timepoint_{metadata['timepoint']}"
    )
    stem_parts.append(config.output_suffix)
    filename = "_".join(stem_parts) + f".{config.output_format}"
    return output_dir / filename


def normalize_mosaic_output(output_path: Path, config: FigureConfig) -> Path:
    """Ensure mosaic output path has a file extension."""
    if output_path.exists() and output_path.is_dir():
        return output_path / f"mosaic.{config.output_format}"
    if output_path.suffix:
        return output_path
    return output_path.with_suffix(f".{config.output_format}")


def create_mosaic(
    tiles: List[MosaicTile], output_path: Path, config: FigureConfig
) -> None:
    """Create a tiled mosaic image aligned by well position."""
    if not tiles:
        logger.warning("No tiles available for mosaic")
        return

    rows = sorted({tile.row for tile in tiles})
    cols = sorted({tile.col for tile in tiles})
    row_index = {row: idx for idx, row in enumerate(rows)}
    col_index = {col: idx for idx, col in enumerate(cols)}

    images: Dict[Tuple[int, int], Image.Image] = {}
    max_width = 0
    max_height = 0
    for tile in tiles:
        image = Image.open(tile.path).convert("RGBA")
        images[(tile.row, tile.col)] = image
        max_width = max(max_width, image.width)
        max_height = max(max_height, image.height)

    canvas = Image.new(
        "RGBA",
        (max_width * len(cols), max_height * len(rows)),
        config.mosaic_background,
    )

    used_positions = set()
    for tile in tiles:
        key = (tile.row, tile.col)
        if key in used_positions:
            logger.warning(
                "Duplicate tile position for row %s col %s; skipping %s",
                tile.row,
                tile.col,
                tile.path.name,
            )
            continue
        used_positions.add(key)

        image = images[key]
        x = col_index[tile.col] * max_width + (max_width - image.width) // 2
        y = row_index[tile.row] * max_height + (max_height - image.height) // 2
        canvas.alpha_composite(image, (x, y))

    output_path = normalize_mosaic_output(output_path, config)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    canvas.save(output_path)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Generate composite figures with XY, XZ, and YZ max projections"
    )
    parser.add_argument(
        "--input-dir",
        type=Path,
        required=True,
        help="Directory containing XY/XZ/YZ max projection composite images",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Directory to save output figures",
    )
    parser.add_argument(
        "--output-format",
        type=str,
        default=DEFAULT_CONFIG.output_format,
        choices=("png", "tif", "tiff"),
        help="Output image format",
    )
    parser.add_argument(
        "--well-format",
        type=str,
        default=DEFAULT_CONFIG.output_well_format,
        choices=("rnc", "a01"),
        help="Well notation for titles/filenames (rnc or a01)",
    )
    parser.add_argument(
        "--metadata-csv",
        type=Path,
        default=None,
        help="Optional CSV mapping well -> label",
    )
    parser.add_argument(
        "--metadata-well-column",
        type=str,
        default=DEFAULT_CONFIG.metadata_well_column,
        help="Column name for well IDs in metadata CSV",
    )
    parser.add_argument(
        "--metadata-label-column",
        type=str,
        default=DEFAULT_CONFIG.metadata_label_column,
        help="Column name for labels in metadata CSV",
    )
    parser.add_argument(
        "--disable-column-labels",
        action="store_true",
        help="Disable automatic column-based labels",
    )
    parser.add_argument(
        "--mosaic-output",
        type=Path,
        default=None,
        help="Optional output path for tiled mosaic image",
    )

    args = parser.parse_args()

    if not args.input_dir.exists():
        logger.error(f"Input directory not found: {args.input_dir}")
        return

    config = FigureConfig(
        filename_pattern=DEFAULT_CONFIG.filename_pattern,
        well_pattern=DEFAULT_CONFIG.well_pattern,
        required_projections=DEFAULT_CONFIG.required_projections,
        input_extensions=DEFAULT_CONFIG.input_extensions,
        output_format=args.output_format,
        output_suffix=DEFAULT_CONFIG.output_suffix,
        output_well_format=args.well_format,
        figure_size=DEFAULT_CONFIG.figure_size,
        dpi=DEFAULT_CONFIG.dpi,
        title_format=DEFAULT_CONFIG.title_format,
        panel_titles=DEFAULT_CONFIG.panel_titles,
        metadata_well_column=args.metadata_well_column,
        metadata_label_column=args.metadata_label_column,
        column_group_specs=DEFAULT_CONFIG.column_group_specs,
        time_label_prefix=DEFAULT_CONFIG.time_label_prefix,
        mosaic_background=DEFAULT_CONFIG.mosaic_background,
    )

    composite_images = list(discover_images(args.input_dir, config))
    logger.info(f"Found {len(composite_images)} composite images")

    wells = group_by_well(composite_images, config)
    logger.info(f"Grouped into {len(wells)} wells")

    complete_wells = filter_complete_wells(wells, config)
    logger.info(f"Found {len(complete_wells)} wells with all projections")

    label_mapping = read_metadata_mapping(args.metadata_csv, config)
    column_label_mapping = {}
    if not args.disable_column_labels:
        column_label_mapping = build_column_labels(complete_wells, config)

    created = 0
    tiles: List[MosaicTile] = []
    for well_key, payload in sorted(complete_wells.items()):
        projections = payload["projections"]
        metadata = payload["metadata"]
        title_label = label_mapping.get(metadata["well"]) or column_label_mapping.get(
            metadata["well"]
        )
        filename_label = column_label_mapping.get(
            metadata["well"]
        ) or label_mapping.get(metadata["well"])

        output_path = build_output_path(
            args.output_dir, metadata, filename_label, config
        )

        create_composite_figure(
            projections["XY"],
            projections["XZ"],
            projections["YZ"],
            output_path,
            metadata,
            title_label,
            config,
        )

        position = parse_well_position(metadata["well"], config)
        if args.mosaic_output and position:
            tiles.append(
                MosaicTile(
                    well_id=metadata["well"],
                    row=position[0],
                    col=position[1],
                    path=output_path,
                )
            )

        created += 1
        logger.info(f"✓ Created: {output_path.name}")

    if args.mosaic_output:
        create_mosaic(tiles, args.mosaic_output, config)
        mosaic_path = normalize_mosaic_output(args.mosaic_output, config)
        logger.info(f"✓ Created mosaic: {mosaic_path.name}")

    logger.info(f"\n✅ Generated {created} composite figures in {args.output_dir}")


if __name__ == "__main__":
    main()
