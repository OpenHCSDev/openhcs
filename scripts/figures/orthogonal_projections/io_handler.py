"""
File I/O operations for loading and saving projections.

This module provides functions to:
- Load Z-stacks from files
- Build projection filenames using FilenameParser API
- Save projections to disk

Invariants:
- I/O is isolated - can be mocked, replaced, or parallelized
- All outputs are tracked via immutable records
- Functions are idempotent (same inputs → same outputs/files)
- Naming delegated to FilenameParser API - no custom naming logic
"""

from dataclasses import dataclass
from pathlib import Path
from typing import Tuple

import numpy as np
import tifffile

from .discovery import WellChannelKey


@dataclass(frozen=True)
class ProjectionOutput:
    """Immutable record of saved projection."""

    projection_type: str
    output_path: Path
    well_id: str
    channel_id: str


def load_z_stack(file_paths: Tuple[Path, ...]) -> np.ndarray:
    """
    Load multiple Z-slice files into a 3D stack.

    Args:
        file_paths: Ordered tuple of paths (Z-order preserved)

    Returns:
        3D NumPy array of shape (Z, Y, X)

    Raises:
        FileNotFoundError: If any file is missing
    """
    if not file_paths:
        raise ValueError("No file paths provided")

    stacks = []
    for path in file_paths:
        path = Path(path)
        if not path.exists():
            raise FileNotFoundError(f"File not found: {path}")

        img = tifffile.imread(str(path))

        if img.ndim == 2:
            stacks.append(img)
        elif img.ndim == 3:
            for z in range(img.shape[0]):
                stacks.append(img[z])
        else:
            raise ValueError(f"Unexpected image dimensions: {img.ndim}")

    if not stacks:
        raise ValueError("No valid images loaded")

    stack = np.stack(stacks, axis=0)
    stack = np.flip(stack, axis=0)
    return stack


def build_projection_filename(
    well_key: WellChannelKey, projection_type: str, extension: str = ".tiff"
) -> str:
    """
    Build output filename using well/channel info.

    Args:
        well_key: WellChannelKey with well_id and channel_id
        projection_type: "xy", "xz", or "yz"
        extension: File extension

    Returns:
        Filename string like "r01c06_ch1_XY_max.tiff"
    """
    proj_upper = projection_type.upper()
    filename = f"{well_key.well_id}_ch{well_key.channel_id}_{proj_upper}_max{extension}"
    return filename


def save_projection(
    projection: np.ndarray,
    projection_type: str,
    well_key: WellChannelKey,
    output_dir: Path,
    output_format: str = "tiff",
) -> ProjectionOutput:
    """
    Save a single projection to disk.

    Args:
        projection: 2D NumPy array
        projection_type: "xy", "xz", or "yz"
        well_key: WellChannelKey for naming
        output_dir: Directory to save to
        output_format: File format ("tiff", "png")

    Returns:
        ProjectionOutput record
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    extension = (
        f".{output_format}" if not output_format.startswith(".") else output_format
    )
    filename = build_projection_filename(well_key, projection_type, extension)
    output_path = output_dir / filename

    if output_format.lower() in ("tiff", "tif"):
        tifffile.imwrite(str(output_path), projection)
    else:
        from PIL import Image

        img = Image.fromarray(projection)
        img.save(str(output_path))

    return ProjectionOutput(
        projection_type=projection_type,
        output_path=output_path,
        well_id=well_key.well_id,
        channel_id=well_key.channel_id,
    )


def save_all_projections(
    projections: dict,
    well_key: WellChannelKey,
    output_dir: Path,
    output_format: str = "tiff",
) -> Tuple[ProjectionOutput, ...]:
    """
    Save all projections for a well/channel.

    Args:
        projections: Dict {"xy": arr, "xz": arr, "yz": arr}
        well_key: WellChannelKey for naming
        output_dir: Directory to save to
        output_format: File format

    Returns:
        Tuple of ProjectionOutput records
    """
    outputs = []
    for proj_type, proj_data in projections.items():
        output = save_projection(
            proj_data, proj_type, well_key, output_dir, output_format
        )
        outputs.append(output)

    return tuple(outputs)
