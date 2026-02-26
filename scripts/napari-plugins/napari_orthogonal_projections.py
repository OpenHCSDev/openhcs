#!/usr/bin/env python3
"""
Napari plugin for creating orthogonal projections (XZ, YZ, XY) and exporting layers.

This plugin provides GUI widgets for:
1. Creating max-intensity projections along orthogonal axes
2. Exporting layers to TIFF/PNG/JPG with optional scaling and dtype conversion
3. Creating composite RGB images from multiple channels

Usage:
    # As a napari plugin (automatic):
    napari  # Plugin will auto-load when placed in ~/.config/napari/plugins/

    # As a standalone script:
    python napari_orthogonal_projections.py

Features:
- XZ projections: Side view (project along Y axis)
- YZ projections: Side view (project along X axis)
- XY projections: Top-down view (project along Z axis)
- Z-scaling: Adjust Z dimension scaling in projections
- Export to TIFF/PNG/JPG with dtype conversion
- Composite multi-channel images to RGB
"""

from magicgui import magicgui
import napari
import numpy as np
from typing import Literal
from pathlib import Path
import tifffile
from skimage import io
from scipy.ndimage import zoom

# ============================================================================
# Core projection functions
# ============================================================================


def create_projection(data: np.ndarray, axis: int, flip_z: bool = True) -> np.ndarray:
    """
    Create a max projection along a specified axis.

    Parameters
    ----------
    data : np.ndarray
        3D array with shape (Z, Y, X)
    axis : int
        Axis along which to project (1=Y, 2=X, 0=Z)
    flip_z : bool
        Whether to flip Z axis in result

    Returns
    -------
    np.ndarray
        2D max projection
    """
    projection = data.max(axis=axis)

    # Flip Z axis if it's first dimension in result
    if flip_z and axis != 0:
        projection = np.flip(projection, axis=0)

    return projection


def get_projection_scale(
    original_scale: tuple, axis: int, z_scale_factor: float = 1.0
) -> tuple:
    """
    Calculate scale for projection based on which axis was projected.

    Parameters
    ----------
    original_scale : tuple
        Original (Z, Y, X) scale
    axis : int
        Axis that was projected out
    z_scale_factor : float
        Additional scaling factor for Z dimension

    Returns
    -------
    tuple
        Scale for 2D projection
    """
    if len(original_scale) != 3:
        return None

    # Apply Z scaling factor
    scales = list(original_scale)
    scales[0] = scales[0] * z_scale_factor

    # Remove projected axis from scale
    scales.pop(axis)
    return tuple(scales)


def add_projection_layer(
    viewer: napari.Viewer,
    data: np.ndarray,
    name: str,
    source_layer: napari.layers.Image,
    scale: tuple = None,
) -> napari.layers.Image:
    """
    Add a projection as a new image layer.

    Parameters
    ----------
    viewer : napari.Viewer
    data : np.ndarray
        Projection data
    name : str
        Layer name
    source_layer : napari.layers.Image
        Original layer to copy properties from
    scale : tuple, optional
        Scale for projection

    Returns
    -------
    napari.layers.Image
        The created layer
    """
    return viewer.add_image(
        data,
        name=name,
        colormap=source_layer.colormap.name,
        contrast_limits=source_layer.contrast_limits,
        scale=scale,
        blending=source_layer.blending,
        opacity=source_layer.opacity,
    )


# ============================================================================
# Layer processing
# ============================================================================


def process_layer(
    viewer: napari.Viewer,
    layer: napari.layers.Image,
    projection_type: Literal["XZ", "YZ", "XY"],
    flip_z: bool = True,
    z_scale_factor: float = 1.0,
) -> napari.layers.Image:
    """
    Create a single projection for a layer.

    Parameters
    ----------
    viewer : napari.Viewer
    layer : napari.layers.Image
        Source layer
    projection_type : str
        One of 'XZ', 'YZ', 'XY'
    flip_z : bool
        Whether to flip Z axis
    z_scale_factor : float
        Scaling factor for Z dimension

    Returns
    -------
    napari.layers.Image
        Created projection layer
    """
    data = layer.data

    # Map projection type to axis
    axis_map = {
        "XZ": 1,  # project along Y
        "YZ": 2,  # project along X
        "XY": 0,  # project along Z
    }

    axis = axis_map[projection_type]

    # Create projection
    projection = create_projection(data, axis, flip_z and projection_type != "XY")

    # Calculate scale with Z scaling factor
    scale = get_projection_scale(layer.scale, axis, z_scale_factor)

    # Add layer
    return add_projection_layer(
        viewer, projection, f"{layer.name}_{projection_type}_max", layer, scale
    )


def get_3d_layers(viewer: napari.Viewer) -> list:
    """Get all 3D image layers from viewer."""
    return [
        layer
        for layer in viewer.layers
        if hasattr(layer, "data") and layer.data.ndim == 3
    ]


# ============================================================================
# Export functions
# ============================================================================


def convert_dtype(data: np.ndarray, target_dtype: str) -> np.ndarray:
    """
    Convert data to target dtype with appropriate scaling.

    Parameters
    ----------
    data : np.ndarray
        Input data
    target_dtype : str
        Target dtype ('as_is', 'uint8', 'uint16', 'float32', 'float64')

    Returns
    -------
    np.ndarray
        Converted data
    """
    if target_dtype == "as_is":
        return data

    # Map string to numpy dtype
    dtype_map = {
        "uint8": np.uint8,
        "uint16": np.uint16,
        "float32": np.float32,
        "float64": np.float64,
    }

    target = dtype_map[target_dtype]

    # If converting to integer types, normalize and scale
    if target in [np.uint8, np.uint16]:
        data_min = data.min()
        data_max = data.max()

        if data_max > data_min:
            # Normalize to 0-1
            data_norm = (data - data_min) / (data_max - data_min)

            # Scale to target range
            if target == np.uint8:
                return (data_norm * 255).astype(np.uint8)
            elif target == np.uint16:
                return (data_norm * 65535).astype(np.uint16)
        else:
            # Constant image
            return np.zeros_like(data, dtype=target)

    # For float types, just convert
    return data.astype(target)


def export_layer(
    layer: napari.layers.Image,
    output_dir: Path,
    format: str = "tiff",
    dtype: str = "as_is",
    apply_scale: bool = True,
) -> None:
    """
    Export a single layer to file.

    Parameters
    ----------
    layer : napari.layers.Image
    output_dir : Path
        Directory to save to
    format : str
        File format ('tiff', 'png', 'jpg')
    dtype : str
        Data type conversion ('as_is', 'uint8', 'uint16', 'float32', 'float64')
    apply_scale : bool
        Apply layer scale to resample image (stretches Z if scaled)
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Sanitize filename
    safe_name = layer.name.replace("/", "_").replace("\\", "_")

    data = layer.data

    # Apply scale by resampling if requested
    if apply_scale and hasattr(layer, "scale") and layer.scale is not None:
        scale = layer.scale
        if len(scale) == data.ndim and not all(s == 1.0 for s in scale):
            # Resample with zoom
            print(f"Resampling {layer.name} with scale {scale}")
            data = zoom(data, scale, order=1)  # order=1 is bilinear interpolation

    # Convert dtype if requested
    data = convert_dtype(data, dtype)

    if format == "tiff":
        filepath = output_dir / f"{safe_name}.tif"
        tifffile.imwrite(filepath, data)
    elif format in ["png", "jpg"]:
        # PNG/JPG require uint8
        if data.dtype != np.uint8:
            data = convert_dtype(data, "uint8")
        filepath = output_dir / f"{safe_name}.{format}"
        io.imsave(filepath, data)

    print(f"Saved: {filepath} (dtype: {data.dtype}, shape: {data.shape})")


def apply_colormap_to_data(
    data: np.ndarray, colormap, contrast_limits: tuple = None
) -> np.ndarray:
    """
    Apply a colormap to grayscale data to create RGB.

    Parameters
    ----------
    data : np.ndarray
        Grayscale image data
    colormap : napari.utils.Colormap
        Napari colormap object
    contrast_limits : tuple, optional
        (min, max) for contrast adjustment

    Returns
    -------
    np.ndarray
        RGB image with shape (..., 3)
    """
    # Normalize data
    if contrast_limits is not None:
        vmin, vmax = contrast_limits
    else:
        vmin, vmax = data.min(), data.max()

    if vmax > vmin:
        data_norm = np.clip((data - vmin) / (vmax - vmin), 0, 1)
    else:
        data_norm = np.zeros_like(data, dtype=float)

    # Use napari's colormap.map() method for proper interpolation
    rgb = colormap.map(data_norm.ravel())[:, :3]  # Get RGB, drop alpha
    rgb = rgb.reshape(data.shape + (3,))

    return rgb


def group_layers_by_base_name(layers: list) -> dict:
    """
    Group layers by their base name (removing channel identifiers).

    Parameters
    ----------
    layers : list
        List of napari layers

    Returns
    -------
    dict
        Dictionary mapping base names to lists of layers
    """
    import re

    groups = {}

    for layer in layers:
        # Try to extract base name by removing channel identifiers
        # Patterns: _channel_1, _channel_2, _ch1, _ch2, _c1, _c2, etc.
        name = layer.name

        # Remove common channel patterns
        base_name = re.sub(r"_channel_\d+", "", name)
        base_name = re.sub(r"_ch\d+", "", base_name)
        base_name = re.sub(r"_c\d+", "", base_name)

        if base_name not in groups:
            groups[base_name] = []
        groups[base_name].append(layer)

    # Only return groups with multiple channels
    return {k: v for k, v in groups.items() if len(v) > 1}


def composite_channels(layers: list) -> np.ndarray:
    """
    Composite multiple channel layers into a single RGB image.

    Parameters
    ----------
    layers : list
        List of layers to composite (should have same shape)

    Returns
    -------
    np.ndarray
        Composited RGB image
    """
    if not layers:
        return None

    # Check that all layers have the same shape
    shape = layers[0].data.shape
    for layer in layers[1:]:
        if layer.data.shape != shape:
            print(f"Warning: Shape mismatch in composite - {layer.name}")
            return None

    # Initialize RGB output
    composite = np.zeros(shape + (3,), dtype=float)

    # Add each channel with its colormap
    for layer in layers:
        rgb = apply_colormap_to_data(
            layer.data,
            layer.colormap,  # Pass colormap object, not name
            layer.contrast_limits,
        )

        # Additive blending
        composite += rgb * layer.opacity

    # Clip to valid range
    composite = np.clip(composite, 0, 1)

    return composite


def export_composite(
    layers: list,
    output_dir: Path,
    base_name: str,
    format: str = "tiff",
    dtype: str = "uint8",
    apply_scale: bool = True,
) -> None:
    """
    Export a composite of multiple channels.

    Parameters
    ----------
    layers : list
        List of channel layers to composite
    output_dir : Path
        Output directory
    base_name : str
        Base name for output file
    format : str
        Output format
    dtype : str
        Data type for export
    apply_scale : bool
        Whether to apply layer scaling
    """
    # Apply scaling to all layers if requested
    if apply_scale:
        scaled_layers = []
        for layer in layers:
            data = layer.data
            if hasattr(layer, "scale") and layer.scale is not None:
                scale = layer.scale
                if len(scale) == data.ndim and not all(s == 1.0 for s in scale):
                    data = zoom(data, scale, order=1)

            # Create temporary layer-like object with scaled data
            class ScaledLayer:
                pass

            scaled_layer = ScaledLayer()
            scaled_layer.data = data
            scaled_layer.colormap = layer.colormap
            scaled_layer.contrast_limits = layer.contrast_limits
            scaled_layer.opacity = layer.opacity
            scaled_layers.append(scaled_layer)

        layers = scaled_layers

    # Create composite
    composite = composite_channels(layers)

    if composite is None:
        print(f"Failed to create composite for {base_name}")
        return

    # Convert dtype
    if dtype == "uint8":
        data = (composite * 255).astype(np.uint8)
    elif dtype == "uint16":
        data = (composite * 65535).astype(np.uint16)
    else:
        data = composite.astype(np.float32)

    # Save
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    safe_name = base_name.replace("/", "_").replace("\\", "_")

    if format == "tiff":
        filepath = output_dir / f"{safe_name}_composite.tif"
        tifffile.imwrite(filepath, data)
    elif format in ["png", "jpg"]:
        if data.dtype != np.uint8:
            data = (composite * 255).astype(np.uint8)
        filepath = output_dir / f"{safe_name}_composite.{format}"
        io.imsave(filepath, data)

    print(f"Saved composite: {filepath} (shape: {data.shape})")


# ============================================================================
# GUI
# ============================================================================


@magicgui(
    call_button="Create Orthogonal Projections",
    z_scale={"min": 0.1, "max": 20.0, "step": 0.1},
)
def create_ortho_projections(
    viewer: napari.Viewer,
    create_xz: bool = True,
    create_yz: bool = True,
    create_xy: bool = False,
    flip_z: bool = True,
    z_scale: float = 5.0,
) -> None:
    """
    Create XZ and YZ max projections for all 3D layers.

    Parameters
    ----------
    viewer : napari.Viewer
    create_xz : bool
        Create XZ side view projection
    create_yz : bool
        Create YZ side view projection
    create_xy : bool
        Create XY top-down projection
    flip_z : bool
        Flip Z axis so index 0 is at bottom
    z_scale : float
        Z dimension scaling factor (increases Z spacing in projections)
    """

    layers = get_3d_layers(viewer)

    if not layers:
        print("No 3D layers found!")
        return

    created = 0
    for layer in layers:
        if create_xz:
            process_layer(viewer, layer, "XZ", flip_z, z_scale)
            created += 1

        if create_yz:
            process_layer(viewer, layer, "YZ", flip_z, z_scale)
            created += 1

        if create_xy:
            process_layer(viewer, layer, "XY", flip_z, z_scale)
            created += 1

    print(f"Created {created} projections from {len(layers)} layers")


@magicgui(
    call_button="Export Layers",
    output_dir={"mode": "d"},
    format={"choices": ["tiff", "png", "jpg"]},
    dtype={"choices": ["as_is", "uint8", "uint16", "float32", "float64"]},
)
def export_layers(
    viewer: napari.Viewer,
    output_dir: Path = Path.home(),
    format: str = "tiff",
    dtype: str = "as_is",
    apply_scale: bool = True,
    create_composites: bool = False,
    projections_only: bool = True,
) -> None:
    """
    Export layers to files.

    Parameters
    ----------
    viewer : napari.Viewer
    output_dir : Path
        Directory to save images
    format : str
        Image format (tiff, png, jpg)
    dtype : str
        Convert to data type (as_is keeps original, uint8/uint16 for smaller files)
    apply_scale : bool
        Resample image to match visual scaling (stretches Z dimension)
    create_composites : bool
        Create RGB composite images by merging channels
    projections_only : bool
        Only export projection layers (names containing _max)
    """

    print("\n=== Export starting ===")
    print(f"Create composites: {create_composites}")
    print(f"Projections only: {projections_only}")

    layers_to_export = []

    for layer in viewer.layers:
        if not hasattr(layer, "data"):
            continue

        if projections_only:
            if "_max" in layer.name:
                layers_to_export.append(layer)
        else:
            layers_to_export.append(layer)

    print(f"Found {len(layers_to_export)} layers to export")
    for layer in layers_to_export:
        print(f"  - {layer.name}")

    if not layers_to_export:
        print("No layers to export!")
        return

    # Export individual layers
    if not create_composites:
        print("\nExporting individual layers...")
        for layer in layers_to_export:
            try:
                export_layer(layer, output_dir, format, dtype, apply_scale)
            except Exception as e:
                print(f"ERROR: Failed to export {layer.name}: {e}")
                import traceback

                traceback.print_exc()

    # Create and export composites
    if create_composites:
        print("\nGrouping layers for composites...")
        groups = group_layers_by_base_name(layers_to_export)

        print(f"Found {len(groups)} groups:")
        for base_name, group_layers in groups.items():
            print(f"  Group '{base_name}':")
            for layer in group_layers:
                print(f"    - {layer.name}")

        if not groups:
            print("No multi-channel groups found for compositing!")
            print("Exporting individual layers instead...")
            for layer in layers_to_export:
                try:
                    export_layer(layer, output_dir, format, dtype, apply_scale)
                except Exception as e:
                    print(f"ERROR: Failed to export {layer.name}: {e}")
                    import traceback

                    traceback.print_exc()
        else:
            for base_name, group_layers in groups.items():
                try:
                    print(f"\nCreating composite for '{base_name}'...")
                    export_composite(
                        group_layers, output_dir, base_name, format, dtype, apply_scale
                    )
                except Exception as e:
                    print(f"ERROR: Failed to create composite for {base_name}: {e}")
                    import traceback

                    traceback.print_exc()

    print(f"\n=== Export complete to {output_dir} ===")


# ============================================================================
# Auto-load
# ============================================================================

if __name__ == "__main__":
    viewer = napari.current_viewer()
    viewer.window.add_dock_widget(create_ortho_projections, name="Ortho Projections")
    viewer.window.add_dock_widget(export_layers, name="Export Layers")
