# Napari Plugins

This directory contains custom napari plugins for extended functionality beyond the core OpenHCS napari integration.

## Plugins

### `napari_orthogonal_projections.py`

A napari plugin for creating orthogonal projections and exporting layers with advanced features.

**Features:**

- **Orthogonal Projections**: Create XZ, YZ, and XY max-intensity projections from 3D image stacks
  - XZ: Side view (project along Y axis)
  - YZ: Side view (project along X axis)
  - XY: Top-down view (project along Z axis)

- **Z-Scaling**: Adjust Z dimension scaling in projections to match physical spacing

- **Layer Export**: Export napari layers to various formats:
  - TIFF (preserves data quality)
  - PNG/JPG (web-friendly formats)
  - Optional dtype conversion (uint8, uint16, float32, float64)
  - Apply layer scaling for proper aspect ratios

- **Multi-channel Composites**: Create RGB composite images by merging multiple channels
  - Automatic channel grouping (detects _ch1, _ch2, _channel_1 patterns)
  - Respects individual channel colormaps and opacity
  - Additive blending for realistic visualization

**Dependencies:**
```
napari
magicgui
numpy
scipy
scikit-image
tifffile
```

**Installation:**

1. **As a napari plugin** (recommended):
   ```bash
   # Create plugin directory if needed
   mkdir -p ~/.config/napari/plugins

   # Copy plugin
   cp scripts/napari-plugins/napari_orthogonal_projections.py ~/.config/napari/plugins/

   # Restart napari - widgets will appear in Plugins menu
   napari
   ```

2. **As a standalone script**:
   ```bash
   # Run after opening napari with data
   python scripts/napari-plugins/napari_orthogonal_projections.py
   ```

**Usage:**

Once installed as a plugin, two widgets will appear in napari's Plugins menu:

1. **Ortho Projections Widget**:
   - Select which projections to create (XZ, YZ, XY)
   - Set Z scaling factor (e.g., 5.0 for typical microscopy data)
   - Toggle Z axis flipping

2. **Export Layers Widget**:
   - Choose output directory
   - Select file format (TIFF, PNG, JPG)
   - Choose dtype conversion
   - Toggle scaling application
   - Option to create multi-channel composites
   - Option to export only projection layers

**Workflow Example:**

```python
import napari
import numpy as np

# Create a 3D image stack
stack = np.random.rand(50, 512, 512)

# Open napari
viewer = napari.Viewer()
viewer.add_image(stack, name='sample_stack', scale=(0.5, 1.0, 1.0))

# Use the plugin:
# 1. Click "Plugins > Ortho Projections"
# 2. Enable XZ and YZ projections
# 3. Set Z scale to match your data (e.g., 5.0)
# 4. Click "Create Orthogonal Projections"
# 5. Use "Plugins > Export Layers" to save results
```

**Key Functions:**

- `create_projection()`: Create max projection along specified axis
- `process_layer()`: Process a single napari layer to create projection
- `export_layer()`: Export a layer to file with optional scaling/dtype conversion
- `export_composite()`: Create and export RGB composite of multiple channels
- `group_layers_by_base_name()`: Auto-group layers for compositing

**Integration with OpenHCS:**

This plugin is particularly useful with OpenHCS napari streaming:

1. Use OpenHCS napari visualizer to stream real-time data
2. Apply orthogonal projections to analyze 3D structure from different angles
3. Export projections with proper scaling for publication or analysis

**Tips:**

- Z-scale should match the physical Z-spacing ratio (e.g., if Z-steps are 5x larger than XY pixels)
- Use TIFF for maximum quality, PNG/JPG for smaller files
- Enable "Create Composites" for multi-channel data to visualize all channels together
- "Projections Only" filter is useful when you have many layers but only want to export projections
