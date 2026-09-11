# Complex CellProfiler workflow imports

Derived from the source pipelines and current importer. Counts of function
calls describe configured invocations, not parallel workers or measured runtime.
These checks import and reload Python documents; they do not execute analyses.

## Advanced segmentation

23 enabled modules of 23 total; 16 imported steps; 59 function calls.

[Source pipeline](../../benchmark/native_refs/official30_scoped_rows/CellProfiler_tutorials_cp_tutorial_advanced_segmentation_final_wells_include_first1/native_cellprofiler_headless/BBBC022_Analysis_Final.cppipe) | [Editable Python](cp_tutorial_advanced_segmentation_final_imported.py)

The archived row `cp_tutorial_advanced_segmentation_final` records one passing output-comparison observation.
Function identities and parameters passed the current generated-Python reload check.

| Step | Imported step | Function | Calls |
| -------- | ---------------------------------- | ------------------------------------------------ | --------: |
| 1 | CorrectIlluminationApply | `correct_illumination_apply` | 5 |
| 2 | IdentifyPrimaryObjects | `identify_primary_objects` | 1 |
| 3 | IdentifySecondaryObjects | `identify_secondary_objects` | 1 |
| 4 | IdentifyTertiaryObjects | `identify_tertiary_objects` | 1 |
| 5 | EnhanceOrSuppressFeatures | `enhance_or_suppress_features` | 1 |
| 6 | MaskImage | `mask_image` | 1 |
| 7 | IdentifyPrimaryObjects | `identify_primary_objects` | 1 |
| 8 | MaskImage | `mask_image` | 1 |
| 9 | IdentifyPrimaryObjects | `identify_primary_objects` | 1 |
| 10 | MeasureColocalization | `measure_colocalization_objects` | 5 |
| 11 | MeasureObjectIntensity | `measure_object_intensity` | 15 |
| 12 | MeasureObjectIntensityDistribution | `measure_object_intensity_distribution` | 15 |
| 13 | MeasureObjectSizeShape | `measure_object_size_shape` | 5 |
| 14 | MeasureObjectNeighbors | `measure_object_neighbors` | 3 |
| 15 | RelateObjects | `relate_objects_with_saved_children` | 2 |
| 16 | ExportToDatabase | `export_to_database` | 1 |

## 3D monolayer

35 enabled modules of 37 total; 31 imported steps; 35 function calls.

[Source pipeline](../../benchmark/native_refs/official30_scoped_rows/CellProfiler_tutorials_cp_tutorial_3d_monolayer_wells_include_first1/native_cellprofiler_headless/3d_monolayer_final.cppipe) | [Editable Python](cp_tutorial_3d_monolayer_imported.py)

The archived row `cp_tutorial_3d_monolayer` records one passing output-comparison observation.
Function identities and parameters passed the current generated-Python reload check.

| Step | Imported step | Function | Calls |
| -------- | ---------------------------------- | ------------------------------------------------ | --------: |
| 1 | RescaleIntensity | `rescale_intensity` | 1 |
| 2 | Resize | `resize_volumetric` | 1 |
| 3 | MedianFilter | `medianfilter` | 1 |
| 4 | Threshold | `threshold` | 1 |
| 5 | RemoveHoles | `remove_holes_3d` | 1 |
| 6 | Watershed | `watershed_cellprofiler4` | 1 |
| 7 | ResizeObjects | `resize_objects_3d` | 1 |
| 8 | ErodeObjects | `erode_objects` | 1 |
| 9 | ResizeObjects | `resize_objects_3d` | 1 |
| 10 | ConvertObjectsToImage | `convert_objects_to_image` | 1 |
| 11 | Threshold | `threshold` | 1 |
| 12 | ImageMath | `image_math` | 1 |
| 13 | RemoveHoles | `remove_holes_3d` | 1 |
| 14 | ImageMath | `image_math` | 1 |
| 15 | Resize | `resize_volumetric` | 1 |
| 16 | Closing | `closing` | 1 |
| 17 | Resize | `resize_volumetric` | 1 |
| 18 | Threshold | `threshold` | 1 |
| 19 | MaskImage | `mask_image` | 1 |
| 20 | ErodeImage | `erode_image` | 1 |
| 21 | Watershed | `watershed_cellprofiler4` | 1 |
| 22 | MeasureObjectIntensity | `measure_object_intensity` | 4 |
| 23 | MeasureObjectSizeShape | `measure_object_size_shape` | 2 |
| 24 | OverlayObjects | `overlay_objects` | 1 |
| 25 | RescaleIntensity | `rescale_intensity` | 1 |
| 26 | OverlayObjects | `overlay_objects` | 1 |
| 27 | ConvertObjectsToImage | `convert_objects_to_image` | 1 |
| 28 | SaveImages | `save_images` | 1 |
| 29 | ConvertObjectsToImage | `convert_objects_to_image` | 1 |
| 30 | SaveImages | `save_images` | 1 |
| 31 | ExportToSpreadsheet | `export_to_spreadsheet` | 1 |
