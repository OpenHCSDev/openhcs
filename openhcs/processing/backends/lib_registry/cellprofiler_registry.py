"""
CellProfiler Library Registry Implementation

Absorbs cellprofiler-library-nightly functions into the unified registry.
The runtime testing system automatically classifies processing contracts
for all discoverable image processing functions.

Scans cellprofiler_library.functions submodules directly (not the modules
layer, which requires the full cellprofiler-core package).
"""
from __future__ import annotations

import importlib
import logging
import numpy as np
from typing import Any, Tuple, List

from openhcs.constants import MemoryType
from openhcs.core.utils import optional_import
from .unified_registry import LibraryRegistryBase, RuntimeTestingRegistryBase

logger = logging.getLogger(__name__)

cellprofiler_library = optional_import("cellprofiler_library")

# Submodules under cellprofiler_library.functions to scan.
# object_processing is excluded: requires cellprofiler-core (not standalone).
_FUNCTION_MODULES = [
    "cellprofiler_library.functions.image_processing",
    "cellprofiler_library.functions.segmentation",
    "cellprofiler_library.functions.measurement",
    "cellprofiler_library.functions.file_processing",
]

# CellProfiler first-parameter names that indicate image/array input
_IMAGE_PARAM_NAMES = {
    "image", "pixel_data", "im_pixel_data", "input_image",
    "orig_image_pixels", "image_pixels", "data", "output_pixels",
    "cropped_pixel_data", "labels", "label_image", "mask",
    "ground_truth", "test_img",
}


class CellProfilerRegistry(RuntimeTestingRegistryBase):
    """CellProfiler library registry with automatic contract classification."""

    _registry_name = "cellprofiler"

    # Exclusions: common + cellprofiler-specific non-image functions
    EXCLUSIONS = LibraryRegistryBase.COMMON_EXCLUSIONS | {
        # Utility functions that don't take images as first arg
        "get_structuring_element",
        "get_rectangle_cropping",
        "get_ellipse_cropping",
        "get_cropped_mask",
        "get_cropped_image_mask",
        # Segmentation format converters (not image processing)
        "cast_labels_to_label_set",
        "convert_dense_to_label_set",
        "convert_dense_to_sparse",
        "convert_ijv_to_label_set",
        "convert_ijv_to_sparse",
        "convert_label_set_to_ijv",
        "convert_labels_to_dense",
        "convert_labels_to_ijv",
        "convert_sparse_to_dense",
        "convert_sparse_to_ijv",
        "dense_shape_from_sparse",
        "find_ijv_overlaps",
        "find_label_overlaps",
        "indices_from_dense",
        "indices_from_ijv",
        "indices_from_labels",
        "areas_from_ijv",
        "count_from_ijv",
        "center_of_labels_mass",
        # Measurement helpers (not image→image)
        "get_kmeans_points",
        "get_labels_mask",
        "get_skeleton_points",
        "get_weights",
        "compute_earth_movers_distance",
        "compute_rand_index",
    }

    MODULES_TO_SCAN = []  # Handled by get_modules_to_scan override
    MEMORY_TYPE = MemoryType.NUMPY.value
    FLOAT_DTYPE = np.float32

    def __init__(self):
        super().__init__("cellprofiler")

    # ===== ESSENTIAL ABC METHODS =====
    def get_library_version(self) -> str:
        if cellprofiler_library and hasattr(cellprofiler_library, "__version__"):
            return cellprofiler_library.__version__
        try:
            from importlib.metadata import version
            return version("cellprofiler-library-nightly")
        except Exception:
            return "unknown"

    def is_library_available(self) -> bool:
        return bool(cellprofiler_library)

    def get_library_object(self):
        return cellprofiler_library

    def get_module_patterns(self) -> List[str]:
        return ["cellprofiler_library", "cellprofiler"]

    def get_display_name(self) -> str:
        return "CellProfiler"

    # ===== MODULE SCANNING OVERRIDE =====
    def get_modules_to_scan(self) -> List[Tuple[str, Any]]:
        """Import function submodules directly (bypasses broken modules layer)."""
        modules = []
        for mod_path in _FUNCTION_MODULES:
            try:
                mod = importlib.import_module(mod_path)
                short_name = mod_path.rsplit(".", 1)[-1]
                modules.append((short_name, mod))
            except ImportError as e:
                logger.warning(f"Skipping {mod_path}: {e}")
        return modules

    # ===== HOOK IMPLEMENTATIONS =====
    def _create_array(self, shape: Tuple[int, ...], dtype):
        return np.random.rand(*shape).astype(dtype)

    def _check_first_parameter(self, first_param, func_name: str) -> bool:
        return first_param.name.lower() in _IMAGE_PARAM_NAMES

    def _preprocess_input(self, image, func_name: str):
        return image

    def _postprocess_output(self, result, original_image, func_name: str):
        return result

    # ===== LIBRARY-SPECIFIC IMPLEMENTATIONS =====
    def _generate_function_name(self, name: str, module_name: str) -> str:
        return f"{module_name}.{name}"

    def _stack_2d_results(self, func, test_3d):
        return np.stack([func(test_3d[z]) for z in range(test_3d.shape[0])])

    def _arrays_close(self, arr1, arr2):
        return np.allclose(arr1, arr2, rtol=1e-5, atol=1e-8)

