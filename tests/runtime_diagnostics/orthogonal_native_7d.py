"""Answer-free native-model diagnostic; not GUI, MCP or plugin acceptance.

Run directly in an owned supported-Napari environment with the owning OpenHCS
source on PYTHONPATH. No pytest fixtures, viewer window or datasets are used.
The inputs and assertions preserve the earlier Napari 0.6.1 diagnostic.
"""

from __future__ import annotations

import importlib.metadata
import json
import sys
import time

import napari
import numpy as np
import openhcs
from napari.components import ViewerModel
from packaging.version import Version


def run_diagnostic() -> dict[str, object]:
    assert Version(napari.__version__) >= Version("0.7.1"), napari.__version__
    start = time.monotonic()
    results: list[dict[str, object]] = []
    for leading in ((2, 2, 2, 2), (1, 2, 1, 2)):
        shape = (leading[0], leading[1], 3, leading[2], leading[3], 4, 5)
        data = np.arange(np.prod(shape), dtype=np.float32).reshape(shape)
        labels = data.astype(np.uint32) + 1
        anchor = (leading[0] - 1, leading[1] - 1, 1, leading[2] - 1, leading[3] - 1, 2, 3)
        scale = (1, 1, 2.5, 1, 1, 0.8, 0.9)
        translate = (10, 20, 17, 30, 40, -2, 4)
        axes = ("site", "channel", "z_index", "timepoint", "well", "y", "x")
        viewer = ViewerModel()
        image = viewer.add_image(
            data,
            name="raw",
            rgb=False,
            scale=scale,
            translate=translate,
            axis_labels=axes,
            contrast_limits=(0, int(data.max())),
            gamma=0.75,
        )
        label = viewer.add_labels(
            labels, name="labels", scale=scale, translate=translate, axis_labels=axes
        )
        point = viewer.add_points(
            np.asarray([anchor], dtype=float),
            name="points",
            scale=scale,
            translate=translate,
            axis_labels=axes,
            size=0.2,
        )
        world = tuple(image.data_to_world(anchor))
        viewer.dims.point = world
        original = tuple(viewer.dims.point)
        for plane, pair in (("XY", (5, 6)), ("XZ", (2, 6)), ("YZ", (2, 5))):
            order = tuple(axis for axis in viewer.dims.order if axis not in pair) + pair
            viewer.dims.order = order
            viewer.dims.ndisplay = 2
            assert viewer.dims.displayed == pair
            assert tuple(viewer.dims.point) == original
            checks = 0
            for first in range(shape[pair[0]]):
                for second in range(shape[pair[1]]):
                    coordinate = list(anchor)
                    coordinate[pair[0]] = first
                    coordinate[pair[1]] = second
                    source_coordinate = tuple(coordinate)
                    world_sample = tuple(image.data_to_world(source_coordinate))
                    actual = image.get_value(
                        world_sample, world=True, dims_displayed=list(pair)
                    )
                    label_value = label.get_value(
                        world_sample, world=True, dims_displayed=list(pair)
                    )
                    assert actual == data[source_coordinate], (
                        plane, source_coordinate, actual, data[source_coordinate]
                    )
                    assert label_value == labels[source_coordinate], (
                        plane, source_coordinate, label_value, labels[source_coordinate]
                    )
                    checks += 1
            assert point.get_value(world, world=True, dims_displayed=list(pair)) == 0
            assert image.data is data
            assert label.data is labels
            assert tuple(image.scale) == scale
            assert tuple(image.translate) == translate
            assert image.gamma == 0.75
            results.append(
                {
                    "shape": shape,
                    "plane": plane,
                    "displayed": pair,
                    "order": order,
                    "image_and_label_sample_pairs": checks,
                    "point_index": 0,
                    "world_point": world,
                    "local_nonspatial_indices": {
                        axes[axis]: anchor[axis] for axis in (0, 1, 3, 4)
                    },
                }
            )
        viewer.layers.clear()
    return {
        "napari_version": napari.__version__,
        "napari_source": napari.__file__,
        "numpy_version": np.__version__,
        "numpy_source": np.__file__,
        "openhcs_source": openhcs.__file__,
        "python_executable": sys.executable,
        "python_version": sys.version,
        "installed_versions": {
            distribution.metadata["Name"]: distribution.version
            for distribution in importlib.metadata.distributions()
        },
        "results": results,
        "elapsed_seconds": time.monotonic() - start,
        "native_model_assertions_passed": True,
        "production_fix_passed": False,
        "gui_mcp_plugin_acceptance": False,
    }


if __name__ == "__main__":
    print(json.dumps(run_diagnostic(), indent=2))
