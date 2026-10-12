"""Reference outputs of CellProfiler plugins, computed by the plugins themselves.

Run with the pinned native CellProfiler interpreter, never the OpenHCS one:

    nice -n 19 <repo>/.venv-cellprofiler39/bin/python -I \
        tests/fixtures/cellprofiler_plugins/make_reference.py \
        <directory holding histogramequalization.py, distancetransform.py, histogrammatching.py> \
        <CellProfiler-plugins commit hash> \
        tests/fixtures/cellprofiler_plugins

CellProfiler's own pipeline loader reads ``cases.cppipe`` (so the plugins parse
their own settings), then each module's ``run`` is called on a workspace whose
images are the arrays below. No image is read from or written to disk and Java
is not started. The script writes ``reference.npz`` (inputs and the pixels each
plugin stored) and ``reference.json`` (versions, voxel spacing, and the cases
in which the plugin itself raised).
"""

import json
import sys
from pathlib import Path

import numpy

VOXEL_SPACING_ZYX = (5.0, 2.0, 2.0)


def input_images():
    random = numpy.random.RandomState(20261012)
    rows, columns = numpy.mgrid[0:24, 0:32]
    plane = 0.15 + 0.5 * numpy.exp(-((rows - 9) ** 2 + (columns - 12) ** 2) / 40.0)
    plane = plane + 0.1 * columns / 31.0 + 0.08 * random.rand(24, 32)
    reference_plane = random.beta(2.0, 5.0, size=(20, 28))
    planes, volume_rows, volume_columns = numpy.mgrid[0:4, 0:20, 0:24]
    volume = 0.1 + 0.12 * planes
    volume = volume + 0.3 * numpy.exp(
        -((volume_rows - 8) ** 2 + (volume_columns - 14) ** 2) / 30.0
    )
    volume = volume + 0.1 * random.rand(4, 20, 24)
    mask_plane = numpy.zeros((24, 32))
    mask_plane[4:20, 6:26] = 1.0
    mask_plane[10:14, 10:14] = 0.5
    mask_volume = numpy.zeros((4, 20, 24))
    mask_volume[1:4, 3:17, 5:20] = 1.0
    binary_plane = numpy.zeros((24, 32), dtype=bool)
    binary_plane[3:15, 4:18] = True
    binary_plane[16:22, 20:30] = True
    binary_plane[8, 9] = False
    binary_volume = numpy.zeros((4, 20, 24), dtype=bool)
    binary_volume[0:4, 4:16, 5:19] = True
    binary_volume[2, 9, 11] = False
    return {
        "Plane": plane.astype(numpy.float32),
        "ReferencePlane": reference_plane.astype(numpy.float32),
        "MaskPlane": mask_plane.astype(numpy.float32),
        "Volume": volume.astype(numpy.float32),
        "MaskVolume": mask_volume.astype(numpy.float32),
        "BinaryPlane": binary_plane,
        "BinaryVolume": binary_volume,
    }


def main(plugin_directory, plugin_commit, fixture_directory):
    import cellprofiler
    import scipy
    import skimage
    from cellprofiler_core.image import Image, ImageSetList
    from cellprofiler_core.measurement import Measurements
    from cellprofiler_core.object import ObjectSet
    from cellprofiler_core.pipeline import Pipeline
    from cellprofiler_core.preferences import set_headless, set_plugin_directory
    from cellprofiler_core.utilities.core.modules import fill_modules
    from cellprofiler_core.workspace import Workspace

    set_headless()
    set_plugin_directory(plugin_directory, globally=False)
    fill_modules()
    fixture_directory = Path(fixture_directory)
    pipeline = Pipeline()
    pipeline.load(str(fixture_directory / "cases.cppipe"))
    inputs = input_images()
    outputs = {}
    failures = {}
    for module in pipeline.modules():
        image_set_list = ImageSetList()
        image_set = image_set_list.get_image_set(0)
        for name, pixels in inputs.items():
            image_set.add(
                name,
                Image(
                    pixels,
                    dimensions=pixels.ndim,
                    spacing=VOXEL_SPACING_ZYX if pixels.ndim == 3 else None,
                ),
            )
        measurements = Measurements()
        workspace = Workspace(
            pipeline, module, image_set, ObjectSet(), measurements, image_set_list
        )
        output_name = module.y_name.value
        try:
            module.run(workspace)
            outputs[output_name] = image_set.get_image(output_name).pixel_data
        except Exception as error:  # noqa: BLE001 - whatever the plugin raises is the record
            failures[output_name] = f"{type(error).__name__}: {error}"
        finally:
            measurements.close()
    numpy.savez_compressed(
        str(fixture_directory / "reference.npz"),
        **{"input_" + name: pixels for name, pixels in inputs.items()},
        **{"output_" + name: pixels for name, pixels in outputs.items()},
    )
    (fixture_directory / "reference.json").write_text(
        json.dumps(
            {
                "cellprofiler_plugins_commit": plugin_commit,
                "cellprofiler": cellprofiler.__version__,
                "scikit-image": skimage.__version__,
                "scipy": scipy.__version__,
                "numpy": numpy.__version__,
                "python": sys.version.split()[0],
                "voxel_spacing_zyx_of_volumes": VOXEL_SPACING_ZYX,
                "plugin_raised": failures,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )


if __name__ == "__main__":
    main(*sys.argv[1:])
