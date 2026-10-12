"""Reference outputs of CellProfiler plugins, computed by the plugins themselves.

Run with the pinned native CellProfiler interpreter, never the OpenHCS one:

    nice -n 19 <repo>/.venv-cellprofiler39/bin/python -I \
        tests/fixtures/cellprofiler_plugins/make_reference.py \
        <directory holding a copy of each plugin file named below> \
        <CellProfiler-plugins commit hash> \
        tests/fixtures/cellprofiler_plugins

Plugin files (CellProfiler-plugins ``active_plugins/`` unless a path is given):
histogramequalization.py, distancetransform.py, histogrammatching.py,
callbarcodes.py, compensatecolors.py, declumpobjects.py, and
measurementtemplate.py: an unchanged copy of
``unmaintained_plugins/CellProfiler4_autoconverted/measureradialentropy.py``.
CellProfiler 4.2.8.1 does not load that file under its own name ("Could not
find cellprofiler_core.module.Module class"), because its class is called
``MeasurementTemplate`` and CellProfiler takes the class named like the file.
Under the name ``measurementtemplate.py`` it loads and registers as
``MeasureRadialEntropy``.

CellProfiler's own pipeline loader reads ``cases.cppipe`` (so the plugins parse
their own settings), then each module's ``run`` is called on a workspace holding
the images, objects and measurements below. No image is read from or written to
disk and Java is not started. A block's first note is its case name. The script
writes ``reference.npz`` (the inputs, and every image, object set and measurement
each plugin added to its workspace) and ``reference.json`` (versions, voxel
spacing, and the cases in which the plugin itself raised).

Keys of ``reference.npz``: ``input/image/<name>``, ``input/objects/<name>``,
``input/measurement/<object>/<feature>``, and per case
``<case>/image/<name>``, ``<case>/objects/<name>``,
``<case>/measurement/<object>/<feature>``.
"""

import json
import sys
from pathlib import Path

import numpy

VOXEL_SPACING_ZYX = (5.0, 2.0, 2.0)
BARCODE_CYCLES = 3
BARCODE_BASES = "ACGT"


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
        **sequencing_cycle_images(),
    }


def sequencing_cycle_images():
    """Two sequencing cycles, each imaged in the channels of bases A and C.

    Ten spots, the first six on the foci. A spot is bright in its base's channel
    and bleeds into the other one; the C channel is the dimmer of the two.
    """
    random = numpy.random.RandomState(20261015)
    rows, columns = numpy.mgrid[0:24, 0:32]
    centres = (
        (2.5, 4),
        (2.5, 13),
        (9.5, 21),
        (15.5, 7),
        (18.5, 27),
        (21.5, 16),
        (6, 27),
        (12, 3),
        (13, 14),
        (20, 21),
    )
    images = {}
    for cycle, bases in ((1, "AACCACACCA"), (2, "CAACCAACAC")):
        signal = {"A": numpy.zeros((24, 32)), "C": numpy.zeros((24, 32))}
        for (row, column), base in zip(centres, bases):
            signal[base] += (0.35 + 0.4 * random.rand()) * numpy.exp(
                -((rows - row) ** 2 + (columns - column) ** 2) / 3.0
            )
        channels = {
            "A": signal["A"] + 0.2 * signal["C"],
            "C": 0.8 * signal["C"] + 0.4 * signal["A"],
        }
        for base, pixels in channels.items():
            background = 0.02 + 0.01 * columns / 31.0 + 0.03 * random.rand(24, 32)
            images["Cycle%02d_%s" % (cycle, base)] = (pixels + background).astype(
                numpy.float32
            )
    return images


def input_objects():
    foci = numpy.zeros((24, 32), dtype=numpy.int32)
    for label, (row, column) in enumerate(
        ((2, 3), (2, 12), (9, 20), (15, 6), (18, 26), (21, 15)), start=1
    ):
        foci[row : row + 2, column : column + 3] = label
    # Two cells that leave only a border of the image uncovered.
    cells = numpy.zeros((24, 32), dtype=numpy.int32)
    cells[1:23, 1:16] = 1
    cells[1:23, 16:31] = 2
    # The second cell under the number 3, so that no object has the number 2.
    cells_numbered_with_gap = numpy.where(cells == 2, 3, cells)
    return {
        "Foci": foci,
        "NoFoci": numpy.zeros((24, 32), dtype=numpy.int32),
        "Cells": cells,
        "CellsNumberedWithGap": cells_numbered_with_gap,
        **clumped_objects(),
    }


def clumped_objects():
    """Objects made of overlapping discs, for the modules that split them.

    In the plane: object 1 is two discs, object 2 three, object 3 one small
    disc, and objects 4 and 5 are the two halves of one rectangle, so they touch.
    In the volume: object 1 is two overlapping columns through all four planes
    and object 2 a small column in the two middle planes.
    """
    rows, columns = numpy.mgrid[0:24, 0:32]
    clumps = numpy.zeros((24, 32), dtype=numpy.int32)
    for label, row, column, radius in (
        (1, 6, 6, 4.5),
        (1, 6, 13, 4.5),
        (2, 17, 5, 3.6),
        (2, 17, 11, 3.6),
        (2, 18, 17, 3.6),
        (3, 4, 27, 2.0),
    ):
        clumps[(rows - row) ** 2 + (columns - column) ** 2 < radius**2] = label
    clumps[10:21, 22:26] = 4
    clumps[10:21, 26:31] = 5
    volume_rows, volume_columns = numpy.mgrid[0:20, 0:24]
    clump_volume = numpy.zeros((4, 20, 24), dtype=numpy.int32)
    for row, column in ((7, 6), (7, 13)):
        column_of_discs = (volume_rows - row) ** 2 + (volume_columns - column) ** 2
        clump_volume[:, column_of_discs < 4.5**2] = 1
    clump_volume[1:3, (volume_rows - 15) ** 2 + (volume_columns - 19) ** 2 < 9] = 2
    return {"Clumps": clumps, "ClumpVolume": clump_volume}


def input_measurements(objects):
    """Per-object values keyed by (object name, feature name).

    Each focus has one intensity per sequencing cycle and base: 1.0 for the base
    of its barcode, at most 0.375 for the others. Focus 4 has two equal maxima
    (C and T) in cycle 2 and focus 5 has no signal in cycle 3. A fourth cycle is
    measured that the cases, which call three, must leave out. The mean
    intensities are a second measurement family, used by the cases that call a
    base from several measurements.
    """
    random = numpy.random.RandomState(20261013)
    barcodes = ("ACGT", "TTAC", "GATG", "GCAA", "TAAC", "CCAT")
    assert len(barcodes) == int(objects["Foci"].max())
    measurements = {}
    for cycle in range(1, BARCODE_CYCLES + 2):
        for base in BARCODE_BASES:
            values = random.randint(0, 4, size=len(barcodes)) / 8.0
            for focus, barcode in enumerate(barcodes):
                if barcode[cycle - 1] == base:
                    values[focus] = 1.0
            if cycle == 2 and base in "CT":
                values[3] = 1.5
            if cycle == 3:
                values[4] = 0.0
            feature = "Intensity_MaxIntensity_CorrCycle%02d_%s" % (cycle, base)
            measurements["Foci", feature] = values
            measurements["NoFoci", feature] = numpy.zeros(0)
        measurements["Foci", "Intensity_MeanIntensity_CorrCycle%02d_A" % cycle] = (
            numpy.arange(len(barcodes)) == cycle
        ) * 0.75
    return measurements


def measurement_values(measurements, object_names):
    return {
        (object_name, feature): numpy.asarray(
            measurements.get_current_measurement(object_name, feature)
        )
        for object_name in object_names
        for feature in measurements.get_feature_names(object_name)
    }


def main(plugin_directory, plugin_commit, fixture_directory):
    import cellprofiler
    import scipy
    import skimage
    from cellprofiler_core.image import Image, ImageSetList
    from cellprofiler_core.measurement import Measurements
    from cellprofiler_core.object import Objects, ObjectSet
    from cellprofiler_core.pipeline import Pipeline
    from cellprofiler_core.preferences import (
        set_default_image_directory,
        set_headless,
        set_plugin_directory,
    )
    from cellprofiler_core.utilities.core.modules import fill_modules
    from cellprofiler_core.workspace import Workspace

    set_headless()
    set_plugin_directory(plugin_directory, globally=False)
    fill_modules()
    fixture_directory = Path(fixture_directory)
    # Files a block names (the barcode library) sit beside the pipeline.
    set_default_image_directory(str(fixture_directory))
    pipeline = Pipeline()
    pipeline.load(str(fixture_directory / "cases.cppipe"))
    images = input_images()
    objects = input_objects()
    object_measurements = input_measurements(objects)
    stored = {}
    for name, pixels in images.items():
        stored["input/image/" + name] = pixels
    for name, labels in objects.items():
        stored["input/objects/" + name] = labels
    for (object_name, feature), values in object_measurements.items():
        stored["input/measurement/%s/%s" % (object_name, feature)] = values
    failures = {}
    for module in pipeline.modules():
        (case,) = module.notes
        image_set_list = ImageSetList()
        image_set = image_set_list.get_image_set(0)
        for name, pixels in images.items():
            image_set.add(
                name,
                Image(
                    pixels,
                    dimensions=pixels.ndim,
                    spacing=VOXEL_SPACING_ZYX if pixels.ndim == 3 else None,
                ),
            )
        object_set = ObjectSet()
        measurements = Measurements()
        for name, labels in objects.items():
            one_object_set = Objects()
            one_object_set.segmented = labels
            object_set.add_objects(one_object_set, name)
            measurements.add_measurement("Image", "Count_" + name, int(labels.max()))
        for (object_name, feature), values in object_measurements.items():
            measurements.add_measurement(object_name, feature, values)
        measured_before = measurement_values(
            measurements, measurements.get_object_names()
        )
        workspace = Workspace(
            pipeline, module, image_set, object_set, measurements, image_set_list
        )
        try:
            module.run(workspace)
        except Exception as error:  # noqa: BLE001 - whatever the plugin raises is the record
            failures[case] = f"{type(error).__name__}: {error}"
        else:
            for name in image_set.names:
                if name not in images:
                    stored[f"{case}/image/{name}"] = image_set.get_image(
                        name
                    ).pixel_data
            for name in object_set.get_object_names():
                if name not in objects:
                    stored[f"{case}/objects/{name}"] = object_set.get_objects(
                        name
                    ).segmented
            measured = measurement_values(
                measurements, measurements.get_object_names()
            )
            for (object_name, feature), values in measured.items():
                if (object_name, feature) not in measured_before:
                    stored[f"{case}/measurement/{object_name}/{feature}"] = values
        finally:
            measurements.close()
    numpy.savez_compressed(str(fixture_directory / "reference.npz"), **stored)
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
