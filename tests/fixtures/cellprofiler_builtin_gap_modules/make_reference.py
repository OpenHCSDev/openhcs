"""Files CellProfiler's own SaveCroppedObjects writes for ``cases.cppipe``.

Run with the pinned native CellProfiler interpreter, never the OpenHCS one:

    nice -n 19 <repo>/.venv-cellprofiler39/bin/python -I \
        tests/fixtures/cellprofiler_builtin_gap_modules/make_reference.py \
        tests/fixtures/cellprofiler_builtin_gap_modules <empty scratch directory>

CellProfiler's pipeline loader reads ``cases.cppipe`` (so the module parses its
own settings). Each module's ``run`` is called on a workspace holding the arrays
below, with a fresh default output folder per module. Java is not started. The
script writes ``reference.npz`` (the inputs, and the pixels read back from every
file a module wrote, keyed ``file_<module_num>/<path below the output folder>``)
and ``reference.json`` (versions, the source file name given to the modules, and
each module's file list or the error it raised).
"""

import json
import sys
from pathlib import Path

import numpy

SOURCE_FILE_NAME = "plate1_A01_s1_w1.tif"


def inputs():
    random = numpy.random.RandomState(20261012)
    rows, columns = numpy.mgrid[0:24, 0:32]
    plane = 0.1 + 0.6 * numpy.exp(-((rows - 9) ** 2 + (columns - 12) ** 2) / 40.0)
    plane = plane + 0.1 * columns / 31.0 + 0.15 * random.rand(24, 32)
    dna = random.beta(2.0, 5.0, size=(24, 32))
    color = random.rand(24, 32, 3)
    volume = random.rand(4, 20, 24)
    cells = numpy.zeros((24, 32), dtype=numpy.int32)
    cells[0:6, 0:9] = 1  # touches the image corner
    cells[8:16, 10:20] = 2
    cells[10:13, 13:17] = 0  # a hole: the crop keeps the bounding box
    cells[18:22, 4:8] = 5  # object numbers skip 3 and 4
    cells[19:23, 24:30] = 5  # the same object in two pieces
    cells[15:20, 21:24] = 7
    cells[17, 22] = 0
    blobs = numpy.zeros((4, 20, 24), dtype=numpy.int32)
    blobs[0:3, 2:9, 3:11] = 1
    blobs[1:4, 11:18, 12:22] = 3
    blobs[2, 13, 15] = 0
    return {
        "ImageAfterMath": plane.astype(numpy.float32),
        "DNA": dna.astype(numpy.float32),
        "Color": color.astype(numpy.float32),
        "Volume": volume.astype(numpy.float32),
        "Cells": cells,
        "Blobs": blobs,
    }


def main(fixture_directory, scratch_directory):
    import cellprofiler
    import skimage
    import skimage.io
    import tifffile
    from cellprofiler_core.image import Image, ImageSetList
    from cellprofiler_core.measurement import Measurements
    from cellprofiler_core.object import Objects, ObjectSet
    from cellprofiler_core.pipeline import Pipeline
    from cellprofiler_core.preferences import (
        set_default_output_directory,
        set_headless,
    )
    from cellprofiler_core.workspace import Workspace

    set_headless()
    fixture_directory = Path(fixture_directory)
    scratch_directory = Path(scratch_directory)
    pipeline = Pipeline()
    pipeline.load(str(fixture_directory / "cases.cppipe"))
    arrays = inputs()
    object_names = ("Cells", "Blobs")
    files = {}
    listing = {}
    for module in pipeline.modules():
        output_directory = scratch_directory / str(module.module_num)
        output_directory.mkdir(parents=True)
        set_default_output_directory(str(output_directory))
        image_set_list = ImageSetList()
        image_set = image_set_list.get_image_set(0)
        for name, pixels in arrays.items():
            if name in object_names:
                continue
            volumetric = name == "Volume"
            image_set.add(name, Image(pixels, dimensions=3 if volumetric else 2))
        object_set = ObjectSet()
        for name in object_names:
            objects = Objects()
            objects.segmented = arrays[name]
            object_set.add_objects(objects, name)
        measurements = Measurements()
        measurements.add_image_measurement("FileName_DNA", SOURCE_FILE_NAME)
        workspace = Workspace(
            pipeline, module, image_set, object_set, measurements, image_set_list
        )
        try:
            module.run(workspace)
        except Exception as error:  # noqa: BLE001 - whatever the module raises is the record
            listing[str(module.module_num)] = f"{type(error).__name__}: {error}"
            continue
        finally:
            measurements.close()
        written = sorted(
            path.relative_to(output_directory).as_posix()
            for path in output_directory.rglob("*")
            if path.is_file()
        )
        listing[str(module.module_num)] = written
        for relative in written:
            path = output_directory / relative
            pixels = (
                tifffile.imread(str(path))
                if path.suffix == ".tiff"
                else skimage.io.imread(str(path))
            )
            files[f"file_{module.module_num}/{relative}"] = pixels
    numpy.savez_compressed(
        str(fixture_directory / "reference.npz"),
        **{"input_" + name: pixels for name, pixels in arrays.items()},
        **files,
    )
    (fixture_directory / "reference.json").write_text(
        json.dumps(
            {
                "cellprofiler": cellprofiler.__version__,
                "scikit-image": skimage.__version__,
                "tifffile": tifffile.__version__,
                "numpy": numpy.__version__,
                "python": sys.version.split()[0],
                "source_file_name": SOURCE_FILE_NAME,
                "files_written": listing,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    with open(str(scratch_directory / "native_dump.cppipe"), "w") as dump:
        pipeline.dump(dump)


if __name__ == "__main__":
    main(*sys.argv[1:])
