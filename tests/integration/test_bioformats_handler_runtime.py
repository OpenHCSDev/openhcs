from pathlib import Path

import numpy as np

from openhcs.constants.constants import Backend
from openhcs.core.source_binding_selection import SourceFileUniverse
from openhcs.microscopes.bioformats import BioFormatsHandler
from tests.unit.bioformats_fixture import (
    bioformats_filemanager,
    write_bioformats_manifest_fixture,
)


def test_bioformats_handler_loads_selected_planes_through_runtime_path(
    tmp_path: Path,
) -> None:
    stack = write_bioformats_manifest_fixture(tmp_path)
    filemanager = bioformats_filemanager()
    handler = BioFormatsHandler(filemanager)
    handler.initialize_workspace(tmp_path, filemanager)

    SourceFileUniverse(
        (str(tmp_path / "A01_s001_w1_z001_t001.tif"),), Backend.VIRTUAL_WORKSPACE,
    ).load_images(filemanager)

    loaded = filemanager.load_batch(
        [str(tmp_path / "A01_s001_w1_z001_t001.tif")],
        Backend.MEMORY.value,
    )
    np.testing.assert_array_equal(loaded[0].data, stack[0, 0, 0])
    assert loaded[0].metadata.source_path.endswith("A01_s001_w1_z001_t001.tif")
