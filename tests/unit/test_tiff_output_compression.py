"""Lossless TIFF compression crosses the declared OpenHCS output boundary."""

from types import SimpleNamespace

import numpy as np
import tifffile
from polystore.disk import DiskBackend
from polystore.filemanager import FileManager

from openhcs.constants.constants import Backend
from openhcs.core.config import GlobalPipelineConfig, TiffCompression, TiffConfig
from openhcs.core.steps.function_artifact_materialization import (
    PersistentArtifactMaterializationTargetPlan,
)
from openhcs.core.steps.function_io import save_materialized_data
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    MaterializedFilenameIdentity,
    materialize,
)


def test_configured_main_flow_tiff_output_is_lossless(tmp_path) -> None:
    config = TiffConfig(compression=TiffCompression.DEFLATE, compression_level=3)
    assert GlobalPipelineConfig().tiff_config == TiffConfig()
    pixels = np.zeros((2, 256, 256), dtype=np.int32)
    pixels[0, 40:60, 80:100] = 5
    path = tmp_path / "labels.tif"
    context = SimpleNamespace(
        microscope_handler=SimpleNamespace(parser=object(), microscope_type="test"),
        tiff_config=config,
    )

    save_materialized_data(
        FileManager({Backend.DISK.value: DiskBackend()}),
        [pixels],
        [str(path)],
        Backend.DISK.value,
        None,
        context,
        "A01",
    )

    with tifffile.TiffFile(path) as output:
        assert output.pages[0].compression.value != 1
    np.testing.assert_array_equal(tifffile.imread(path), pixels)


def test_configured_named_artifact_tiff_output_is_lossless(tmp_path) -> None:
    config = TiffConfig(compression=TiffCompression.DEFLATE, compression_level=3)
    pixels = np.zeros((2, 256, 256), dtype=np.int32)
    pixels[1, 60:80, 90:110] = 11
    path = materialize(
        MaterializationSpec(
            ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
            )
        ),
        pixels,
        str(tmp_path / "artifact"),
        FileManager({Backend.DISK.value: DiskBackend()}),
        backends=[Backend.DISK.value],
        backend_kwargs=PersistentArtifactMaterializationTargetPlan(
            backend=Backend.DISK.value
        ).persistent_backend_kwargs(SimpleNamespace(tiff_config=config)),
    )

    with tifffile.TiffFile(path) as output:
        assert output.pages[0].compression.value != 1
    np.testing.assert_array_equal(tifffile.imread(path), pixels)
