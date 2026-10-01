"""Selected image declarations must materialize with their exact source identity."""

from pathlib import Path

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.napari_stream import NapariStreamingBackend

from openhcs.core.callable_contract import CallableContract
from openhcs.core.projected_image_output import SelectedPlaneImageOutput
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_metadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_runtime import ImageFunctionOutputContextStrategy
from openhcs.processing.backends.analysis.neurite_outgrowth import neurite_outgrowth_metaxpress
from openhcs.processing.materialization import materialize

from test_function_artifact_materialization import _context
from test_materialization_core import _viewer_stream_backend_kwargs


def _source_stack(axis, component="channel"):
    spacing = SourceVoxelSpacing((1.3556, 1.3556))
    coordinates = tuple(
        {"well": "A01", "site": "1", "channel": "7", "z_index": "1", "timepoint": "1", component: str(index)}
        for index in (1, 2)
    )
    metadata = ImagePayloadMetadata(
        plane_axis=axis,
        source_voxel_spacing=spacing,
        source_image_names=("DAPI", "FITC"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/input/A01_s001_w{index}_z001_t001.tif" for index in (1, 2)),
            component_metadata=coordinates,
        ),
    )
    return metadata.payload_with(np.arange(112, dtype=np.uint16).reshape(2, 7, 8))


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_public_selected_checkpoint_materializes_and_streams_without_storage_axes(
    axis, tmp_path, monkeypatch,
):
    source = _source_stack(axis)
    pixels = np.arange(56, dtype=np.uint16).reshape(1, 7, 8)
    selected = SelectedPlaneImageOutput(pixels, (1,))
    payload = ImageFunctionOutputContextStrategy().contextualize(
        source, selected, None,
        RuntimePlaneAxisValueProjection.preserve(axis=axis, axis_size=2),
    )
    spec = next(
        spec for spec in CallableContract.from_callable(neurite_outgrowth_metaxpress).artifact_outputs
        if spec.name == "neurite_candidate_mask"
    )
    viewer = NapariStreamingBackend()
    filemanager = FileManager({"disk": DiskStorageBackend(), "napari_stream": viewer})
    saved_streams = []
    save_batch = filemanager.save_batch

    def capture_stream(data_list, paths, backend, **kwargs):
        if backend == "napari_stream":
            saved_streams.append((tuple(data_list), tuple(paths), kwargs["stream_request"]))
            return
        return save_batch(data_list, paths, backend, **kwargs)

    monkeypatch.setattr(filemanager, "save_batch", capture_stream)
    try:
        result = materialize(
            spec.materialization, payload, str(tmp_path / "checkpoint.tif"),
            filemanager, ["disk", "napari_stream"],
            {"napari_stream": _viewer_stream_backend_kwargs()},
            context=_context(filemanager), variable_components=(),
        )
        assert Path(result).is_file()
        np.testing.assert_array_equal(np.asarray(filemanager.load(result, "disk")).reshape(-1), pixels.reshape(-1))
        assert len(saved_streams) == 1
        (data,), (path,), request = saved_streams[0]
        assert path == result
        np.testing.assert_array_equal(np.asarray(data).reshape(-1), pixels.reshape(-1))
        assert request.source.metadata.component_metadata_for_item(path, 0)["channel"] == 2
        assert image_payload_metadata(payload).source_image_names == ("FITC",)
        assert image_payload_metadata(payload).source_path == "/input/A01_s001_w2_z001_t001.tif"
        assert image_payload_metadata(payload).source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))
    finally:
        viewer.cleanup()
