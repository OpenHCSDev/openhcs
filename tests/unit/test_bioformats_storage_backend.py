import json
from pathlib import Path

import numpy as np
from polystore.base import ImageSamplingRequest, ImageSamplingResult
from polystore.bioformats_storage import BioFormatsPlaneRef, BioFormatsStorageBackend

from openhcs.constants.constants import Backend
from openhcs.core.runtime_image_values import image_payload_data
from openhcs.core.viewer_streaming_service import ViewerStreamingSource
from openhcs.microscopes.bioformats import BioFormatsHandler
from tests.unit.bioformats_fixture import (
    bioformats_filemanager,
    write_bioformats_manifest_fixture,
)


def test_virtual_workspace_lists_and_loads_disk_fixture_refs(tmp_path: Path) -> None:
    stack = write_bioformats_manifest_fixture(tmp_path)
    filemanager = bioformats_filemanager()
    BioFormatsHandler(filemanager).initialize_workspace(tmp_path, filemanager)
    backend = filemanager.registry[Backend.VIRTUAL_WORKSPACE.value]

    files = backend.list_files(tmp_path, extensions={".tif"})
    loaded = backend.load(tmp_path / "A01_s001_w2_z001_t001.tif")
    sampled = backend.sample(
        tmp_path / "A01_s001_w2_z001_t001.tif",
        ImageSamplingRequest(origin_yx=(1, 1), shape_yx=(2, 2)),
    )

    assert sorted(Path(path).name for path in files) == [
        "A01_s001_w1_z001_t001.tif",
        "A01_s001_w2_z001_t001.tif",
    ]
    np.testing.assert_array_equal(loaded, stack[0, 0, 1])
    np.testing.assert_array_equal(sampled.data, stack[0, 0, 1, 1:3, 1:3])
    np.testing.assert_array_equal(sampled.statistics_data, stack[0, 0, 1])
    assert sampled.source_shape == stack[0, 0, 1].shape


def test_viewer_streams_exact_bioformats_plane_address(
    monkeypatch,
    tmp_path: Path,
) -> None:
    write_bioformats_manifest_fixture(tmp_path)
    manifest_path = tmp_path / "bioformats_spw.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["images"][0]["source_path"] = "plate.fake"
    manifest["images"][0]["reader"] = "bioformats"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    (tmp_path / "plate.fake").write_bytes(b"")
    observed: list[tuple[Path, int, int]] = []

    def load_plane(*, source_path, series_index, plane_index):
        observed.append((Path(source_path), series_index, plane_index))
        return np.full((3, 4), plane_index + 11, dtype=np.uint16)

    monkeypatch.setattr(
        "polystore.bioformats_java.load_bioformats_plane", load_plane
    )
    filemanager = bioformats_filemanager()
    handler = BioFormatsHandler(filemanager)
    handler.initialize_workspace(tmp_path, filemanager)
    source = ViewerStreamingSource(
        plate_path=str(tmp_path),
        filemanager=filemanager,
        microscope_handler=handler,
    )
    projection = source.source_workspace_projection()
    filename = "A01_s001_w2_z001_t001.tif"
    components = source.image_component_metadata_by_path([filename], projection)

    image = source.load_image(
        filename,
        Backend.VIRTUAL_WORKSPACE.value,
        source_projection=projection,
        component_metadata=components[filename],
    )

    np.testing.assert_array_equal(image_payload_data(image), np.full((3, 4), 12))
    assert observed == [(tmp_path / "plate.fake", 0, 1)]


def test_bioformats_plane_ref_has_canonical_address_round_trip(tmp_path: Path) -> None:
    ref = BioFormatsPlaneRef(tmp_path / "plate.fake", 3, 7)

    assert BioFormatsPlaneRef.from_backend_address(ref.to_backend_address()) == ref
    assert ref.to_backend_address() == (
        '{"plane_index":7,"series_index":3,'
        f'"source_path":"{tmp_path / "plate.fake"}"}}'
    )
    assert (
        BioFormatsStorageBackend().source_path(
            ref.to_backend_address(),
            base_path=tmp_path / "workspace",
        )
        == tmp_path / "plate.fake"
    )


def test_bioformats_backend_dispatches_java_reader(monkeypatch, tmp_path: Path) -> None:
    def fake_load_bioformats_plane(*, source_path, series_index, plane_index):
        assert source_path == tmp_path / "plate.fake"
        assert series_index == 3
        assert plane_index == 7
        return np.array([[42]], dtype=np.uint16)

    monkeypatch.setattr(
        "polystore.bioformats_java.load_bioformats_plane",
        fake_load_bioformats_plane,
    )

    backend = BioFormatsStorageBackend()
    address = BioFormatsPlaneRef(
        source_path=tmp_path / "plate.fake",
        series_index=3,
        plane_index=7,
    ).to_backend_address()

    np.testing.assert_array_equal(
        backend.load(address),
        np.array([[42]], dtype=np.uint16),
    )


def test_bioformats_backend_dispatches_typed_sampling_request(
    monkeypatch,
    tmp_path: Path,
) -> None:
    request = ImageSamplingRequest(
        origin_yx=(3, 4),
        shape_yx=(5, 6),
        resolution_index=2,
    )
    expected = ImageSamplingResult(
        data=np.array([[42]], dtype=np.uint16),
        statistics_data=np.array([[42]], dtype=np.uint16),
        source_shape=(100, 80),
        resolution_shape=(25, 20),
        sample_origin_yx=(3, 4),
        selected_resolution_index=2,
        resolution_count=3,
        downsample_yx=(4.0, 4.0),
    )

    def fake_sample_bioformats_plane(
        *, source_path, series_index, plane_index, request: ImageSamplingRequest
    ):
        assert source_path == tmp_path / "plate.fake"
        assert series_index == 3
        assert plane_index == 7
        assert request is sample_request
        return expected

    sample_request = request
    monkeypatch.setattr(
        "polystore.bioformats_java.sample_bioformats_plane",
        fake_sample_bioformats_plane,
    )
    address = BioFormatsPlaneRef(
        source_path=tmp_path / "plate.fake",
        series_index=3,
        plane_index=7,
    ).to_backend_address()

    sampled = BioFormatsStorageBackend().sample(address, request)

    assert sampled is expected
