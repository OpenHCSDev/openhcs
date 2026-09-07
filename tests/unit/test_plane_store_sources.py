import json
from pathlib import Path

import numpy as np
import pytest
import zarr
from objectstate.lazy_factory import ensure_global_config_context
from ome_zarr.format import Format
from polystore.base import ensure_storage_registry, storage_registry
from polystore.bioformats_java import BioFormatsJavaContext
from polystore.filemanager import FileManager
from polystore.ome_zarr_metadata import OmeZarrLocation
from polystore.ome_zarr_storage import OmeZarrStorageBackend
from polystore.zarr import ZarrStorageBackend
from polystore.zarr_batch import (
    ZarrBatchAxis,
    ZarrBatchAxisRole,
    ZarrBatchLayout,
)

from openhcs.constants.constants import AllComponents, Backend, OrchestratorState
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazySourceBindingsConfig,
    PipelineConfig,
)
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.source_bindings import (
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.steps.function_io import (
    save_materialized_data,
    update_metadata_for_zarr_conversion,
)
from openhcs.microscopes.bioformats import BioFormatsHandler
from openhcs.microscopes.bioformats_adapter import (
    OmeZarrStoreAdapter,
    SourcePlaneStoreAdapter,
)
from openhcs.microscopes.microscope_base import create_microscope_handler
from openhcs.microscopes.openhcs import OpenHCSMicroscopeHandler
from tests.ome_zarr_fixture import NGFF_FORMATS, write_ngff_plate


@pytest.mark.parametrize("fmt", NGFF_FORMATS, ids=lambda fmt: fmt.version)
def test_ngff_axis_cardinalities_and_plane_pixels_survive_discovery(
    tmp_path: Path,
    fmt: Format,
) -> None:
    pixels = np.arange(2 * 2 * 3 * 4 * 5, dtype=np.uint16).reshape(2, 2, 3, 4, 5)
    store = tmp_path / "nested" / "plate"
    write_ngff_plate(store, pixels, fmt=fmt)
    adapter = OmeZarrStoreAdapter()

    (direct,) = adapter.discover_stores(store)
    (nested,) = adapter.discover_stores(tmp_path)

    assert len(direct.candidates) == len(nested.candidates) == 12
    assert direct.identity == nested.identity
    assert direct.pixel_size == nested.pixel_size == 1.0
    expected_components = {
        AllComponents.WELL: {"A01"},
        AllComponents.SITE: {"1"},
        AllComponents.CHANNEL: {"1", "2"},
        AllComponents.Z_INDEX: {"1", "2", "3"},
        AllComponents.TIMEPOINT: {"1", "2"},
    }
    for component, expected in expected_components.items():
        assert {
            candidate.declared_address.value_for(component)
            for candidate in nested.candidates
        } == expected
    assert {
        candidate.component_labels[AllComponents.CHANNEL.value]
        for candidate in nested.candidates
    } == {"NGFF", "NGFF-2"}
    backend = OmeZarrStorageBackend()
    for candidate in nested.candidates:
        assert candidate.source_axis_shape == (2, 2, 3)
        address = candidate.declared_address
        expected_indices = tuple(
            int(address.value_for(component)) - 1
            for component in (
                AllComponents.TIMEPOINT,
                AllComponents.CHANNEL,
                AllComponents.Z_INDEX,
            )
        )
        assert candidate.source_ref.source_axis_indices == expected_indices
        loaded = backend.load(candidate.source_ref.backend_address)
        np.testing.assert_array_equal(
            loaded[expected_indices], pixels[expected_indices]
        )
    array = OmeZarrLocation(store).group["A/01/0/0"]
    assert array.shape == pixels.shape
    assert array.chunks == (1, 1, 1, 4, 5)
    assert array.dtype == pixels.dtype
    if fmt.zarr_format == 3:
        assert array.metadata.dimension_names == ("t", "c", "z", "y", "x")


def test_legacy_polystore_namespace_does_not_override_declared_source_identity(
    tmp_path: Path,
) -> None:
    pixels = np.arange(12, dtype=np.uint16).reshape(3, 4)
    write_ngff_plate(tmp_path, pixels)
    group = zarr.open_group(tmp_path, mode="a")
    group.attrs["ome"] = {"version": "0.4"}
    well = group["A/01"]
    well.attrs["ome"] = {
        "well": {"version": "0.5", "images": [{"path": "missing", "acquisition": 0}]}
    }

    (dataset,) = OmeZarrStoreAdapter().discover_stores(tmp_path)

    assert dataset.identity.value == "Plate:mixed"
    assert len(dataset.candidates) == 1
    candidate = dataset.candidates[0]
    assert candidate.declared_address.value_for(AllComponents.WELL) == "A01"
    loaded = OmeZarrStorageBackend().load(candidate.source_ref.backend_address)
    np.testing.assert_array_equal(loaded[0, 0, 0], pixels)


@pytest.mark.parametrize("fmt", NGFF_FORMATS, ids=lambda fmt: fmt.version)
def test_ngff_image_can_be_submitted_without_its_plate(
    tmp_path: Path,
    fmt: Format,
) -> None:
    pixels = np.arange(12, dtype=np.uint16).reshape(3, 4)
    write_ngff_plate(tmp_path, pixels, fmt=fmt)
    image_path = tmp_path / "A" / "01" / "0"

    (dataset,) = OmeZarrStoreAdapter().discover_stores(image_path)

    assert len(dataset.candidates) == 1
    candidate = dataset.candidates[0]
    assert candidate.source_axis_shape == (1, 1, 1)
    assert candidate.component_labels[AllComponents.CHANNEL.value] == "NGFF"
    loaded = OmeZarrStorageBackend().load(candidate.source_ref.backend_address)
    np.testing.assert_array_equal(loaded[0, 0, 0], pixels)


class _NoJavaStores:
    def declares_path(self, source_path: Path) -> bool:
        del source_path
        return False


def _filemanager() -> FileManager:
    ensure_storage_registry()
    return FileManager(dict(storage_registry))


def _binding(alias: str, file_name: str) -> NamedSourceBinding:
    return NamedSourceBinding(
        alias=alias,
        selector=SourceSelector(
            filters=(
                SourceFilterClause(
                    SourceFilterSubject.FILE,
                    SourceFilterMatchType.EQUALS,
                    file_name,
                ),
            ),
        ),
    )


def _write_mixed_stores(
    root: Path,
    fmt: Format,
) -> dict[str, tuple[Path, np.ndarray]]:
    stores = {
        "NGFF": (root / "plate.zarr", np.full((3, 4), 7, dtype=np.uint16)),
        "TIFF": (root / "plain.tif", np.full((3, 4), 11, dtype=np.uint16)),
        "PNG": (root / "mask.png", np.full((3, 4), 13, dtype=np.uint16)),
    }
    write_ngff_plate(*stores["NGFF"], fmt=fmt)
    for alias in ("TIFF", "PNG"):
        path, pixels = stores[alias]
        ImageFileFormat.require_path(path).write(path, pixels)
    return stores


def test_polystore_zarr_semantic_coordinates_round_trip_through_store_discovery(
    monkeypatch,
    tmp_path: Path,
) -> None:
    monkeypatch.setattr(
        BioFormatsJavaContext,
        "instance",
        classmethod(lambda cls: _NoJavaStores()),
    )
    store_root = tmp_path / "images"
    output_paths = [
        store_root / "A01_s003_w2_z001_t002.tif",
        store_root / "A01_s003_w1_z001_t001.tif",
        store_root / "A01_s003_w2_z001_t001.tif",
        store_root / "A01_s003_w1_z001_t002.tif",
    ]
    layout = ZarrBatchLayout(
        axes=(
            ZarrBatchAxis("t", "time", ("2", "1")),
            ZarrBatchAxis(
                "field",
                "field",
                ("3",),
                ZarrBatchAxisRole.HCS_IMAGE,
            ),
            ZarrBatchAxis("c", "channel", ("2", "1")),
            ZarrBatchAxis("z", "space", ("1",)),
        ),
        item_coordinates=(
            (0, 0, 0, 0),
            (1, 0, 1, 0),
            (1, 0, 0, 0),
            (0, 0, 1, 0),
        ),
    )
    pixels = [np.full((3, 4), index, dtype=np.uint16) for index in range(4)]
    ZarrStorageBackend().save_batch(
        pixels,
        output_paths,
        chunk_name="A01",
        batch_layout=layout,
        row="A",
        col="01",
    )

    dataset = SourcePlaneStoreAdapter.discover_dataset(store_root)

    assert {
        (
            candidate.declared_address.value_for(AllComponents.SITE),
            candidate.declared_address.value_for(AllComponents.CHANNEL),
            candidate.declared_address.value_for(AllComponents.Z_INDEX),
            candidate.declared_address.value_for(AllComponents.TIMEPOINT),
        )
        for candidate in dataset.candidates
    } == {
        ("3", "1", "1", "1"),
        ("3", "1", "1", "2"),
        ("3", "2", "1", "1"),
        ("3", "2", "1", "2"),
    }


@pytest.mark.parametrize("fmt", NGFF_FORMATS, ids=lambda fmt: fmt.version)
def test_mixed_plane_stores_bind_and_load_through_virtual_workspace(
    monkeypatch,
    tmp_path: Path,
    fmt: Format,
) -> None:
    stores = _write_mixed_stores(tmp_path, fmt)
    monkeypatch.setattr(
        BioFormatsJavaContext,
        "instance",
        classmethod(lambda cls: _NoJavaStores()),
    )

    dataset = SourcePlaneStoreAdapter.discover_dataset(tmp_path)

    assert dataset.identity.value == "Plate:mixed"
    assert {candidate.source_ref.backend for candidate in dataset.candidates} == {
        Backend.DISK.value,
        Backend.OME_ZARR.value,
    }
    assert {
        candidate.declared_address.value_for(AllComponents.WELL)
        for candidate in dataset.candidates
    } == {
        "A01",
        "mask.png",
        "plain.tif",
    }

    source_bindings = SourceBindingsConfig(
        bindings=tuple(
            _binding(alias, path.name) for alias, (path, _pixels) in stores.items()
        )
    )
    filemanager = _filemanager()
    handler = create_microscope_handler(
        "auto",
        plate_folder=tmp_path,
        filemanager=filemanager,
        source_bindings_config=source_bindings,
    )
    assert isinstance(handler, BioFormatsHandler)
    assert handler.parser.extract_component_coordinates("plain.tif") == (
        "S",
        "112108097105110046116105102",
    )
    handler.initialize_workspace(tmp_path, filemanager)
    metadata = json.loads(
        (tmp_path / "openhcs_metadata.json").read_text(encoding="utf-8")
    )["subdirectories"]["."]
    paths_by_alias = {
        source_metadata["source_alias"]: virtual_path
        for virtual_path, source_metadata in metadata["source_metadata"].items()
    }

    assert set(paths_by_alias) == {"NGFF", "TIFF", "PNG"}
    for alias, (_path, pixels) in stores.items():
        loaded = filemanager.load(
            tmp_path / paths_by_alias[alias],
            backend=Backend.VIRTUAL_WORKSPACE.value,
        )
        np.testing.assert_array_equal(loaded, pixels)


@pytest.mark.parametrize("fmt", NGFF_FORMATS, ids=lambda fmt: fmt.version)
def test_saved_source_bindings_rebuild_canonical_store_projection(
    monkeypatch,
    tmp_path: Path,
    fmt: Format,
) -> None:
    stores = _write_mixed_stores(tmp_path, fmt)
    monkeypatch.setattr(
        BioFormatsJavaContext,
        "instance",
        classmethod(lambda cls: _NoJavaStores()),
    )
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    initial_bindings = SourceBindingsConfig(
        bindings=tuple(
            _binding(alias, path.name) for alias, (path, _pixels) in stores.items()
        )
    )
    orchestrator = PipelineOrchestrator(
        plate_path=tmp_path,
        pipeline_config=PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig.from_config(
                initial_bindings
            ),
        ),
    ).initialize()
    initial_handler = orchestrator.microscope_handler
    assert isinstance(initial_handler, BioFormatsHandler)
    initial_projection = orchestrator.source_workspace_projection()
    assert {
        projection.source_alias
        for path in initial_projection.relative_virtual_paths()
        if (projection := initial_projection.source_projections_by_virtual_path[path])
    } == set(stores)

    edited_aliases = {"NGFF": "RawNGFF", "TIFF": "RawTIFF", "PNG": "Mask"}
    edited_bindings = SourceBindingsConfig(
        bindings=tuple(
            _binding(edited_aliases[alias], path.name)
            for alias, (path, _pixels) in stores.items()
        )
    )
    orchestrator.apply_pipeline_config(
        PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig.from_config(edited_bindings)
        )
    )

    assert orchestrator.state is OrchestratorState.CREATED
    assert not orchestrator.is_initialized()
    assert orchestrator.microscope_handler is None
    assert orchestrator.get_effective_config().source_bindings_config == edited_bindings

    orchestrator.initialize()

    assert isinstance(orchestrator.microscope_handler, BioFormatsHandler)
    assert orchestrator.microscope_handler is not initial_handler
    projection = orchestrator.source_workspace_projection()
    records = tuple(
        projection.source_projections_by_virtual_path[path]
        for path in projection.relative_virtual_paths()
    )
    assert {record.source_alias for record in records} == set(edited_aliases.values())
    assert {record.address.value_for(AllComponents.WELL) for record in records} == {
        "A01",
        "mask.png",
        "plain.tif",
    }
    assert {
        (
            record.address.value_for(AllComponents.SITE),
            record.address.value_for(AllComponents.CHANNEL),
            record.address.value_for(AllComponents.Z_INDEX),
            record.address.value_for(AllComponents.TIMEPOINT),
        )
        for record in records
    } == {("1", "1", "1", "1")}
    assert {record.ref.backend for record in records} == {
        Backend.DISK.value,
        Backend.OME_ZARR.value,
    }
    assert len({record.ref.backend_address for record in records}) == len(records)
    expected_components = {
        AllComponents.WELL: {"A01", "mask.png", "plain.tif"},
        AllComponents.SITE: {"1"},
        AllComponents.CHANNEL: {"1"},
        AllComponents.Z_INDEX: {"1"},
        AllComponents.TIMEPOINT: {"1"},
    }
    assert {
        component: set(orchestrator.get_component_keys(component))
        for component in AllComponents
    } == expected_components


@pytest.mark.parametrize("fmt", NGFF_FORMATS, ids=lambda fmt: fmt.version)
def test_mixed_plane_stores_materialize_and_reopen_with_source_identity(
    monkeypatch,
    tmp_path: Path,
    fmt: Format,
) -> None:
    stores = _write_mixed_stores(tmp_path, fmt)
    monkeypatch.setattr(
        BioFormatsJavaContext,
        "instance",
        classmethod(lambda cls: _NoJavaStores()),
    )
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    source_bindings = SourceBindingsConfig(
        bindings=tuple(
            _binding(alias, path.name) for alias, (path, _pixels) in stores.items()
        )
    )
    orchestrator = PipelineOrchestrator(
        plate_path=tmp_path,
        pipeline_config=PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig.from_config(source_bindings)
        ),
    ).initialize()
    context = orchestrator.create_context(axis_id="A01")
    projection = orchestrator.source_workspace_projection()
    source_records = {
        projection.source_projections_by_virtual_path[path].source_alias: (
            path,
            projection.source_projections_by_virtual_path[path],
        )
        for path in projection.relative_virtual_paths()
    }

    for alias, (virtual_path, record) in source_records.items():
        payload = orchestrator.filemanager.load(
            tmp_path / virtual_path,
            Backend.VIRTUAL_WORKSPACE.value,
        )
        save_materialized_data(
            orchestrator.filemanager,
            [payload],
            [str(tmp_path / "zarr" / virtual_path)],
            Backend.ZARR.value,
            orchestrator.get_effective_config().zarr_config,
            context,
            record.address.value_for(AllComponents.WELL),
        )
        np.testing.assert_array_equal(payload, stores[alias][1])

    update_metadata_for_zarr_conversion(tmp_path, ".", "zarr", context)

    metadata = json.loads(
        (tmp_path / "openhcs_metadata.json").read_text(encoding="utf-8")
    )
    assert metadata["subdirectories"]["."]["main"] is False
    zarr_metadata = metadata["subdirectories"]["zarr"]
    assert zarr_metadata["main"] is True
    assert zarr_metadata["available_backends"] == {Backend.ZARR.value: True}
    assert {
        source_metadata["source_alias"]
        for source_metadata in zarr_metadata["source_metadata"].values()
    } == set(stores)
    assert {
        payload["backend"] for payload in zarr_metadata["workspace_mapping"].values()
    } == {Backend.ZARR.value}

    reopened = PipelineOrchestrator(plate_path=tmp_path).initialize()
    assert isinstance(reopened.microscope_handler, OpenHCSMicroscopeHandler)
    assert reopened.input_dir == tmp_path / "zarr"
    assert (
        reopened.microscope_handler.get_primary_backend(
            reopened.input_dir,
            reopened.filemanager,
        )
        == Backend.ZARR.value
    )
    reopened_projection = reopened.source_workspace_projection()
    reopened_records = {
        reopened_projection.source_projections_by_virtual_path[path].source_alias: (
            path,
            reopened_projection.source_projections_by_virtual_path[path],
        )
        for path in reopened_projection.relative_virtual_paths()
    }
    assert set(reopened_records) == set(stores)
    for alias, (virtual_path, record) in reopened_records.items():
        assert record.ref.backend == Backend.ZARR.value
        assert record.ref.backend_address == virtual_path
        np.testing.assert_array_equal(
            reopened.filemanager.load(tmp_path / virtual_path, Backend.ZARR.value),
            stores[alias][1],
        )
