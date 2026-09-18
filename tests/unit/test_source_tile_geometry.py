"""Structural, synthetic-only checks of embedded acquisition tile placement."""

import json
from pathlib import Path
from xml.etree import ElementTree as ET

import numpy as np
import pytest
import tifffile
from polystore.base import ensure_storage_registry, storage_registry
from polystore.filemanager import FileManager
from polystore.source_tile_geometry import SourceTileGeometry
from polystore.tiff_header import TiffImageHeader

from openhcs.constants.constants import AllComponents, Backend
from openhcs.core.callable_contract import CallableContract
from openhcs.core.memory import numpy
from openhcs.core.runtime_adapters import runtime_adapter
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector
from openhcs.core.source_bindings import (
    MetadataExtractionRule,
    MetadataSource,
    SourceBindingsConfig,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_tile_geometry import SourceTileLayout
from openhcs.core.virtual_workspace_metadata import FIELDS
from openhcs.microscopes.imagexpress_source_metadata import (
    ImageXpressTiffSourceMetadataAdapter,
)
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.processing.backends.assemblers.assemble_stack_cpu import assemble_stack_cpu
from openhcs.processing.backends.assemblers.blending import TileBlendMethod
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.pos_gen.acquisition_positions import (
    _source_metadata,
    acquisition_tile_positions,
)


def _xml(
    *, x=-2.5, y=1.25, row=1, column=1, sx=0.5, sy=0.25, units="um", extra=(), omit=()
):
    root = ET.Element("MetaData")
    plane = ET.SubElement(root, "PlaneInfo")
    values = {
        "OffsetFromWellCenterUmX": x,
        "OffsetFromWellCenterUmY": y,
        "SiteX": column,
        "SiteY": row,
        "spatial-calibration-x": sx,
        "spatial-calibration-y": sy,
        "spatial-calibration-units": units,
        "spatial-calibration-state": "on",
    }
    for key, value in (*values.items(), *extra):
        if key not in omit:
            ET.SubElement(plane, "prop", id=key, value=str(value))
    return ET.tostring(root, encoding="unicode")


def _write(path, **kwargs):
    tifffile.imwrite(
        path,
        np.ones((4, 6), dtype=np.uint16),
        description=_xml(**kwargs),
        metadata=None,
    )
    return path


def _filemanager():
    ensure_storage_registry()
    return FileManager(dict(storage_registry))


def _config():
    return SourceBindingsConfig(
        metadata_rules=(
            MetadataExtractionRule(
                MetadataSource.FILE_NAME,
                r"(?P<well>A\d+)_s(?P<site>\d+)_w(?P<channel>\d+)_z(?P<z_index>\d+)_t(?P<timepoint>\d+)\.tif",
            ),
        )
    )


def _projector():
    return SourceBindingWorkspaceProjector(
        _config(), parser=SourceSchemaFilenameParser()
    )


def _metadata(geometries, order, channel="1"):
    records = tuple(
        {
            "well": "A01",
            "site": str(site + 1),
            "channel": channel,
            "z_index": "1",
            "timepoint": "1",
            SourceTileGeometry.metadata_field: geometries[site].as_metadata_value(),
        }
        for site in order
    )
    return ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"source-{site}" for site in order),
            component_metadata=records,
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )


@pytest.mark.parametrize("coordinates", ((-3.25, 4.125), (0, 0), (1e6, -1e6)))
def test_fractional_signed_geometry_roundtrip(coordinates):
    value = SourceTileGeometry(
        *coordinates, row=2, column=4, width_pixels=6, height_pixels=4
    )
    metadata = {value.metadata_field: json.loads(json.dumps(value.as_metadata_value()))}
    assert SourceTileGeometry.from_source_metadata(metadata) == value


@pytest.mark.parametrize(
    "kwargs",
    (
        {"x_pixels": float("nan"), "y_pixels": 0},
        {"x_pixels": 0, "y_pixels": float("inf")},
        {"x_pixels": 0, "y_pixels": 0, "row": 1},
        {"x_pixels": 0, "y_pixels": 0, "row": 1.5, "column": 0},
        {"x_pixels": 0, "y_pixels": 0, "row": True, "column": 0},
        {"x_pixels": 0, "y_pixels": 0, "width_pixels": -1, "height_pixels": 4},
    ),
)
def test_geometry_rejects_invalid_coordinates(kwargs):
    with pytest.raises(ValueError):
        SourceTileGeometry(**kwargs)


def test_grid_projection_does_not_infer_shuffled_serpentine_holes_or_unknown():
    grid = tuple(
        SourceTileGeometry(column * 4.1, row * 3.8, row=row, column=column)
        for row in range(2)
        for column in range(3)
    )
    assert SourceTileGeometry.rectangular_grid_dimensions(
        grid, require_row_major=True
    ) == (2, 3)
    assert SourceTileGeometry.rectangular_grid_dimensions(grid[::-1]) == (2, 3)
    assert (
        SourceTileGeometry.rectangular_grid_dimensions(
            grid[::-1], require_row_major=True
        )
        is None
    )
    assert (
        SourceTileGeometry.rectangular_grid_dimensions(
            grid[:3] + grid[3:][::-1], require_row_major=True
        )
        is None
    )
    assert SourceTileGeometry.rectangular_grid_dimensions(grid[:2] + grid[3:]) is None
    assert SourceTileGeometry.rectangular_grid_dimensions(grid + grid[:1]) is None
    assert (
        SourceTileGeometry.rectangular_grid_dimensions((SourceTileGeometry(0, 0),))
        is None
    )


def test_tiff_header_and_anisotropic_calibration_are_header_only(tmp_path, monkeypatch):
    path = _write(tmp_path / "tile.tif")
    monkeypatch.setattr(
        tifffile.TiffPage, "asarray", lambda *a, **k: pytest.fail("pixel decoding")
    )
    assert TiffImageHeader.read(path).shape == (4, 6)
    metadata = ImageXpressTiffSourceMetadataAdapter().source_metadata_for_path(path)
    geometry = SourceTileGeometry.from_source_metadata(metadata)
    assert (geometry.x_pixels, geometry.y_pixels) == (-5.0, 5.0)
    assert (geometry.row, geometry.column) == (0, 0)
    assert SourceVoxelSpacing.from_source_metadata(metadata) == SourceVoxelSpacing(
        (0.25, 0.5)
    )


@pytest.mark.parametrize(
    "kwargs",
    (
        {"units": "pixels"},
        {"units": "unknown"},
        {"sx": 0},
        {"sy": float("nan")},
        {"row": 1.5},
        {"column": 0},
        {"x": float("inf")},
        {"omit": ("OffsetFromWellCenterUmY",)},
        {"extra": (("SiteX", 99),)},
    ),
)
def test_declared_xml_geometry_fails_on_malformed_or_conflicting_properties(
    tmp_path, kwargs
):
    path = _write(tmp_path / "tile.tif", **kwargs)
    with pytest.raises(ValueError):
        ImageXpressTiffSourceMetadataAdapter().source_metadata_for_path(path)


def test_ordinary_raw_files_without_embedded_layout_stay_unknown(tmp_path):
    path = tmp_path / "A01_s001_w1_z001_t001.tif"
    tifffile.imwrite(path, np.ones((4, 6), dtype=np.uint16))
    projector = _projector()
    materialization = projector.materialize(
        tmp_path,
        tmp_path / "workspace",
        filemanager=_filemanager(),
        source_backend=Backend.DISK,
        workspace_backend=Backend.DISK,
        source_files=(path,),
    )
    payload = json.loads(materialization.metadata_path.read_text())["subdirectories"][
        FIELDS.DEFAULT_SUBDIRECTORY
    ]
    assert payload[FIELDS.GRID_DIMENSIONS] == []
    assert all(
        SourceTileGeometry.from_source_metadata(value) is None
        for value in payload[FIELDS.SOURCE_METADATA].values()
    )
    with pytest.raises(ValueError, match="two integers"):
        OpenHCSMetadataHandler(_filemanager()).get_grid_dimensions(
            tmp_path / "workspace"
        )


def test_materialization_preserves_binding_axes_serialization_and_shared_sparse_canvas(
    tmp_path,
):
    paths = tuple(
        _write(
            tmp_path / f"A01_s{site:03d}_w{channel}_z001_t001.tif",
            x=(site - 1) * 2.1,
            y=-0.125,
            column=site,
        )
        for channel in (2, 1)
        for site in (3, 1)
    )
    projector = _projector()
    projection = projector.projection_set(tmp_path, paths, filemanager=_filemanager())
    layouts = SourceTileLayout.from_projection_set(projection)
    assert len(layouts) == 1
    assert set(layouts[0].sites) == {"1", "3"}
    assert SourceTileLayout.metadata_grid_dimensions(projection) == []
    assert {
        (
            p.address.value_for(AllComponents.SITE),
            p.address.value_for(AllComponents.CHANNEL),
        )
        for p in projection.plane_projections
    } == {("1", "1"), ("1", "2"), ("3", "1"), ("3", "2")}
    workspace = tmp_path / "workspace"
    materialization = projector.materialize(
        tmp_path,
        workspace,
        filemanager=_filemanager(),
        source_backend=Backend.DISK,
        workspace_backend=Backend.DISK,
        source_files=paths,
    )
    serialized = json.loads(materialization.metadata_path.read_text())[
        "subdirectories"
    ][FIELDS.DEFAULT_SUBDIRECTORY]
    assert all(
        SourceTileGeometry.from_source_metadata(metadata).width_pixels == 6
        for metadata in serialized[FIELDS.SOURCE_METADATA].values()
    )
    again = projector.materialize(
        tmp_path,
        workspace,
        filemanager=_filemanager(),
        source_backend=Backend.DISK,
        workspace_backend=Backend.DISK,
        source_files=paths,
    )
    assert (
        json.loads(again.metadata_path.read_text())["subdirectories"][
            FIELDS.DEFAULT_SUBDIRECTORY
        ]
        == serialized
    )


@pytest.mark.parametrize("difference", ("position", "missing", "shape"))
def test_paired_channels_reject_nonshared_site_identity_canvas(tmp_path, difference):
    paths = []
    for channel in (1, 2):
        for site in (1, 2):
            if difference == "missing" and (channel, site) == (2, 2):
                continue
            kwargs = {"x": (site - 1) * 2.1, "column": site}
            if difference == "position" and channel == 2:
                kwargs["x"] += 0.01
            path = _write(
                tmp_path / f"A01_s{site:03d}_w{channel}_z001_t001.tif", **kwargs
            )
            if difference == "shape" and channel == 2:
                tifffile.imwrite(
                    path,
                    np.ones((4, 7), np.uint16),
                    description=_xml(**kwargs),
                    metadata=None,
                )
            paths.append(path)
    with pytest.raises(ValueError, match="identical source site geometry and canvas"):
        _projector().projection_set(tmp_path, paths, filemanager=_filemanager())


def test_position_artifact_preserves_shuffled_paired_order_and_exact_shared_canvas():
    geometries = (
        SourceTileGeometry(
            -1.25, -0.5, row=0, column=0, width_pixels=6, height_pixels=4
        ),
        SourceTileGeometry(
            3.375, -0.25, row=0, column=1, width_pixels=6, height_pixels=4
        ),
        SourceTileGeometry(
            -1.125, 2.875, row=1, column=0, width_pixels=6, height_pixels=4
        ),
    )
    metadata = OpenHCSRegistry.metadata_for_declared_callable(
        acquisition_tile_positions
    )
    assert metadata.contract is ProcessingContract.PURE_3D
    assert tuple(
        spec.name
        for spec in CallableContract.from_callable(metadata.func).artifact_outputs
    ) == ("positions",)
    raw_assemble = CallableContract.from_callable(
        assemble_stack_cpu
    ).resolve_raw_runtime_callable()
    mosaics = []
    for channel, order in (("1", (2, 0, 1)), ("2", (1, 2, 0))):
        sources = _metadata(geometries, order, channel)
        stack = np.stack([np.full((4, 6), site + 1, np.uint16) for site in order])
        payload = ImageMetadataPayload(stack, sources)
        output, positions = metadata.func(payload, source_metadata=sources)
        assert positions == [
            (geometries[site].x_pixels, geometries[site].y_pixels) for site in order
        ]
        assert output.metadata.source_image_paths == sources.source_image_paths
        mosaic = raw_assemble(stack, positions, blend_method=TileBlendMethod.NONE)
        mosaics.append(mosaic)
    assert mosaics[0].shape == mosaics[1].shape == (8, 12)
    # Order-independent placement when non-overlapping source pixels agree.
    assert all(np.isfinite(mosaic).all() for mosaic in mosaics)


def test_positions_reject_unknown_duplicate_or_resized_geometry():
    geometries = (SourceTileGeometry(0, 0, width_pixels=6, height_pixels=4),)
    function = OpenHCSRegistry.metadata_for_declared_callable(
        acquisition_tile_positions
    ).func
    with pytest.raises(ValueError, match="Incoming tile shape"):
        function(np.ones((1, 4, 7)), source_metadata=_metadata(geometries, (0,)))
    with pytest.raises(ValueError, match="distinct source site"):
        function(np.ones((2, 4, 6)), source_metadata=_metadata(geometries, (0, 0)))
    with pytest.raises(ValueError, match="exact embedded acquisition geometry"):
        function(
            np.ones((1, 4, 6)),
            source_metadata=ImagePayloadMetadata(
                source_component_metadata={
                    "well": "A01",
                    "site": "1",
                    "channel": "1",
                    "z_index": "1",
                    "timepoint": "1",
                }
            ),
        )


@runtime_adapter("source_metadata", _source_metadata)
@numpy(contract=ProcessingContract.PURE_3D)
def _verify_paired_stitched_mosaics(
    image: np.ndarray, *, source_metadata: ImagePayloadMetadata
) -> np.ndarray:
    """Synthetic analysis consumer: requires channels, never source sites."""
    assert image.shape == (2, 10, 16)
    records = source_metadata.source_plane_metadata_records()
    assert len(records) == 2
    assert tuple(
        source_component_metadata_value(
            record.source_component_metadata, AllComponents.CHANNEL
        )
        for record in records
    ) == ("1", "2")
    assert all(
        len(record.source_provenance.represented_source_identities) == 9
        for record in records
    )
    assert source_metadata.source_voxel_spacing == SourceVoxelSpacing((0.25, 0.5))
    return image


@pytest.mark.parametrize(
    "embedded,assembly_backend,storage_backend",
    (
        (True, "cpu", "disk"),
        (True, "gpu", "disk"),
        (False, "cpu", "disk"),
        (True, "cpu", "zarr"),
        (True, "gpu", "zarr"),
    ),
)
def test_synthetic_pipeline_compiles_and_executes_positions_artifact_then_paired_channels(
    tmp_path, embedded, assembly_backend, storage_backend
):
    from objectstate import ObjectStateRegistry
    from objectstate.lazy_factory import ensure_global_config_context

    from openhcs.constants.constants import GroupBy, Microscope, VariableComponents
    from openhcs.core.config import (
        AnalysisConsolidationConfig,
        GlobalPipelineConfig,
        InputSource,
        LazyProcessingConfig,
        LazySourceBindingsConfig,
        LazyStepMaterializationConfig,
        LazyVFSConfig,
        MaterializationBackend,
        PipelineConfig,
    )
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.steps import FunctionStep

    assembler = assemble_stack_cpu
    if assembly_backend == "gpu":
        cp = pytest.importorskip("cupy")
        from cupy_backends.cuda.libs import nvrtc

        try:
            if not cp.cuda.runtime.getDeviceCount():
                pytest.skip("native CUDA device unavailable")
            nvrtc.getVersion()
        except (cp.cuda.runtime.CUDARuntimeError, RuntimeError) as exc:
            pytest.skip(f"native CUDA test dependency unavailable: {exc}")
        from openhcs.processing.backends.assemblers.assemble_stack_cupy import (
            assemble_stack_cupy,
        )

        assembler = assemble_stack_cupy

    plate = tmp_path / "synthetic-plate"
    plate.mkdir()
    for channel in (2, 1):
        for site in (9, 3, 7, 1, 8, 2, 6, 4, 5):
            row, column = (site - 1) // 3 + 1, (site - 1) % 3 + 1
            path = plate / f"A01_s{site:03d}_w{channel}_z001_t001.tif"
            if embedded:
                _write(
                    path,
                    x=(column - 1) * 2.3125 - 0.625,
                    y=(row - 1) * 0.59375 - 0.125,
                    row=row,
                    column=column,
                )
            else:
                tifffile.imwrite(path, np.full((4, 6), channel, np.uint16))
    ObjectStateRegistry.clear()
    import queue

    from openhcs.core.progress import set_progress_queue

    progress = queue.Queue()
    set_progress_queue(progress)
    try:
        global_config = GlobalPipelineConfig(
            num_workers=1,
            microscope=Microscope.SOURCE_BINDINGS,
            use_threading=True,
            analysis_consolidation_config=AnalysisConsolidationConfig(enabled=False),
        )
        ensure_global_config_context(GlobalPipelineConfig, global_config)
        config = PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig.from_config(_config()),
            vfs_config=LazyVFSConfig(
                materialization_backend=MaterializationBackend(storage_backend)
            ),
        )
        orchestrator = PipelineOrchestrator(plate, pipeline_config=config).initialize()
        if embedded:
            site_processing = LazyProcessingConfig(
                variable_components=[VariableComponents.SITE], group_by=GroupBy.CHANNEL
            )
            steps = [
                FunctionStep(
                    name="Embedded acquisition positions",
                    func=acquisition_tile_positions,
                    processing_config=site_processing,
                ),
                FunctionStep(
                    name="Shared channel canvas",
                    func=(assembler, {"blend_method": TileBlendMethod.NONE}),
                    processing_config=site_processing,
                ),
                FunctionStep(
                    name="Paired stitched channel consumer",
                    func=_verify_paired_stitched_mosaics,
                    step_materialization_config=LazyStepMaterializationConfig(
                        enabled=True, sub_dir="checkpoints"
                    ),
                    processing_config=LazyProcessingConfig(
                        variable_components=[VariableComponents.CHANNEL],
                        group_by=GroupBy.NONE,
                        input_source=InputSource.PREVIOUS_STEP,
                    ),
                ),
            ]
        else:
            # Ordinary non-stitching analysis must compile with truly unknown grid.
            from openhcs.processing.backends.processors.numpy_processor import (
                stack_percentile_normalize,
            )

            steps = [FunctionStep(func=stack_percentile_normalize)]
        compilation = orchestrator.compile_pipelines(
            pipeline_definition=steps, well_filter=["A01"]
        )
        context = compilation.runtime_contexts["A01"]
        if embedded:
            producer = next(
                context.step_plans[0].compiled_function_pattern.iter_invocations()
            )
            consumer = next(
                context.step_plans[1].compiled_function_pattern.iter_invocations()
            )
            assert (
                producer.contract.runtime_adapter.require_parameter_name()
                == "source_metadata"
            )
            assert any(
                edge.spec.name == "positions" for edge in consumer.artifact_input_edges
            )
            assert context.step_plans[2].variable_components == [
                VariableComponents.CHANNEL
            ]
        result = orchestrator.execute_compiled_plate(
            execution_bundle=compilation,
            progress_queue=progress,
            progress_context={
                "execution_id": f"test::source-geometry::{embedded}",
                "plate_id": str(plate),
                "axis_id": "",
            },
        )
        assert result["A01"].is_success(), result["A01"].error_message
        if embedded:
            # Both channel groups retain their ordered pixel-valued positions;
            # the same runtime artifacts still drive the native paired replay.
            position_outputs = tuple(
                context.step_plans[0].artifact_analysis_output_dir.glob(
                    "*positions*.json"
                )
            )
            assert len(position_outputs) == 2, (
                context.step_plans[0].artifact_analysis_output_dir,
                tuple(Path(context.output_plate_root).rglob("*positions*.json")),
            )
            expected_positions = [
                [((site - 1) % 3) * 4.625 - 1.25, ((site - 1) // 3) * 2.375 - 0.5]
                for site in range(1, 10)
            ]
            for position_output in position_outputs:
                assert json.loads(position_output.read_text()) == expected_positions

            from openhcs.microscopes.microscope_base import (
                MicroscopeSourceSelectionRole,
            )
            from openhcs.microscopes.openhcs import OpenHCSMicroscopeHandler

            output_plate = Path(context.output_plate_root)
            metadata_path = output_plate / OpenHCSMetadataHandler.METADATA_FILENAME
            persisted_bytes = metadata_path.read_bytes()
            persisted = json.loads(persisted_bytes)
            image_subdirectories = [
                subdir
                for subdir in persisted["subdirectories"].values()
                if subdir.get("source_projection")
            ]
            assert len(image_subdirectories) == 2  # Main and materialized images.
            for subdir in image_subdirectories:
                assert subdir["grid_dimensions"] == []  # Mosaics are not 3x3 tile axes.
                assert len(subdir["source_projection"]) == 2
                for entry in subdir["source_projection"]:
                    metadata = ImagePayloadMetadata.from_mapping(
                        entry["image_metadata"]
                    )
                    assert (
                        len(metadata.source_provenance.represented_source_identities)
                        == 9
                    )
                    assert metadata.source_voxel_spacing == SourceVoxelSpacing(
                        (0.25, 0.5)
                    )
                    assert metadata.plane_axis is None
            replay_config = MicroscopeSourceSelectionRole.PREPARED_WORKSPACE.pipeline_config_for_source(
                config
            )
            reopened = PipelineOrchestrator(
                output_plate, pipeline_config=replay_config
            ).initialize()
            assert isinstance(reopened.microscope_handler, OpenHCSMicroscopeHandler)
            input_dir = reopened.microscope_handler.initialize_workspace(
                output_plate, reopened.filemanager
            )
            assert input_dir == reopened.input_dir
            assert metadata_path.read_bytes() == persisted_bytes
            # Execution tears down its queue; a second explicit compile needs
            # the harness to establish its own progress context again.
            set_progress_queue(progress)
            replay = reopened.compile_pipelines(
                pipeline_definition=[
                    FunctionStep(
                        func=_verify_paired_stitched_mosaics,
                        processing_config=LazyProcessingConfig(
                            variable_components=[VariableComponents.CHANNEL],
                            group_by=GroupBy.NONE,
                            input_source=InputSource.PIPELINE_START,
                        ),
                    )
                ],
                well_filter=["A01"],
            )
            replay_result = reopened.execute_compiled_plate(
                execution_bundle=replay,
                progress_queue=progress,
                progress_context={
                    "execution_id": f"test::stitched-output-replay::{assembly_backend}",
                    "plate_id": str(output_plate),
                    "axis_id": "",
                },
            )
            assert replay_result["A01"].is_success(), replay_result["A01"].error_message
    finally:
        set_progress_queue(None)
        ObjectStateRegistry.clear()
