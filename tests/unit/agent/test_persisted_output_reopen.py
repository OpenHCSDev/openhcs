"""Public native output inventory -> bounded sample -> original stream, no GUI."""

from types import SimpleNamespace

import numpy as np
import pytest
from polystore.exceptions import MetadataNotFoundError
from polystore.virtual_workspace import SourcePixelRef

from openhcs.agent.dto.plate import (
    PlateFileQueryRequest,
    PlateFileStreamRequest,
    PlateImageSampleRequest,
    PlatePathInspectionRequest,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.constants import Microscope
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.viewer_streaming_service import StreamingService
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.runtime.viewer_protocol import ViewerLaunchContext


def declared_output(root, aliases):
    """Use original writer/codec declarations, never acquisition-shaped filenames."""
    root.mkdir()
    metadata_path = root / "openhcs_metadata.json"
    declarations = []
    for index, alias in enumerate(aliases):
        branch = root / f"saved-{index}"
        branch.mkdir()
        path = branch / "not-an-acquisition.checkpoint.tif"
        pixels = (np.arange(30, dtype=np.uint16).reshape(5, 6) + index)
        provenance = SourceImageProvenance(
            source_path=str(root / "acquisition-reference.tif"),
            source_component_metadata={
                "well": "A01", "site": 1, "channel": 2, "z_index": 1,
                "timepoint": 1,
            },
            source_image_names=(alias,),
        )
        metadata = ImagePayloadMetadata(
            source_provenance=provenance,
            source_voxel_spacing=SourceVoxelSpacing(
                (2, 3), SourceVoxelSpacingUnit.RELATIVE
            ),
            source_spatial_domain=SourceSpatialDomain((7, 11), (20, 30)),
        )
        payload = metadata.payload_with(pixels)
        image_format = ImageFileFormat.require_path(path)
        image_format.write(path, payload)
        virtual_path = str(path.relative_to(root))
        projection = SourceArtifactProjection(
            address=OpenHCSPlaneAddress.from_values("A01", 1, 2, 1, 1),
            ref=SourcePixelRef("disk", virtual_path),
            source_alias=alias,
            artifact_kind=ImageArtifactType,
            image_metadata=image_format.persisted_metadata(path, payload),
        )
        declaration = SourceProjectionMetadataSerializer(
            SourceSchemaFilenameParser()
        ).metadata_dict(
            SourceProjectionSet((projection,)),
            microscope_handler_name=Microscope.SOURCE_BINDINGS.value,
            source_filename_parser_name="SourceSchemaFilenameParser",
            grid_dimensions=[], pixel_size=1,
            projection_paths=((projection, virtual_path),),
        )
        AtomicMetadataWriter().replace_subdirectory_metadata(
            metadata_path, branch.name, declaration
        )
        declarations.append((path, pixels, projection, declaration))
    inspection = PlateInspectionService(
        AgentPathPolicy.with_roots(readable_roots=(root,), writable_roots=())
    )
    return inspection, declarations


class NoRuntimeBridge:
    def viewer_launch_context(self, connection):
        del connection
        return ViewerLaunchContext.projected_graphical_session({"DISPLAY": ":0"})


@pytest.mark.parametrize(
    "aliases",
    [
        ("candidate_mask", "unrooted_residual"),
        ("independent_new_capability", "unrooted_residual", "another_output"),
    ],
)
def test_public_native_inventory_sample_stream_without_historical_receipt(
    tmp_path, monkeypatch, aliases
):
    inspection, declarations = declared_output(tmp_path / "output", aliases)
    root = declarations[0][0].parent.parent
    result = inspection.query_files(PlateFileQueryRequest.from_fields(
        plate_path=str(root), kind="image", include_previews=False
    ))
    assert result.errors == ()
    assert result.warnings == ()
    assert result.total_count == len(aliases)
    for record, (path, pixels, projection, _declaration) in zip(
        result.records, declarations, strict=True
    ):
        assert record.source_path == str(path)
        assert record.metadata["channel"] == "2"
        sampled = inspection.sample_image(PlateImageSampleRequest.from_fields(
            plate_path=str(root), image_path=str(path),
            y=1, x=2, height=2, width=3,
            include_array_values=True, max_array_elements=6,
        ))
        assert sampled.errors == ()
        assert sampled.sample_shape == (2, 3)
        np.testing.assert_array_equal(sampled.sample_values, pixels[1:3, 2:5])

    context, errors, _warnings = inspection.open_context(
        PlatePathInspectionRequest(plate_path=str(root))
    )
    assert errors == ()
    saved = []
    from polystore.filemanager import FileManager

    def receive(_manager, data, paths, backend, **fields):
        saved.append((data, paths, backend, fields))

    # Only native lifecycle and transport endpoints are substituted. The public
    # service, inventory, original image loader/window validator/message builder
    # and streaming algorithm below are real; no canvas or scientific run.
    monkeypatch.setattr(
        "openhcs.agent.services.plate_streaming_service.StreamingViewerLifecycle.get_or_create_visualizer",
        lambda **_fields: SimpleNamespace(port=5992),
    )
    monkeypatch.setattr(StreamingService, "_wait_for_viewer_ready", lambda *_: None)
    monkeypatch.setattr(StreamingService, "_require_viewer_settled", lambda *_: None)
    monkeypatch.setattr(FileManager, "save_batch", receive)
    streamed = PlateStreamingService(inspection, NoRuntimeBridge()).stream_files(
        PlateFileStreamRequest.from_fields(
            plate_path=str(root), kind="image",
            file_paths=[str(path) for path, *_rest in declarations],
        )
    )
    assert streamed.errors == ()
    assert len(streamed.streamed_image_paths) == len(aliases)
    assert saved
    np.testing.assert_array_equal(
        np.concatenate([data for data, *_ in saved]),
        np.stack([pixels for _path, pixels, *_ in declarations]),
    )
    # No-main read-only projection does not invent a pipeline execution input.
    with pytest.raises(MetadataNotFoundError, match="none is marked main"):
        context.handler.metadata_handler.determine_main_subdirectory(root)


def test_no_main_output_rejects_conflicting_workspace_addresses(tmp_path):
    inspection, declarations = declared_output(tmp_path / "output", ("one", "two"))
    root = declarations[0][0].parent.parent
    path, _pixels, _projection, declaration = declarations[1]
    key = next(iter(declarations[0][3]["workspace_mapping"]))
    declaration["workspace_mapping"][key] = SourcePixelRef(
        "disk", str(path.relative_to(root))
    ).to_workspace_mapping()
    AtomicMetadataWriter().replace_subdirectory_metadata(
        root / "openhcs_metadata.json", path.parent.name, declaration
    )
    context, errors, _warnings = inspection.open_context(
        PlatePathInspectionRequest(plate_path=str(root))
    )
    assert errors == ()
    with pytest.raises(ValueError, match="disagree on.*workspace_mapping"):
        context.handler.metadata_handler.workspace_mapping_metadata(root)


@pytest.mark.parametrize("main_branch", ("saved-0", "unmapped"))
def test_read_only_reopening_does_not_replace_explicit_input_authority(
    tmp_path, main_branch
):
    inspection, declarations = declared_output(tmp_path / "output", ("one", "two"))
    root = declarations[0][0].parent.parent
    declaration = dict(declarations[0][3])
    declaration["main"] = True
    if main_branch == "unmapped":
        declaration["workspace_mapping"] = {}
        declaration["source_projection"] = []
        declaration["source_metadata"] = {}
    AtomicMetadataWriter().replace_subdirectory_metadata(
        root / "openhcs_metadata.json", main_branch, declaration
    )
    context, errors, _warnings = inspection.open_context(
        PlatePathInspectionRequest(plate_path=str(root))
    )
    assert errors == ()
    owner = context.handler.metadata_handler
    assert owner.determine_main_subdirectory(root) == main_branch
    if main_branch == "unmapped":
        with pytest.raises(ValueError, match="does not own"):
            owner.workspace_mapping_metadata(root)
    else:
        assert owner.workspace_mapping_metadata(root) == declaration


def test_no_main_output_rejects_incompatible_backend_owners(tmp_path):
    inspection, declarations = declared_output(tmp_path / "output", ("one", "two"))
    root = declarations[0][0].parent.parent
    path, _pixels, _projection, declaration = declarations[1]
    declaration["microscope_handler_name"] = "imagexpress"
    AtomicMetadataWriter().replace_subdirectory_metadata(
        root / "openhcs_metadata.json", path.parent.name, declaration
    )
    result = inspection.query_files(PlateFileQueryRequest.from_fields(
        plate_path=str(root), kind="image", include_previews=False
    ))
    assert result.returned_count == 0
    assert any(
        "disagree on 'microscope_handler_name'" in item.message
        for item in (*result.errors, *result.warnings)
    )


def test_metadata_projection_uses_one_document_loader_and_writer_invalidation(
    tmp_path, monkeypatch
):
    inspection, declarations = declared_output(tmp_path / "output", ("one", "two"))
    root = declarations[0][0].parent.parent
    context, errors, _warnings = inspection.open_context(
        PlatePathInspectionRequest(plate_path=str(root))
    )
    assert errors == ()
    owner = type(context.handler.metadata_handler)(context.filemanager)
    original_load = context.filemanager.load
    loaded = []

    def observe(path, backend, *args, **kwargs):
        loaded.append(path)
        return original_load(path, backend, *args, **kwargs)

    monkeypatch.setattr(context.filemanager, "load", observe)
    document = owner.source_workspace_metadata_document(root)
    assert owner.get_pixel_size(root) == 1
    assert len(owner.get_image_files(root, all_subdirs=True)) == 2
    assert owner.source_workspace_metadata_document(root) is document
    assert loaded == [str(root / "openhcs_metadata.json")]
    owner.update_available_backends(root, {"disk": True})
    assert owner.get_pixel_size(root) == 1
    assert len(loaded) == 2
    assert owner.source_workspace_metadata_document(root) is not document


def test_unbound_explicit_result_image_still_requires_a_receipt(tmp_path, monkeypatch):
    inspection, declarations = declared_output(tmp_path / "output", ("one", "two"))
    root = declarations[0][0].parent.parent
    results = root / "undeclared-results"
    results.mkdir()
    # A real saved image is not itself proof of the acquisition it represents.
    path = results / "looks-like-A01-w2.tif"
    ImageFileFormat.require_path(path).write(path, np.zeros((2, 3), dtype=np.uint16))
    monkeypatch.setattr(
        "openhcs.agent.services.plate_streaming_service.StreamingViewerLifecycle.get_or_create_visualizer",
        lambda **_fields: pytest.fail("Unbound image must not launch a viewer"),
    )
    result = PlateStreamingService(inspection, NoRuntimeBridge()).stream_files(
        PlateFileStreamRequest.from_fields(
            plate_path=str(root), kind="result", result_directory=str(results),
            file_paths=[str(path)],
        )
    )
    assert len(result.errors) == 1
    assert "exact source receipt" in result.errors[0].message
    assert result.streamed_image_paths == ()
