"""Persisted semantic image metadata across source-projection replay."""

import concurrent.futures
import json
import multiprocessing
from collections.abc import Mapping
from pathlib import Path

import numpy as np
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import AllComponents
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload,
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.source_binding_selection import SourcePatternResolutionContext
from openhcs.core.source_bindings import SourceBindingRuntimeContext
from openhcs.core.source_image_provenance import (
    SourceImageProvenance,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.serialization.json import to_jsonable

VIRTUAL_PATH = "A01_s001_w1_z001_t001.tif"


def _collapsed_metadata() -> ImagePayloadMetadata:
    return ImagePayloadMetadata(
        source_provenance=SourceImageProvenance(
            source_component_metadata={
                "well": "A01",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
            },
            source_image_provenance_planes=SourceImageProvenancePlanes.from_contributor_components(
                paths=("/source/site-1.tif", "/source/site-2.tif"),
                component_metadata=({"site": "1"}, {"site": "2"}),
            ),
        ),
        source_dtype="uint16",
    )


def _projection(
    image_metadata: ImagePayloadMetadata | None,
    source_metadata: Mapping[str, object] | None = None,
) -> SourcePlaneProjection:
    return SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values("A01", 1, 1, 1, 1),
        ref=SourcePixelRef("disk", VIRTUAL_PATH),
        image_metadata=image_metadata,
        source_metadata={} if source_metadata is None else source_metadata,
    )


def _serialized_metadata(
    image_metadata: ImagePayloadMetadata | None,
    source_metadata: Mapping[str, object] | None = None,
) -> dict[str, object]:
    projection_set = SourceProjectionSet(
        (_projection(image_metadata, source_metadata),)
    )
    subdirectory = projection_set.metadata_dict(
        parser=SourceSchemaFilenameParser(),
        microscope_handler_name="openhcs",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, 1],
        pixel_size=1.0,
    )
    return json.loads(json.dumps({"subdirectories": {".": subdirectory}}))


def _resolve_persisted_nested_metadata_in_spawned_runtime(
    document: dict[str, object],
) -> dict[str, object]:
    """Exercise the worker's normalized metadata-to-selector path."""

    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        Path("/plate"), document
    )
    runtime_context = SourceBindingRuntimeContext(
        step_input_files=(VIRTUAL_PATH,),
        step_input_source_paths={VIRTUAL_PATH: VIRTUAL_PATH},
        source_metadata_by_path=projection.source_metadata_by_path,
    )
    selection_context = SourcePatternResolutionContext.from_runtime_context(
        parser=SourceSchemaFilenameParser(),
        runtime_context=runtime_context,
    )
    metadata = selection_context.metadata_for_path(VIRTUAL_PATH)
    if metadata is None:
        raise AssertionError("Persisted source metadata was not resolved.")
    nested = metadata["source_tile_geometry"]
    if not isinstance(nested, Mapping):
        raise TypeError("Nested source metadata lost its mapping contract.")
    return dict(nested)


def test_image_payload_metadata_codec_preserves_collapsed_contributors() -> None:
    metadata = _collapsed_metadata()

    restored = ImagePayloadMetadata.from_mapping(to_jsonable(metadata))

    assert restored == metadata
    assert "site" not in restored.source_component_metadata
    assert len(restored.source_provenance.represented_source_identities) == 2


def test_source_projection_serialization_decodes_typed_image_metadata() -> None:
    document = _serialized_metadata(_collapsed_metadata())
    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        Path("/plate"), document
    ).require_source_projection_for(
        VirtualWorkspacePathLookup.from_paths(VIRTUAL_PATH, VIRTUAL_PATH)
    )

    assert projection.address.value_for(AllComponents.SITE) == "1"
    assert projection.image_metadata == _collapsed_metadata()


def test_image_artifact_projection_round_trips_typed_pixel_metadata() -> None:
    metadata = ImagePayloadMetadata(
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "2",
            "z_index": "1",
            "timepoint": "1",
        },
        source_dtype="uint8",
    )
    projection = SourceArtifactProjection(
        address=OpenHCSPlaneAddress.from_values("A01", 1, 2, 1, 1),
        ref=SourcePixelRef("disk", "analysis/A01_candidate.checkpoint.tif"),
        source_alias="neurite_candidate_mask",
        artifact_kind=ImageArtifactType,
        source_metadata=metadata.source_component_metadata,
        image_metadata=metadata,
    )
    virtual_path = "analysis/A01_candidate.checkpoint.tif"
    projection_set = SourceProjectionSet((projection,))
    subdirectory = SourceProjectionMetadataSerializer(
        SourceSchemaFilenameParser()
    ).metadata_dict(
        projection_set,
        microscope_handler_name="openhcs",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, 1],
        pixel_size=1.0,
        projection_paths=((projection, virtual_path),),
    )
    document = json.loads(json.dumps({"subdirectories": {"analysis": subdirectory}}))

    restored = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        Path("/plate"), document
    ).require_source_projection_for(
        VirtualWorkspacePathLookup.from_paths(virtual_path, virtual_path)
    )

    assert restored.source_alias == "neurite_candidate_mask"
    assert restored.artifact_kind is ImageArtifactType
    assert restored.image_metadata == metadata


def test_legacy_projection_replay_uses_complete_top_level_source_metadata() -> None:
    document = _serialized_metadata(None)
    workspace = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        Path("/plate"), document
    )
    payload = ImageMetadataPayload(
        np.zeros((3, 4), dtype=np.uint16),
        ImagePayloadMetadata(source_path="/loaded/legacy.tif"),
    )

    projected = workspace.project_unbound_payload(
        VirtualWorkspacePathLookup.from_paths(VIRTUAL_PATH, VIRTUAL_PATH), payload
    )

    assert image_payload_metadata(projected).source_component_metadata["site"] == "1"


def test_site_collapsed_serialize_read_project_roundtrip_keeps_semantics() -> None:
    document = _serialized_metadata(_collapsed_metadata())
    subdirectory = document["subdirectories"]["."]
    assert subdirectory["source_metadata"][VIRTUAL_PATH]["site"] == "1"
    workspace = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        Path("/plate"), document
    )
    payload = ImageMetadataPayload(
        np.zeros((3, 4), dtype=np.uint16),
        ImagePayloadMetadata(
            source_path="/loaded/mosaic.tif",
            source_component_metadata={
                "well": "A01",
                "site": "1",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
            },
        ),
    )

    projected = workspace.project_unbound_payload(
        VirtualWorkspacePathLookup.from_paths(VIRTUAL_PATH, VIRTUAL_PATH), payload
    )
    metadata = image_payload_metadata(projected)

    assert dict(metadata.source_component_metadata) == {
        "well": "A01",
        "channel": "1",
        "z_index": "1",
        "timepoint": "1",
    }
    contributors = metadata.source_provenance.represented_source_identities
    assert tuple(
        contributor.component_metadata["site"] for contributor in contributors
    ) == ("1", "2")
    assert (
        workspace.require_source_projection_for(
            VirtualWorkspacePathLookup.from_paths(VIRTUAL_PATH, VIRTUAL_PATH)
        ).address.value_for(AllComponents.SITE)
        == "1"
    )


def test_persisted_nested_source_metadata_matches_in_spawned_runtime() -> None:
    tile_geometry = {
        "x_pixels": -921.5,
        "y_pixels": 17.25,
        "row": 0,
        "column": 1,
        "width_pixels": 1024,
        "height_pixels": 1024,
    }
    document = _serialized_metadata(
        None,
        source_metadata={"source_tile_geometry": tile_geometry},
    )

    context = multiprocessing.get_context("spawn")
    with concurrent.futures.ProcessPoolExecutor(
        max_workers=1,
        mp_context=context,
    ) as executor:
        resolved = executor.submit(
            _resolve_persisted_nested_metadata_in_spawned_runtime,
            document,
        ).result(timeout=30)

    assert resolved == tile_geometry
