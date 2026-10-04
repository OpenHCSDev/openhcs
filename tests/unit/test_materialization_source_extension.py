"""Issues257/264: preserve source identity into ordinary image publication."""

from pathlib import Path
from dataclasses import replace
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
    image_payload_metadata,
)
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenance,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceImagePayloadProjection,
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
)
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.processing.materialization import ImageFileOptions, MaterializationSpec
from openhcs.processing.materialization.core import (
    ParserBackedSourceStemAuthority,
    materialization_outputs,
)
from openhcs.serialization.json import to_jsonable

COMPONENTS = {
    "well": "image.ome.tif",
    "site": "1",
    "channel": "1",
    "z_index": "1",
    "timepoint": "1",
}


@pytest.mark.parametrize("extension", (".tif", ".ome.tif"))
def test_native_header_only_workspace_keeps_loaded_source_identity(extension):
    """Same empty persisted provenance as259-02, without opening its pixels."""
    virtual_path = f"image.ome.tif_s001_w1_z001_t001{extension}"
    source_path = f"/input/physical.source{extension}"
    document = {
        "subdirectories": {
            ".": {
                "workspace_mapping": {
                    virtual_path: {
                        "backend": "disk",
                        "backend_address": source_path,
                        "source_axis_indices": [],
                    },
                },
                "source_metadata": {virtual_path: COMPONENTS},
                "source_projection": [
                    {
                        "virtual_path": virtual_path,
                        "address": COMPONENTS,
                        "ref": {
                            "backend": "disk",
                            "backend_address": source_path,
                            "source_axis_indices": [],
                        },
                        "projection_role": "primary_plane",
                        "image_metadata": to_jsonable(
                            ImagePayloadMetadata(source_dtype="uint16")
                        ),
                    }
                ],
            },
        },
    }
    workspace = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        Path("/plate"), document
    )
    loaded = ImagePayloadMetadata(
        source_path=source_path,
        source_component_metadata={**COMPONENTS, "extension": extension},
        source_image_names=("fixture",),
    ).payload_with(np.ones((8, 8), dtype=np.uint16))
    projected = workspace.project_unbound_payload(
        VirtualWorkspacePathLookup.from_paths(virtual_path, f"/plate/{virtual_path}"),
        loaded,
    )
    metadata = image_payload_metadata(projected)
    assert metadata.source_path == source_path
    assert metadata.source_component_metadata == {**COMPONENTS, "extension": extension}
    assert metadata.source_image_names == ("fixture",)
    assert metadata.source_dtype == "uint16"

    outputs = materialization_outputs(
        MaterializationSpec(ImageFileOptions(filename_suffix="_labels.tif")),
        projected,
        "/analysis/fixture",
        FileManager({"memory": MemoryStorageBackend()}),
        context=SimpleNamespace(
            microscope_handler=SimpleNamespace(parser=SourceSchemaFilenameParser())
        ),
    )
    assert tuple(output.path for output in outputs) == (
        f"/analysis/{Path(source_path).stem}_labels.tif",
    )


@pytest.mark.parametrize("extension", (".tif", ".ome.tif"))
def test_component_addressed_source_stem_retains_typed_extension_without_parsing(
    extension, monkeypatch
):
    parser = SourceSchemaFilenameParser()
    authority = ParserBackedSourceStemAuthority(parser=parser)
    metadata = ImagePayloadMetadata(source_component_metadata=COMPONENTS)
    filename_identity = SourceImageIdentity(
        component_metadata={**COMPONENTS, "extension": extension}
    )

    def no_generated_path_parse(_path):
        raise AssertionError("A typed source identity must not be reparsed")

    monkeypatch.setattr(parser, "parse_filename", no_generated_path_parse)
    assert (
        authority.required_source_stem(metadata, filename_identity)
        == Path(f"image.ome.tif_s001_w1_z001_t001{extension}").stem
    )


def test_missing_materialization_extension_still_rejects():
    assert SourceImageIdentity().filename_extension is None
    authority = ParserBackedSourceStemAuthority(parser=SourceSchemaFilenameParser())
    with pytest.raises(ValueError, match="include an extension"):
        authority.required_source_stem(
            ImagePayloadMetadata(source_component_metadata=COMPONENTS)
        )


def test_source_identity_fill_preserves_authoritative_extension_and_other_metadata():
    identity = SourceImageIdentity(
        component_metadata={
            **COMPONENTS,
            "extension": ".ome.tif",
            "source_note": "retained",
        }
    )
    fallback = SourceImageIdentity(
        component_metadata={
            **COMPONENTS,
            "extension": ".tif",
            "foreign_note": "not identity",
        }
    )
    filled = identity.with_missing_from(fallback)
    assert filled.component_metadata == identity.component_metadata


def test_parsed_external_source_fills_declared_extension():
    identity = SourceImageIdentity(
        path="/input/image.ome.tif_s001_w1_z001_t001.ome.tif",
        component_metadata=COMPONENTS,
    )
    parsed = identity.with_parsed_path_components(SourceSchemaFilenameParser())
    assert parsed.component_metadata["extension"] == ".ome.tif"
    assert parsed.path == identity.path


@pytest.mark.parametrize("missing", ({}, {"extension": None}))
def test_source_identity_fills_only_explicitly_declared_extension(missing):
    identity = SourceImageIdentity(component_metadata={**COMPONENTS, **missing})
    fallback = SourceImageIdentity(
        component_metadata={"extension": ".ome.tif", "foreign_note": "not identity"}
    )
    assert identity.with_missing_from(fallback).component_metadata == {
        **COMPONENTS,
        "extension": ".ome.tif",
    }


def test_header_alias_does_not_hide_loaded_source_identity():
    header = SourceImageProvenance(source_image_names=("declared",))
    loaded = SourceImageProvenance(
        source_path="/input/source.tif", source_image_names=("physical",)
    )
    filled = VirtualWorkspaceImagePayloadProjection(
        persisted_metadata=ImagePayloadMetadata(source_provenance=header)
    ).metadata(ImagePayloadMetadata(source_provenance=loaded))
    assert filled.source_path == loaded.source_path
    assert filled.source_image_names == ("declared",)


@pytest.mark.parametrize(
    "declared",
    (
        SourceImageProvenance(source_component_metadata={"well": "A01"}),
        SourceImageProvenance(
            source_image_provenance_planes=SourceImageProvenancePlanes.from_contributor_components(
                paths=("/input/site-1.tif", "/input/site-2.tif"),
                component_metadata=({"site": "1"}, {"site": "2"}),
            )
        ),
    ),
)
def test_loaded_storage_identity_does_not_complete_declared_semantic_omissions(
    declared,
):
    loaded = SourceImageProvenance(
        source_path="/storage/mosaic.tif",
        source_component_metadata={**COMPONENTS, "extension": ".tif"},
    )
    projected = VirtualWorkspaceImagePayloadProjection(
        persisted_metadata=ImagePayloadMetadata(source_provenance=declared)
    ).metadata(ImagePayloadMetadata(source_provenance=loaded))
    assert projected.source_provenance == declared
    assert projected.source_path is None


def test_issue264_header_only_metadata_reaches_actual_image_writer():
    # Original259-02 scalar metadata has no extension; its loaded canonical
    # source path is still authoritative. No native request or original file.
    metadata = ImagePayloadMetadata(source_dtype="uint16")
    loaded = SourceImageProvenance(
        source_path="/plate/A01_s001_w1_z001_t001.tif",
        source_component_metadata={**COMPONENTS, "well": "A01"},
    )
    metadata = VirtualWorkspaceImagePayloadProjection(
        persisted_metadata=metadata
    ).metadata(ImagePayloadMetadata(source_provenance=loaded))
    filemanager = FileManager({"memory": MemoryStorageBackend()})
    outputs = materialization_outputs(
        MaterializationSpec(ImageFileOptions(filename_suffix="_labels.tif")),
        metadata.payload_with(np.ones((8, 8), dtype=np.uint16)),
        "/analysis/fixture",
        filemanager,
        context=SimpleNamespace(
            microscope_handler=SimpleNamespace(parser=SourceSchemaFilenameParser())
        ),
    )
    assert tuple(output.path for output in outputs) == (
        "/analysis/A01_s001_w1_z001_t001_labels.tif",
    )


@pytest.mark.parametrize("well", ("A01", "image.ome.tif"))
@pytest.mark.parametrize("extension", (".tif", ".ome.tif"))
@pytest.mark.parametrize("retain_declared_extension", (False, True))
@pytest.mark.parametrize("mode", tuple(ImagePayloadMetadataCompositionMode))
def test_real_source_schema_composition_to_named_output_and_image_materializer(
    well,
    extension,
    retain_declared_extension,
    mode,
):
    parser = SourceSchemaFilenameParser()
    filename = f"{well}_s001_w1_z001_t001{extension}"
    parsed = parser.parse_filename(filename)
    assert parsed.extension == extension
    assert parsed.components.wire_mapping()["well"] == well
    components = (
        parsed.wire_mapping()
        if retain_declared_extension
        else parsed.components.wire_mapping()
    )
    pixels = np.ones((8, 8), dtype=np.uint16)
    payload = ImagePayloadMetadata(
        source_path=f"/input/{filename}",
        source_component_metadata=components,
    ).payload_with(pixels)
    # This invokes the actual runtime composer which stamped all dotted well
    # suffixes before the named main/checkpoint writer saw the source identity.
    composed = ImagePayloadMetadata.compose((payload,), mode=mode)
    scalar = composed.for_leading_source_plane(0)
    identity = FunctionOutputIdentity.from_filename_metadata(
        parser, scalar
    )
    destination = replace(identity, filename_qualifier="fixture_image").filename(parser)
    assert destination == f"{well}_s001_w1_z001_t001_fixture_image{extension}"
    assert destination.count("_s001_w1_z001_t001") == 1
    assert identity.extension == extension
    assert composed.source_component_metadata.get("extension") == (
        extension if retain_declared_extension else None
    )

    authority = ParserBackedSourceStemAuthority(parser=parser)
    assert authority.path_parse_extensions(scalar) == (extension,)
    # Real image writer, including the source identity projected from that same
    # composed runtime plane. No Fake/DotParser or alternate scientific code.
    outputs = materialization_outputs(
        MaterializationSpec(ImageFileOptions(filename_suffix=".tif")),
        scalar.payload_with(pixels),
        "/analysis/fixture",
        FileManager({"memory": MemoryStorageBackend()}),
        context=SimpleNamespace(microscope_handler=SimpleNamespace(parser=parser)),
    )
    assert tuple(output.path for output in outputs) == (f"/analysis/{filename}",)


@pytest.mark.parametrize("extension", (".tif", ".ome.tif"))
def test_materializer_resolves_dotted_source_extension_only_through_real_parser(
    extension,
):
    parser = SourceSchemaFilenameParser()
    filename = f"image.ome.tif_s001_w1_z001_t001{extension}"
    metadata = ImagePayloadMetadata(
        source_path=f"/input/{filename}",
        source_component_metadata=parser.parse_filename(
            filename
        ).components.wire_mapping(),
    )
    assert ParserBackedSourceStemAuthority(parser=parser).path_parse_extensions(
        metadata
    ) == (extension,)


def test_materializer_does_not_invent_extension_for_unparsed_source():
    authority = ParserBackedSourceStemAuthority(parser=SourceSchemaFilenameParser())
    unknown = ImagePayloadMetadata(
        source_path="/input/physical.image.ome.tif",
        source_component_metadata=COMPONENTS,
    )
    assert authority.path_parse_extensions(unknown) == ()
    declared = unknown.with_source_component_metadata(
        {**COMPONENTS, "extension": ".ome.tif"}
    )
    assert authority.path_parse_extensions(declared) == (".ome.tif",)
