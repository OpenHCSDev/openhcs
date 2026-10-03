"""Real loader/workspace/format consumers retain one metadata owner lifecycle."""

from dataclasses import dataclass, fields

import numpy as np
import pytest

from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.image_file_serialization import (
    ImageFileFormat,
    ImageFileSourceMetadata,
)
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_image_values import (
    ImageMetadataProjection,
    ImagePayloadMetadata,
    ImageUnitIntervalIntensityMetadata,
    image_payload_data,
    image_payload_metadata,
    image_payload_metadata_projection,
)
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenance,
)
from openhcs.core.source_metadata import DurableSourceMetadata, SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceImagePayloadProjection,
)
from openhcs.serialization.json import to_jsonable


@dataclass
class CalibratedMetadata(ImagePayloadMetadata):
    calibration: float = 3.0


def test_loader_owner_preserves_virtual_identity_and_public_mutable_contract():
    image = np.arange(12, dtype=np.uint16).reshape(3, 4)
    context = ImagePayloadSourceMetadataContext(
        SourceImageIdentity(
            "/virtual/A01_s001_w1_z001_t001.tif",
            DurableSourceMetadata.from_mapping({"well": "A01", "channel": "1"}),
        )
    )
    owner = context.metadata_projection(image)
    assert isinstance(owner, ImageMetadataProjection)
    actual = owner.materialize_metadata()
    assert type(actual) is ImagePayloadMetadata
    assert actual.source_path == context.source_path
    assert actual.source_dtype == "uint16"
    assert dict(actual.source_component_metadata) == {"well": "A01", "channel": "1"}
    assert actual.source_spatial_shape_yx == image.shape
    assert to_jsonable(context.metadata(image)) == to_jsonable(actual)
    actual.source_dtype = "float32"
    assert owner.read_value("source_dtype") == "float32"


def test_workspace_owner_preserves_declared_omissions_alias_and_mutation():
    loaded = ImagePayloadMetadata(
        source_path="/storage/raw.tif",
        source_spatial_domain=SourceSpatialDomain((1, 2), (12, 14)),
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.75)),
        source_dtype="float32",
    )
    persisted = CalibratedMetadata(
        source_provenance=SourceImageProvenance(
            source_component_metadata={"well": "A01"},
            source_image_names=("declared",),
        ),
    )
    # These are live public facts despite the provenance's stored birth identity.
    persisted.source_provenance.source_image_names = ("changed-before-apply",)
    projection = VirtualWorkspaceImagePayloadProjection(persisted_metadata=persisted)
    owner = projection.metadata_projection(loaded)
    expected = projection.metadata(loaded)
    actual = owner.materialize_metadata()
    assert type(actual) is CalibratedMetadata
    assert actual.calibration == 3.0
    assert actual.source_path is None
    assert actual.source_image_names == ("changed-before-apply",)
    assert to_jsonable(actual) == to_jsonable(expected)
    actual.source_image_names = ("one-output-only",)
    assert persisted.source_image_names == ("changed-before-apply",)
    aliased = VirtualWorkspaceImagePayloadProjection(
        persisted_metadata=persisted, source_alias="DNA"
    ).apply(loaded.payload_with(np.ones((3, 4), dtype=np.float32)))
    assert image_payload_metadata(aliased).source_image_names == ("DNA",)
    assert image_payload_data(aliased).shape == (3, 4)


@pytest.mark.parametrize("values_preserved", (False, True))
def test_format_owner_retains_subtype_schema_and_native_value_facts(values_preserved):
    metadata = CalibratedMetadata(
        source_path="/input/image.tif",
        source_dtype="float32",
        intensity_scale=1.0,
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(255),
        physical_border_edges_yx=(True, False, False, True),
        mask_defines_border=True,
    )
    header = ImageFileSourceMetadata(np.dtype("uint8"), 255)
    owner = header.project_image_metadata_projection(
        metadata, values_preserved=values_preserved
    )
    actual = owner.materialize_metadata()
    public = header.project_image_metadata(metadata, values_preserved=values_preserved)
    assert type(actual) is type(public) is CalibratedMetadata
    assert {member.name for member in fields(actual)} == set(to_jsonable(actual))
    assert to_jsonable(actual) == to_jsonable(public)
    assert actual.source_dtype == "uint8"
    assert actual.intensity_scale == 255
    assert actual.source_path == metadata.source_path
    if not values_preserved:
        assert actual.unit_interval_intensity.scale is None
        assert actual.physical_border_edges_yx is None
        assert actual.mask_defines_border is None
    assert metadata.source_dtype == "float32"


def test_actual_saved_tiff_owner_and_public_contract_share_native_facts(tmp_path):
    data = np.arange(12, dtype=np.uint16).reshape(3, 4)
    payload = ImagePayloadMetadata(
        source_path="/source/virtual.tif", source_dtype="uint16"
    ).payload_with(data)
    path = tmp_path / "output.tif"
    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, payload)
    owner = image_format.persisted_metadata_projection(path, payload)
    assert to_jsonable(owner.materialize_metadata()) == to_jsonable(
        image_format.persisted_metadata(path, payload)
    )
    np.testing.assert_array_equal(image_format.read(path), data)


def test_named_image_artifact_projects_owned_alias_without_changing_pixels():
    data = np.ones((3, 4), dtype=np.float32)
    original = ImagePayloadMetadata(
        source_path="/input/image.tif", source_image_names=("DNA",)
    ).payload_with(data)
    named = ImageArtifactType.normalize_runtime_payload("DerivedDNA", original)
    owner = image_payload_metadata_projection(named)
    assert owner.read_value("source_provenance").source_image_names == ("DerivedDNA",)
    assert image_payload_data(named) is data
    assert image_payload_metadata(original).source_image_names == ("DNA",)
    public = image_payload_metadata(named)
    assert public is image_payload_metadata(named)
    public.source_path = "/changed/output.tif"
    assert owner.read_value("source_provenance").source_path == "/changed/output.tif"
    assert image_payload_metadata(original).source_path == "/input/image.tif"
