"""Public identity and manifest laws for the shared metadata-only capability."""

from dataclasses import FrozenInstanceError, dataclass, fields, replace
import copyreg
import gc
import pickle
from pathlib import Path
from types import MappingProxyType
import weakref

import numpy as np
import pytest

from openhcs.constants.constants import VariableComponents
from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.runtime_image_values import (
    ImageMetadataCarrier,
    ImageMetadataPayload,
    ImageMetadataProjection,
    ImagePayloadMetadata,
    ImagePayloadMetadataCarrier,
    image_payload_data,
    image_payload_metadata_projection,
)
from openhcs.core.source_image_provenance import (
    SourceImageProvenance,
    SourceImageProvenancePlanes,
)
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
    FunctionOutputIdentityAuthority,
    FunctionOutputIdentityCache,
    FunctionOutputMetadataIdentityCacheKey,
    FunctionOutputPathRequest,
)
from openhcs.core.steps.function_output_manifest import ProducedOutputSemantics
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.serialization.json import to_jsonable

from tests.unit.test_function_outputs import function_step_plan


@dataclass
class CalibratedMetadata(ImagePayloadMetadata):
    calibration: float = 1.25

    def __post_init__(self, *values):
        super().__post_init__(*values)
        self.constructor_note = "actual subtype namespace"


def _metadata(metadata_type=ImagePayloadMetadata):
    return metadata_type(
        source_path="/input/A01_s001_w1_z001_t001.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
            "extension": ".tif",
        },
        source_dtype="float32",
    )


def _record(owner):
    return ProducedOutputSemantics.from_output(
        function_step_plan("Produce"),
        "/tmp/output/A01_s001_w1_z001_t001.tif",
        FunctionOutputIdentity(
            component_values={
                "well": "A01",
                "site": 1,
                "channel": 1,
                "z_index": 1,
                "timepoint": 1,
            },
            extension=".tif",
            source="actual public source declaration",
        ),
        output_context=AlignedImageSliceContext.main_flow(
            output_key="DNA",
            artifact_kind=ImageArtifactType.value,
        ),
        image_metadata=owner,
    )


def test_identity_reads_owner_without_public_namespace_and_preserves_cache_key(
    monkeypatch,
):
    parser = SourceSchemaFilenameParser()
    metadata = _metadata()
    expected = FunctionOutputIdentityAuthority.identity_from_metadata(parser, metadata)
    owner = metadata.capture()
    payload = ImageMetadataPayload.from_projection(
        np.zeros((3, 4), dtype=np.float32), owner
    )
    cache = FunctionOutputIdentityCache()
    request = FunctionOutputPathRequest(
        parser, Path("/tmp/output"), payload, None, identity_cache=cache
    )

    def unexpected_public_namespace(self):
        raise AssertionError("Identity query forced its public metadata namespace.")

    monkeypatch.setattr(
        ImageMetadataProjection, "materialize_metadata", unexpected_public_namespace
    )
    actual = FunctionOutputIdentityAuthority.identity(request)
    assert actual == expected
    assert FunctionOutputIdentityAuthority.identity(request) is actual
    assert list(cache.metadata_identities) == [
        FunctionOutputMetadataIdentityCacheKey(
            parser_id=id(parser),
            source_provenance_identity=owner.read_value(
                "source_provenance"
            ).equality_identity,
            fallback_identity_path=None,
            identity_components=(),
            input_aligned_output=False,
        )
    ]


def test_collapsed_contributors_keep_distinct_filename_and_semantic_components():
    metadata = ImagePayloadMetadata(
        source_provenance=SourceImageProvenance(
            source_component_metadata={
                "well": "A01",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
                "extension": ".tif",
            },
            source_image_provenance_planes=SourceImageProvenancePlanes.from_contributor_components(
                paths=(
                    "/input/A01_s001_w1_z001_t001.tif",
                    "/input/A01_s002_w1_z001_t001.tif",
                ),
                component_metadata=({"site": "1"}, {"site": "2"}),
            ),
        )
    )
    parser = SourceSchemaFilenameParser()
    kwargs = {"variable_components": (VariableComponents.SITE,)}
    public = FunctionOutputIdentityAuthority.identity_from_metadata(
        parser, metadata, **kwargs
    )
    projected = FunctionOutputIdentityAuthority.identity_from_metadata(
        parser, metadata.capture(), **kwargs
    )
    assert projected == public
    assert "site" not in projected.component_values
    assert projected.filename_values["site"] == 1


def test_missing_extension_error_is_preserved_for_owner():
    metadata = ImagePayloadMetadata(
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
        }
    )
    payload = ImageMetadataPayload.from_projection(np.zeros((3, 4)), metadata.capture())
    request = FunctionOutputPathRequest(
        SourceSchemaFilenameParser(), Path("/tmp/output"), payload, None
    )
    with pytest.raises(ValueError, match="no source path or extension"):
        FunctionOutputIdentityAuthority.identity(request)


def test_manifest_preserves_exact_owner_and_pass_through_without_namespace(monkeypatch):
    owner = _metadata().capture()
    payload = ImageMetadataPayload.from_projection(np.zeros((3, 4)), owner)
    record = _record(owner)
    assert record.metadata_projection is image_payload_metadata_projection(payload)

    def unexpected_public_namespace(self):
        raise AssertionError("Manifest lifecycle forced public metadata.")

    monkeypatch.setattr(
        ImageMetadataProjection, "materialize_metadata", unexpected_public_namespace
    )
    passed = record.passed_through(function_step_plan("Next", pipeline_position=4))
    assert passed.metadata_projection is owner
    assert passed.filename_address == record.filename_address
    assert passed.component_values == record.component_values
    assert (
        passed.producer_identity.step_scope_id != record.producer_identity.step_scope_id
    )


def test_manifest_has_metadata_capability_without_image_role_or_new_fields():
    record = _record(_metadata().capture())
    assert isinstance(record, ImageMetadataCarrier)
    assert not isinstance(record, ImagePayloadMetadataCarrier)
    assert not hasattr(record, "__dict__")
    assert not hasattr(record, "image_data")
    assert image_payload_data(record) is record
    names = tuple(member.name for member in fields(record))
    assert names == (
        "component_values",
        "extension",
        "source",
        "filename_component_values",
        "filename_qualifier",
        "producer_identity",
        "output_path",
        "relative_output_path",
        "image_metadata",
        "main_flow_plane_axis",
    )
    wire = to_jsonable(record)
    assert tuple(wire) == names
    assert "_metadata_projection" not in wire
    assert record.image_metadata is record.image_metadata


def test_image_carrier_still_requires_image_data():
    class MissingImageData(ImagePayloadMetadataCarrier):
        pass

    with pytest.raises(TypeError, match="image_data"):
        MissingImageData()
    payload = ImageMetadataPayload.from_projection(
        np.zeros((3, 4)), _metadata().capture()
    )
    assert isinstance(payload, ImageMetadataCarrier)
    assert isinstance(payload, ImagePayloadMetadataCarrier)
    assert image_payload_data(payload) is payload.data


def test_public_mutation_and_subtype_share_the_same_payload_namespace():
    owner = _metadata(CalibratedMetadata).capture()
    payload = ImageMetadataPayload.from_projection(np.zeros((3, 4)), owner)
    record = _record(owner)
    public = record.image_metadata
    assert type(public) is CalibratedMetadata
    assert public.constructor_note == "actual subtype namespace"
    assert public is payload.metadata
    public.calibration = 2.5
    public.source_path = "/input/changed.tif"
    assert owner.read_value("calibration") == 2.5
    assert owner.read_value("source_provenance").source_path == "/input/changed.tif"
    with pytest.raises(FrozenInstanceError):
        record.image_metadata = _metadata()


def test_public_source_mutation_keeps_original_cache_epoch_law():
    metadata = _metadata()
    owner = metadata.capture()
    record = _record(owner)
    parser = SourceSchemaFilenameParser()
    cache = FunctionOutputIdentityCache()
    first = FunctionOutputIdentityAuthority.identity_from_metadata_with_cache(
        parser, owner, identity_cache=cache
    )
    original_key = next(iter(cache.metadata_identities))
    record.image_metadata.source_path = "/input/changed.tif"
    second = FunctionOutputIdentityAuthority.identity_from_metadata_with_cache(
        parser, owner, identity_cache=cache
    )
    assert second == first
    assert len(cache.metadata_identities) == 2
    assert (
        original_key.source_provenance_identity
        != owner.read_value("source_provenance").equality_identity
    )


def test_manifest_never_retains_pixels_or_payload():
    pixels = np.ones((2, 3, 4), dtype=np.float32)
    owner = _metadata().capture()
    payload = ImageMetadataPayload.from_projection(pixels, owner)
    pixel_ref = weakref.ref(pixels)
    payload_ref = weakref.ref(payload)
    record = _record(image_payload_metadata_projection(payload))
    del pixels, payload
    gc.collect()
    assert pixel_ref() is None
    assert payload_ref() is None
    assert record.metadata_projection is owner


def test_replace_and_pickle_keep_original_public_dataclass_semantics(monkeypatch):
    record = _record(_metadata(CalibratedMetadata).capture())
    public = record.image_metadata
    copied = replace(record)
    assert copied.image_metadata is public
    # Other integrations can register a mappingproxy reducer globally. Exercise
    # the standard-pickle boundary independently of test collection order.
    monkeypatch.delitem(copyreg.dispatch_table, MappingProxyType, raising=False)
    # Standard pickle already rejects the public metadata mappingproxy.
    with pytest.raises(TypeError, match="mappingproxy"):
        pickle.dumps(record)
    absent = _record(None)
    restored = pickle.loads(pickle.dumps(absent))
    assert restored == absent
    assert restored.metadata_projection is None
    assert restored.image_metadata is None
    assert not hasattr(restored, "__dict__")


def test_contextualization_uses_record_owner_preserving_borrowed_pixels():
    owner = _metadata().capture()
    pixels = np.ones((3, 4), dtype=np.float32)
    record = _record(owner)
    contextualized = record.contextualize_image_payload(pixels)
    assert image_payload_data(contextualized) is pixels
    projected = image_payload_metadata_projection(contextualized)
    assert (
        projected.read_value("source_provenance").source_component_metadata["site"]
        == "1"
    )
    assert (
        owner.read_value("source_provenance").source_component_metadata["site"] == "1"
    )


def test_absent_manifest_metadata_stays_absent():
    record = _record(None)
    assert record.metadata_projection is None
    assert record.image_metadata is None
    assert (
        record.passed_through(
            function_step_plan("Next", pipeline_position=4)
        ).image_metadata
        is None
    )
