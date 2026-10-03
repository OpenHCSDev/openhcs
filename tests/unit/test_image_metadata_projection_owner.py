"""Semantic boundaries for the shared metadata projection owner."""

import gc
import pickle
import weakref
from dataclasses import Field, FrozenInstanceError, dataclass, field, fields

import cloudpickle
import numpy as np
import pytest

from openhcs.core.runtime_image_values import (
    ImageMetadataCarrier,
    ImagePayloadMetadataCarrier,
    ImageMetadataPayload,
    ImageMetadataProjection,
    ImagePayloadMetadata,
    LeadingPlaneAxisMetadataProjection,
    LeadingSourcePlaneMetadataProjection,
    MaskedImagePayload,
    SourcePlaneImageMetadataProjection,
    image_payload_data,
    image_payload_metadata,
    image_payload_metadata_projection,
    image_payload_slice_context,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane,
    SourceImageIdentity,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_metadata import DurableSourceMetadata
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.serialization.json import to_jsonable


class MutableTag(int):
    def __repr__(self):
        return self.tag

    def __str__(self):
        return self.tag


SUBTYPE_EVENTS = []


@dataclass
class CalibratedMetadata(ImagePayloadMetadata):
    calibration: float = 2.5
    declared_layout: object = field(init=False)

    def __post_init__(self, *values):
        super().__post_init__(*values)
        SUBTYPE_EVENTS.append(self)
        self.declared_layout = self.plane_axis
        self.constructor_attribute = "preserve actual constructor namespace"


class ObservedMetadata(ImagePayloadMetadata):
    def singleton_plane_projection(self):
        self.observed = True
        return super().singleton_plane_projection()


def stack_metadata(metadata_type=ImagePayloadMetadata):
    return metadata_type(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_dtype="float32",
        source_path="/input/original.tif",
        source_image_names=("DNA",),
    )


def test_slice_owner_exposes_stable_mutable_metadata_without_changing_pixels():
    data = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    original = stack_metadata().payload_with(data)
    sliced = image_payload_slice_context(original, data[1], 1)
    owner = image_payload_metadata_projection(sliced)
    assert isinstance(owner, ImageMetadataProjection)
    assert owner.read_value("plane_axis") is None
    assert np.shares_memory(image_payload_data(sliced), data)
    public = image_payload_metadata(sliced)
    assert public is image_payload_metadata(sliced)
    assert owner.materialize_metadata() is public
    public.source_dtype = "uint16"
    public.source_path = "/input/changed.tif"
    assert owner.read_value("source_dtype") == "uint16"
    assert owner.read_value("source_provenance").source_path == "/input/changed.tif"
    assert image_payload_metadata(original).source_path == "/input/original.tif"
    derived = owner.derive_fields(source_dtype="float64")
    assert derived.read_value("source_dtype") == "float64"
    assert public.source_dtype == "uint16"


def test_captured_siblings_keep_distinct_namespaces_and_source_epochs():
    original = stack_metadata()
    first = LeadingSourcePlaneMetadataProjection(original, 0).capture()
    second = LeadingSourcePlaneMetadataProjection(original, 1).capture()
    original.source_path = "/input/later.tif"
    assert first.read_value("source_provenance").source_path == "/input/original.tif"
    one = first.materialize_metadata()
    two = second.materialize_metadata()
    assert one is not two
    assert one.source_provenance is not two.source_provenance
    one.source_path = "/input/one.tif"
    assert two.source_path == "/input/original.tif"


@pytest.mark.parametrize("codec", (pickle, cloudpickle))
def test_private_transport_preserves_stored_birth_after_opaque_scalar_changes(codec):
    tag = MutableTag(1)
    tag.tag = "before"
    metadata = ImagePayloadMetadata(
        source_component_metadata=DurableSourceMetadata.from_mapping({"channel": tag})
    )
    owner = SourcePlaneImageMetadataProjection(metadata, 0).capture()
    birth = owner.read_value("source_provenance").equality_identity
    tag.tag = "after"
    restored = codec.loads(codec.dumps(owner))
    assert restored.read_value("source_provenance").equality_identity == birth
    public = restored.materialize_metadata()
    assert public.source_provenance.equality_identity == birth
    assert str(public.source_component_metadata["channel"]) == "after"
    reducer_state = owner.__reduce__()[1]
    assert all(not isinstance(value, Field) for value in reducer_state)


@pytest.mark.parametrize("public_api", (False, True))
def test_constructor_extensions_preserve_subclass_fields_and_one_public_lifecycle(
    public_api,
):
    metadata = stack_metadata(CalibratedMetadata)
    before = len(SUBTYPE_EVENTS)
    rule = LeadingSourcePlaneMetadataProjection(metadata, 0)
    result = rule.project() if public_api else rule.capture().materialize_metadata()
    assert type(result) is CalibratedMetadata
    assert result.calibration == 2.5
    # This init=False fact is born in the scalar-source constructor, before the
    # independent leading-axis capability clears the axis. Do not recompute it.
    assert result.declared_layout is RuntimePlaneAxis.RUNTIME_SLICE
    assert result.plane_axis is None
    assert result.constructor_attribute == "preserve actual constructor namespace"
    assert len(SUBTYPE_EVENTS) == before + 1
    assert set(to_jsonable(result)) == {member.name for member in fields(type(result))}


def test_public_nominal_hook_survives_capture_and_realization():
    original = stack_metadata(ObservedMetadata)
    owner = SourcePlaneImageMetadataProjection(original, 0).capture()
    actual = owner.materialize_metadata()
    assert type(actual) is ObservedMetadata
    actual.singleton_plane_projection()
    assert actual.observed


@pytest.mark.parametrize("payload_type", (ImageMetadataPayload, MaskedImagePayload))
def test_public_payload_schema_and_frozen_fields_remain(payload_type):
    data = np.ones((3, 4), dtype=np.float32)
    owner = ImagePayloadMetadata(source_dtype="float32").capture()
    payload = (
        payload_type.from_projection(data, owner)
        if payload_type is ImageMetadataPayload
        else payload_type.from_projection(data, np.ones(data.shape, dtype=bool), owner)
    )
    assert image_payload_metadata_projection(payload) is owner
    assert isinstance(payload.metadata, ImagePayloadMetadata)
    assert "metadata" in {member.name for member in fields(payload)}
    assert not payload_type.__abstractmethods__
    with pytest.raises(FrozenInstanceError):
        payload.metadata = ImagePayloadMetadata(source_dtype="uint16")
    replacement = payload.with_data(data.copy())
    assert image_payload_metadata_projection(replacement) is owner


def test_nominal_source_and_axis_guards_preserve_first_error_order(monkeypatch):
    metadata = stack_metadata()
    metadata.source_spatial_domain = SourceSpatialDomain(origin_yx=(1,))
    calls = []

    def fail_contributors(self):
        calls.append(self)
        raise RuntimeError("contributor first")

    monkeypatch.setattr(
        type(metadata.source_provenance),
        "with_runtime_planes_as_contributors",
        fail_contributors,
    )
    with pytest.raises(ValueError, match="spatial_origin_yx"):
        LeadingSourcePlaneMetadataProjection(metadata, 0).capture()
    assert calls == []
    with pytest.raises(RuntimeError, match="contributor first"):
        LeadingPlaneAxisMetadataProjection(metadata).capture()
    assert calls == [metadata.source_provenance]


def test_metadata_owner_does_not_keep_pixels_or_original_stack_alive():
    data = np.ones((2, 3, 4), dtype=np.float32)
    original = stack_metadata().payload_with(data)
    leaf = image_payload_slice_context(original, data[0], 0)
    owner = image_payload_metadata_projection(leaf)
    pixels = weakref.ref(data)
    del leaf, original, data
    gc.collect()
    assert pixels() is None
    assert owner.read_value("source_dtype") == "float32"


def test_runtime_slice_strategy_keeps_existing_payload_family():
    data = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    payload = stack_metadata().payload_with(data)
    assert RuntimeSliceProjection.slice_count_from_values((payload,)) == 2


class MetadataOnlyCarrier(ImageMetadataCarrier):
    __slots__ = ("_metadata_projection",)

    def __init__(self, owner):
        self.metadata = owner


def test_metadata_capability_does_not_make_a_carrier_an_image():
    carrier = MetadataOnlyCarrier(ImagePayloadMetadata().capture())
    assert not hasattr(carrier, "__dict__")
    assert isinstance(carrier, ImageMetadataCarrier)
    assert not isinstance(carrier, ImagePayloadMetadataCarrier)
    assert image_payload_data(carrier) is carrier
    assert image_payload_metadata_projection(carrier).has_values is False
    assert carrier.metadata is carrier.metadata
    empty = MetadataOnlyCarrier(None)
    assert empty.metadata is None
    assert empty.metadata_projection is None
    with pytest.raises(TypeError):
        ImagePayloadMetadataCarrier()


@pytest.mark.parametrize(
    "projection_type",
    (
        SourcePlaneImageMetadataProjection,
        LeadingSourcePlaneMetadataProjection,
    ),
)
def test_projection_observes_public_provenance_reassignments_before_capture(
    projection_type,
):
    metadata = stack_metadata()
    provenance = metadata.source_provenance
    old_birth = provenance.equality_identity
    provenance.source_image_names = ("changed-name",)
    provenance.source_identity = SourceImageIdentity("/input/changed-scalar.tif")
    provenance.source_image_provenance_planes = SourceImageProvenancePlanes(
        (
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity("/input/changed-plane.tif"),
                source_image_name="changed-plane-name",
            ),
        )
    )
    # Mutable live fields and the stored birth are distinct existing contracts.
    assert provenance.equality_identity == old_birth
    expected = projection_type(metadata, 0).project()
    first = projection_type(metadata, 0).capture().materialize_metadata()
    second = projection_type(metadata, 0).capture().materialize_metadata()
    assert (
        first.source_provenance.equality_identity
        == expected.source_provenance.equality_identity
    )
    assert first.source_path == "/input/changed-plane.tif"
    assert first.source_image_names == expected.source_image_names
    assert (
        first.source_image_provenance_planes.identity
        == expected.source_image_provenance_planes.identity
    )
    assert first.source_provenance is not provenance
    assert first.source_provenance is not second.source_provenance
    first.source_provenance.source_image_names = ("first-only",)
    first.source_provenance.source_identity.path = "/input/first-only.tif"
    first.source_provenance.source_image_provenance_planes = (
        SourceImageProvenancePlanes()
    )
    assert second.source_path == "/input/changed-plane.tif"
    assert second.source_image_names == expected.source_image_names
    assert (
        second.source_image_provenance_planes.identity
        == expected.source_image_provenance_planes.identity
    )


def test_projection_rebirth_observes_opaque_scalar_mutation_before_capture():
    tag = MutableTag(1)
    tag.tag = "old-birth"
    metadata = ImagePayloadMetadata(
        source_component_metadata=DurableSourceMetadata.from_mapping({"channel": tag}),
    )
    old_birth = metadata.source_provenance.equality_identity
    tag.tag = "new-birth"
    expected = SourcePlaneImageMetadataProjection(metadata, 0).project()
    owner = SourcePlaneImageMetadataProjection(metadata, 0).capture()
    assert metadata.source_provenance.equality_identity == old_birth
    assert owner.read_value("source_provenance").equality_identity != old_birth
    assert (
        owner.read_value("source_provenance").equality_identity
        == expected.source_provenance.equality_identity
    )


class SourceNormalizerMetadata(ImagePayloadMetadata):
    def normalize_source_provenance_fields(self):
        super().normalize_source_provenance_fields()
        self.normalizer_result = "nominal subtype hook"


def test_capture_preserves_nominal_source_normalizer_override():
    original = stack_metadata(SourceNormalizerMetadata)
    owner = LeadingSourcePlaneMetadataProjection(original, 0).capture()
    actual = owner.materialize_metadata()
    assert type(actual) is SourceNormalizerMetadata
    assert actual.normalizer_result == "nominal subtype hook"


class ComponentAliasMetadata(ImagePayloadMetadata):
    @property
    def source_component_metadata(self):
        self.component_alias_read = True
        return super().source_component_metadata


def test_actual_source_component_alias_hook_survives_normalization_and_capture():
    metadata = stack_metadata(ComponentAliasMetadata)
    assert metadata.component_alias_read
    actual = (
        LeadingSourcePlaneMetadataProjection(metadata, 0)
        .capture()
        .materialize_metadata()
    )
    assert type(actual) is ComponentAliasMetadata
    assert actual.component_alias_read
