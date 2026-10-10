"""Physical source-plane projection preserves composition and mutable isolation."""

from dataclasses import fields

import numpy as np
import pytest

from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadSliceProjector,
    ImageUnitIntervalIntensityMetadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane,
    SourceImageIdentity,
    SourceImageProvenanceContributor,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.payload_axes import PayloadAxes
from openhcs.core.axes import ColourAxis


def _metadata(axis, channel_axis):
    return ImagePayloadMetadata(
        source_path="/tmp/parent.tif",
        source_component_metadata={"well": "A01", "extension": ".tif"},
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/tmp/first.tif", "/tmp/second.tif"),
            component_metadata=({"site": "1"}, {"site": "2"}),
        ),
        intensity_scale=255.0,
        source_dtype="uint8",
        source_plane_intensity_scales=(255.0, 65535.0),
        source_plane_dtypes=("uint8", "uint16"),
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(
            scale=255, source_plane_scales=(255, 65535)
        ),
        source_image_names=("DNA", "RNA"),
        axes=PayloadAxes.colour_samples(channel_axis),
        plane_axis=axis,
    )


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
@pytest.mark.parametrize("channel_axis", (None, 1, 3, -1))
@pytest.mark.parametrize("plane", (0, 1))
def test_physical_projection_agrees_with_separate_semantic_operations(
    axis, channel_axis, plane
):
    metadata = _metadata(axis, channel_axis)
    sequential = metadata.for_source_plane(plane).without_leading_plane_axis()
    projected = metadata.for_leading_source_plane(plane)
    for member in fields(ImagePayloadMetadata):
        assert getattr(projected, member.name) == getattr(sequential, member.name)
    assert projected.source_path == ("/tmp/first.tif", "/tmp/second.tif")[plane]
    assert projected.source_component_metadata["well"] == "A01"
    assert projected.source_component_metadata["site"] == str(plane + 1)
    assert projected.unit_interval_intensity.scale == (255, 65535)[plane]
    assert projected.source_plane_intensity_scales == ()
    assert projected.source_plane_dtypes == ()
    assert projected.plane_axis is None
    projected.source_provenance.source_identity.path = "/tmp/changed.tif"
    assert metadata.source_path == "/tmp/parent.tif"
    assert metadata.source_image_provenance_planes.paths[plane] != "/tmp/changed.tif"


def test_physical_projection_constructs_only_the_final_metadata(monkeypatch):
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    calls = []
    original = ImagePayloadMetadata.__post_init__

    def observe(self, *values):
        calls.append(self)
        original(self, *values)

    monkeypatch.setattr(ImagePayloadMetadata, "__post_init__", observe)
    projected = metadata.for_leading_source_plane(1)
    assert calls == [projected]


def test_physical_projection_rejects_leading_channel_axis():
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, 0)
    with pytest.raises(ValueError, match="both plane and"):
        metadata.for_leading_source_plane(1)


def test_physical_projection_requires_declared_plane_axis():
    metadata = _metadata(None, None)
    with pytest.raises(ValueError, match="declared plane axis"):
        metadata.for_leading_source_plane(1)


@pytest.mark.parametrize("channel_axis", (False, True, "1", 1.5))
def test_declared_axis_positions_must_be_int(channel_axis):
    with pytest.raises(TypeError, match="positions must be int"):
        PayloadAxes.colour_samples(channel_axis)


def test_physical_projection_preserves_invalid_mutated_plane_error():
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    metadata.plane_axis = "invalid-axis"
    with pytest.raises(ValueError):
        metadata.for_source_plane(1).without_leading_plane_axis()
    with pytest.raises(ValueError):
        metadata.for_leading_source_plane(1)


def test_projection_preserves_selected_spacing_and_nested_contributors():
    contributor = SourceImageProvenanceContributor(
        SourceImageIdentity("/tmp/contributor.tif", {"site": "3"}),
        source_image_name="Original",
    )
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_image_provenance_planes=SourceImageProvenancePlanes(
            (
                RuntimeSourceImageProvenancePlane(
                    SourceImageIdentity(
                        "/tmp/selected.tif",
                        {"OpenHCSSourceVoxelSpacingZYX": "4,2,1"},
                    ),
                    contributors=(contributor,),
                    source_image_name="DNA",
                ),
            )
        ),
    )
    sequential = metadata.for_source_plane(0).without_leading_plane_axis()
    projected = metadata.for_leading_source_plane(0)
    for member in fields(ImagePayloadMetadata):
        assert getattr(projected, member.name) == getattr(sequential, member.name)
    assert projected.source_image_provenance_planes.planes == (contributor,)


def test_projection_observes_mask_and_metadata_mutation():
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    mask = np.ones((2, 3, 4), dtype=bool)
    projector = ImagePayloadSliceProjector(mask, metadata)
    data = np.zeros((3, 4))
    first = projector.payload_for_slice(data, 1)
    assert first.metadata.intensity_scale == 65535.0
    metadata.source_plane_intensity_scales = (1.0, 2.0)
    mask[1, 0, 0] = False
    second = projector.payload_for_slice(data, 1)
    assert second.metadata.intensity_scale == 2.0
    assert not second.mask[0, 0]
    mask.resize((2, 2, 6), refcheck=False)
    with pytest.raises(ValueError, match="cannot be projected"):
        projector.payload_for_slice(data, 1)


def _metadata_with_observed_plane_fields(*, proof_raises=False):
    events = []

    class ObservedInt(int):
        def __int__(self):
            events.append("proof-int")
            if proof_raises:
                raise RuntimeError("proof conversion observed")
            return 1

    class ObservedTuple(tuple):
        def __getitem__(self, index):
            events.append("intensity-getitem")
            return super().__getitem__(index)

    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_plane_intensity_scales=ObservedTuple((2.0,)),
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(
            source_plane_scales=(ObservedInt(1),)
        ),
    )
    return metadata, events


def test_plane_proof_failure_precedes_leading_channel_guard():
    metadata, events = _metadata_with_observed_plane_fields(proof_raises=True)
    metadata.axes = PayloadAxes.colour_samples(0)
    with pytest.raises(RuntimeError, match="proof conversion observed"):
        metadata.for_leading_source_plane(0)
    assert events == ["intensity-getitem", "proof-int"]


def test_plane_field_effects_precede_leading_channel_guard():
    metadata, events = _metadata_with_observed_plane_fields()
    metadata.axes = PayloadAxes.colour_samples(0)
    with pytest.raises(ValueError, match="both plane and"):
        metadata.for_leading_source_plane(0)
    assert events == ["intensity-getitem", "proof-int"]


def test_source_plane_preserves_intensity_then_proof_effect_order():
    metadata, events = _metadata_with_observed_plane_fields()
    projected = metadata.for_source_plane(0)
    assert events == ["intensity-getitem", "proof-int"]
    assert projected.intensity_scale == 2.0
    assert projected.unit_interval_intensity.scale == 1


@pytest.mark.parametrize(
    "operation,channel_axis,broken,error,message",
    (
        ("for_leading_source_plane", 0, "domain", ValueError, "spatial_origin_yx"),
        ("for_leading_source_plane", 0, "spacing", ValueError, "finite and positive"),
        (
            "for_leading_source_plane",
            0,
            "spacing-value",
            AttributeError,
            "with_missing_from",
        ),
        ("for_leading_source_plane", 0, "plane", ValueError, "invalid-axis"),
        (
            "without_leading_plane_axis",
            0,
            "domain",
            ValueError,
            "both plane and",
        ),
        (
            "without_leading_plane_axis",
            0,
            "spacing",
            ValueError,
            "both plane and",
        ),
        (
            "without_leading_plane_axis",
            0,
            "spacing-value",
            ValueError,
            "both plane and",
        ),
        (
            "without_leading_plane_axis",
            0,
            "plane",
            ValueError,
            "both plane and",
        ),
    ),
)
def test_projection_preserves_cross_invalid_constructor_guard_order(
    operation, channel_axis, broken, error, message
):
    metadata = ImagePayloadMetadata(
        source_path="/tmp/source.tif",
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    metadata.axes = PayloadAxes.colour_samples(channel_axis)
    if broken == "domain":
        metadata.source_spatial_domain = SourceSpatialDomain(origin_yx=(1,))
    elif broken == "spacing":
        metadata.source_component_metadata = {"OpenHCSSourceVoxelSpacingZYX": "0,1,1"}
    elif broken == "spacing-value":
        metadata.source_voxel_spacing = None
    else:
        metadata.plane_axis = "invalid-axis"
    with pytest.raises(error, match=message):
        if operation == "without_leading_plane_axis":
            metadata.without_leading_plane_axis()
        else:
            getattr(metadata, operation)(0)


def test_missing_leading_axis_precedes_plane_field_effects():
    metadata, events = _metadata_with_observed_plane_fields(proof_raises=True)
    metadata.plane_axis = None
    metadata.axes = PayloadAxes.colour_samples(0)
    with pytest.raises(ValueError, match="requires a declared plane axis"):
        metadata.for_leading_source_plane(0)
    assert events == []


def test_projection_spacing_failure_precedes_other_invalid_source_fields():
    metadata = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE)
    metadata.source_component_metadata = {"OpenHCSSourceVoxelSpacingZYX": "0,1,1"}
    metadata.source_spatial_domain = SourceSpatialDomain(origin_yx=(1,))
    metadata.plane_axis = "invalid-axis"
    with pytest.raises(ValueError, match="finite and positive"):
        metadata.for_leading_source_plane(0)


@pytest.mark.parametrize(
    "operation,normalization_axes",
    (
        ("without_leading_plane_axis", (RuntimePlaneAxis.RUNTIME_SLICE, None)),
        (
            "for_leading_source_plane",
            (RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.RUNTIME_SLICE, None),
        ),
    ),
)
def test_projection_normalizes_owned_metadata_at_each_historical_phase(
    monkeypatch, operation, normalization_axes
):
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, 2)
    input_provenance = metadata.source_provenance
    input_proof = metadata.unit_interval_intensity
    births = []
    phases = []
    original_constructor = ImagePayloadMetadata.__post_init__
    original_normalize = ImagePayloadMetadata.normalize_metadata_fields

    def observe_constructor(self, *values):
        births.append((self, self.plane_axis, self.axes.position_of(ColourAxis)))
        original_constructor(self, *values)

    def observe_normalization(self):
        phases.append((self, self.plane_axis, self.axes.position_of(ColourAxis)))
        original_normalize(self)

    monkeypatch.setattr(ImagePayloadMetadata, "__post_init__", observe_constructor)
    monkeypatch.setattr(
        ImagePayloadMetadata, "normalize_metadata_fields", observe_normalization
    )
    projected = (
        metadata.without_leading_plane_axis()
        if operation == "without_leading_plane_axis"
        else metadata.for_leading_source_plane(1)
    )

    assert births == [(projected, RuntimePlaneAxis.RUNTIME_SLICE, 2)]
    assert tuple(axis for _, axis, _ in phases) == normalization_axes
    assert all(owner is projected for owner, _, _ in phases)
    assert tuple(channel for _, _, channel in phases) == (2,) * (
        len(normalization_axes) - 1
    ) + (1,)
    assert projected is not metadata
    assert metadata.source_provenance is input_provenance
    assert metadata.unit_interval_intensity is input_proof
    assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert metadata.axis_position(ColourAxis) == 2
    assert metadata.source_plane_intensity_scales == (255.0, 65535.0)
    assert projected.source_provenance is not input_provenance
    assert projected.unit_interval_intensity is not input_proof


@pytest.mark.parametrize("combined", (False, True))
def test_projection_preserves_contributor_derivation_constructor_error_order(
    monkeypatch, combined
):
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    invalid_domain = SourceSpatialDomain(origin_yx=(1,))
    metadata.source_spatial_domain = invalid_domain
    provenance = metadata.source_provenance
    calls = []

    def fail_contributors(self):
        calls.append(self)
        raise RuntimeError("contributor derivation observed")

    monkeypatch.setattr(
        type(provenance), "with_runtime_planes_as_contributors", fail_contributors
    )
    if combined:
        with pytest.raises(ValueError, match="spatial_origin_yx"):
            metadata.for_leading_source_plane(1)
        assert calls == []
    else:
        with pytest.raises(RuntimeError, match="contributor derivation observed"):
            metadata.without_leading_plane_axis()
        assert calls == [provenance]
    assert metadata.source_provenance is provenance
    assert metadata.source_spatial_domain is invalid_domain
    assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert metadata.source_plane_intensity_scales == (255.0, 65535.0)


@pytest.mark.parametrize("combined", (False, True))
def test_failed_owned_axis_transform_does_not_mutate_source(monkeypatch, combined):
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, 2)
    provenance = metadata.source_provenance
    proof = metadata.unit_interval_intensity

    def fail_proof(self):
        raise RuntimeError("axis proof derivation observed")

    monkeypatch.setattr(
        ImageUnitIntervalIntensityMetadata, "without_source_planes", fail_proof
    )
    with pytest.raises(RuntimeError, match="axis proof derivation observed"):
        if combined:
            metadata.for_leading_source_plane(1)
        else:
            metadata.without_leading_plane_axis()
    assert metadata.source_provenance is provenance
    assert metadata.unit_interval_intensity is proof
    assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert metadata.axis_position(ColourAxis) == 2
    assert metadata.source_plane_intensity_scales == (255.0, 65535.0)
    assert metadata.source_plane_dtypes == ("uint8", "uint16")


@pytest.mark.parametrize(
    "plane_index,expected_scale",
    ((None, 255), (-1, 255), (0, 255), (1, 65535), (2, 255)),
)
def test_owned_proof_projection_preserves_scalar_fallback_and_axis_removal(
    plane_index, expected_scale
):
    proof = ImageUnitIntervalIntensityMetadata(
        scale=255, source_plane_scales=(None, 65535)
    )
    metadata = ImagePayloadMetadata(unit_interval_intensity=proof)
    projected = metadata.project_intensity_proof(plane_index)
    assert projected is not proof
    assert projected.scale == expected_scale
    assert projected.source_plane_scales == ()
    assert metadata.unit_interval_intensity is proof
    assert proof.source_plane_scales == (None, 65535)
    if plane_index is not None:
        assert metadata.unit_interval_intensity_scale_for_source_plane(plane_index) == (
            expected_scale
        )


@pytest.mark.parametrize("plane_index", (None, 0, 1))
def test_owned_proof_projection_observes_absence_and_live_replacement(plane_index):
    metadata = ImagePayloadMetadata(intensity_scale=255)
    assert metadata.project_intensity_proof(plane_index) is None
    if plane_index is not None:
        assert (
            metadata.unit_interval_intensity_scale_for_source_plane(plane_index) is None
        )
    proof = ImageUnitIntervalIntensityMetadata(scale=7, source_plane_scales=(11, 13))
    metadata.unit_interval_intensity = proof
    assert metadata.project_intensity_proof(plane_index).scale == (
        7 if plane_index is None else (11, 13)[plane_index]
    )
    metadata.unit_interval_intensity = None
    assert metadata.project_intensity_proof(plane_index) is None


def test_quantization_queries_preserve_integer_conversion_and_fallback_identity():
    calls = []

    class ObservedInt(int):
        def __int__(self):
            calls.append(self)
            return super().__int__()

    scalar = ObservedInt(255)
    plane = ObservedInt(65535)
    metadata = ImagePayloadMetadata(
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(
            scale=scalar, source_plane_scales=(None, plane)
        )
    )
    assert metadata.unit_interval_intensity_scale_for_source_plane(0) is scalar
    assert metadata.unit_interval_intensity_scale_for_source_plane(-1) is scalar
    assert calls == []
    assert metadata.unit_interval_intensity_scale_for_source_plane(1) == 65535
    assert calls == [plane]
    calls.clear()
    assert metadata.project_intensity_proof(1).scale == 65535
    assert calls == [plane]
    assert metadata.project_intensity_proof(None).scale is scalar
    assert calls == [plane]
