"""Focused source-image provenance projection regressions."""

import numpy as np
import pytest

from openhcs.constants.constants import AllComponents
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane,
    SourceImageIdentity,
    SourceImageProvenance,
    SourceImageProvenanceContributor,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy


def test_source_provenance_projects_scalar_image_set_identity() -> None:
    provenance = SourceImageProvenance(
        source_path="/input/A01_s001_w1.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
        },
    )
    policy = SourceImageSetIdentityPolicy(frozenset((AllComponents.CHANNEL,)))

    identities = provenance.image_set_identities(policy)

    assert tuple(identity.components for identity in identities) == (
        (("site", "1"), ("well", "A01")),
    )


def test_source_provenance_preserves_plane_positions_before_axis_deduplication() -> (
    None
):
    provenance = SourceImageProvenance(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/input/A01_s001_w1.tif",
                "/input/A01_s001_w2.tif",
            ),
            component_metadata=(
                {"well": "A01", "site": "1", "channel": "1"},
                {"well": "A01", "site": "1", "channel": "2"},
            ),
        ),
    )
    policy = SourceImageSetIdentityPolicy(frozenset((AllComponents.CHANNEL,)))

    plane_identities = provenance.image_set_plane_identities(policy)
    axis = provenance.image_set_axis(policy)

    assert len(plane_identities) == 2
    assert plane_identities[0] == plane_identities[1]
    assert axis == (plane_identities[0],)


def test_plane_coordinate_reads_preserve_runtime_scope_and_scalar_fallback() -> None:
    provenance = SourceImageProvenance(
        source_path="/input/fallback.tif",
        source_component_metadata={
            "well": "A01", "site": "99", "channel": "9", "timepoint": "3",
        },
        source_image_provenance_planes=SourceImageProvenancePlanes((
            SourceImageProvenanceContributor(
                SourceImageIdentity(component_metadata={"site": "88"}),
                source_image_name="Ancestor",
            ),
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity(component_metadata={"site": "1", "channel": "1"}),
                contributors=(SourceImageProvenanceContributor(
                    SourceImageIdentity(component_metadata={"site": "77"}),
                    source_image_name="DNA",
                ),),
            ),
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity(component_metadata={"site": "2", "channel": "2"}),
            ),
        )),
    )
    assert dict(provenance.component_metadata_for_plane(0)) == {
        "well": "A01", "site": "1", "channel": "1", "timepoint": "3",
    }
    assert provenance.varying_plane_component_values(tuple(AllComponents)) == {
        "site": ("1", "2"), "channel": ("1", "2"),
    }
    assert provenance.require_common_component_values(
        (AllComponents.WELL, AllComponents.TIMEPOINT)
    ) == ((AllComponents.WELL, "A01"), (AllComponents.TIMEPOINT, "3"))
    with pytest.raises(ValueError, match="'site' is not fixed"):
        provenance.require_common_component_values((AllComponents.SITE,))
    identities = provenance.image_set_plane_identities(
        SourceImageSetIdentityPolicy(frozenset((AllComponents.CHANNEL,)))
    )
    assert len(identities) == 2
    assert tuple(next(iter(value)).components for value in identities) == (
        (("site", "1"), ("timepoint", "3"), ("well", "A01")),
        (("site", "2"), ("timepoint", "3"), ("well", "A01")),
    )
    provenance.source_identity.component_metadata = {"well": "B02", "timepoint": "4"}
    assert provenance.require_common_component_values(
        (AllComponents.WELL, AllComponents.TIMEPOINT)
    ) == ((AllComponents.WELL, "B02"), (AllComponents.TIMEPOINT, "4"))


def test_source_provenance_axis_retains_distinct_image_sets() -> None:
    provenance = SourceImageProvenance(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/input/A01_s001_w3.tif",
                "/input/A01_s002_w3.tif",
            ),
            component_metadata=(
                {"well": "A01", "site": "1", "channel": "3"},
                {"well": "A01", "site": "2", "channel": "3"},
            ),
        ),
    )
    policy = SourceImageSetIdentityPolicy(frozenset((AllComponents.CHANNEL,)))

    axis = provenance.image_set_axis(policy)

    assert tuple(next(iter(identities)).components for identities in axis) == (
        (("site", "1"), ("well", "A01")),
        (("site", "2"), ("well", "A01")),
    )


def test_declared_source_projection_resolves_singleton_plane_contributor() -> None:
    source = ImagePayloadMetadata(
        source_path="/input/A01_DNA.tif",
        source_component_metadata={"well": "A01", "channel": "1"},
        source_image_names=("DNA",),
    ).payload_with(np.zeros((4, 5), dtype=np.float32))
    output = ImagePayloadMetadata(
        source_image_names=("OrigOverlay",),
    ).payload_with(np.ones((4, 5), dtype=np.float32))
    derived = image_payload_metadata(source).derive_payload(source, output)
    payload = ImagePayloadMetadata.compose((derived,)).payload_with(
        np.expand_dims(derived.data, axis=0)
    )

    projected_payload = image_payload_metadata(payload).project_declared_source_image(
        payload,
        "DNA",
    )
    projected = image_payload_metadata(projected_payload)

    assert projected.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert projected_payload.data.shape == (1, 4, 5)
    assert projected.source_provenance.represented_source_image_names == (
        "OrigOverlay",
        "DNA",
    )
    assert projected.source_image_provenance_planes.contributor_count == 1


def test_complete_source_identity_accepts_nested_contributor() -> None:
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes(
            (
                RuntimeSourceImageProvenancePlane(
                    contributors=(
                        SourceImageProvenanceContributor(
                            SourceImageIdentity(path="/input/A01_DNA.tif"),
                            source_image_name="DNA",
                        ),
                    )
                ),
            )
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    payload = metadata.payload_with(np.zeros((1, 4, 5), dtype=np.float32))

    assert metadata.has_complete_source_identity(
        payload,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=1,
        ),
    )
    assert metadata.source_image_paths == ("/input/A01_DNA.tif",)


def test_complete_source_identity_requires_multi_plane_axis_declaration() -> None:
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/A01_z001.tif", "/input/A01_z002.tif"),
            component_metadata=(
                {"well": "A01", "z_index": "1"},
                {"well": "A01", "z_index": "2"},
            ),
        )
    )
    payload = metadata.payload_with(np.zeros((2, 4, 5), dtype=np.float32))

    assert not metadata.has_complete_source_identity(
        payload,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=2,
        ),
    )


def test_derived_singleton_runtime_plane_retains_declared_source_name() -> None:
    source = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/A01_DNA.tif",),
            component_metadata=({"well": "A01", "channel": "1"},),
        ),
        source_image_names=("DNA",),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(np.zeros((1, 4, 5), dtype=np.float32))
    output = ImagePayloadMetadata(
        source_image_names=("OrigOverlay",),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(np.ones((1, 4, 5), dtype=np.float32))

    derived = image_payload_metadata(source).derive_payload(
        source,
        output,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=1,
        ),
    )
    projected_payload = image_payload_metadata(derived).project_declared_source_image(
        derived,
        "DNA",
    )
    projected = image_payload_metadata(projected_payload)

    assert projected.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert projected_payload.data.shape == (1, 4, 5)
    assert projected.source_provenance.represented_source_image_names == (
        "OrigOverlay",
        "DNA",
    )
    assert projected.source_image_provenance_planes.contributor_count == 1


def _repeated_source_alias_payload(
    *, data_plane_count: int = 7
) -> tuple[object, np.ndarray, np.ndarray]:
    pixels = np.stack(
        tuple(
            np.full((4, 5), plane_index + 1, dtype=np.float32)
            for plane_index in range(data_plane_count)
        )
    )
    mask = np.stack(
        tuple(
            np.full((4, 5), plane_index % 2 == 0, dtype=bool)
            for plane_index in range(data_plane_count)
        )
    )
    aliases = (
        "OrigDNA",
        "OrigER",
        "OrigRNA",
        "OrigActin",
        "OrigMito",
        "OrigGolgi",
        "OrigER",
    )
    metadata = ImagePayloadMetadata(
        source_image_names=aliases,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/input/plane_{index}.tif" for index in range(7)),
            component_metadata=tuple(
                {"well": "A01", "site": str(index + 1)} for index in range(7)
            ),
        ),
        source_plane_intensity_scales=(
            10.0,
            255.0,
            30.0,
            40.0,
            50.0,
            60.0,
            65535.0,
        ),
        source_plane_dtypes=(
            "uint8",
            "uint8",
            "uint8",
            "uint8",
            "uint8",
            "uint8",
            "uint16",
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    return metadata.payload_with(pixels, mask), pixels, mask


def test_declared_source_projection_selects_ordered_repeated_alias_planes() -> None:
    payload, pixels, mask = _repeated_source_alias_payload()

    projected_payload = image_payload_metadata(payload).project_declared_source_image(
        payload, "OrigER"
    )
    projected = image_payload_metadata(projected_payload)

    np.testing.assert_array_equal(
        image_payload_data(projected_payload),
        np.stack((pixels[1], pixels[6])),
    )
    np.testing.assert_array_equal(
        image_payload_mask(projected_payload),
        np.stack((mask[1], mask[6])),
    )
    assert projected.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert projected.source_plane_intensity_scales == (255.0, 65535.0)
    assert projected.source_plane_dtypes == ("uint8", "uint16")
    assert projected.source_image_names == ("OrigER", "OrigER")
    assert projected.source_image_provenance_planes.paths == (
        "/input/plane_1.tif",
        "/input/plane_6.tif",
    )
    assert tuple(
        dict(metadata or {})
        for metadata in projected.source_image_provenance_planes.component_metadata
    ) == (
        {"well": "A01", "site": "2"},
        {"well": "A01", "site": "7"},
    )


def test_declared_source_projection_drops_axis_for_single_selected_plane() -> None:
    payload, pixels, mask = _repeated_source_alias_payload()

    projected_payload = image_payload_metadata(payload).project_declared_source_image(
        payload, "OrigRNA"
    )
    projected = image_payload_metadata(projected_payload)

    np.testing.assert_array_equal(image_payload_data(projected_payload), pixels[2])
    np.testing.assert_array_equal(image_payload_mask(projected_payload), mask[2])
    assert projected.plane_axis is None
    assert projected.intensity_scale == 30.0
    assert projected.source_dtype == "uint8"
    assert projected.source_path == "/input/plane_2.tif"


def test_declared_source_projection_validates_runtime_plane_cardinality() -> None:
    payload, _, _ = _repeated_source_alias_payload(data_plane_count=6)

    with pytest.raises(
        ValueError,
        match="does not match its declared 'runtime_slice' axis of size 7",
    ):
        image_payload_metadata(payload).project_declared_source_image(
            payload,
            "OrigER",
        )


def test_removed_runtime_axis_retains_distinct_current_named_sources() -> None:
    original = SourceImageIdentity("/site1.tif", {"site": "1"})
    repeated = SourceImageIdentity("/previous.tif", {"site": "1"})
    repeated.path = original.path
    distinct = SourceImageIdentity("/site2.tif", {"site": "2"})
    planes = SourceImageProvenancePlanes(
        (
            RuntimeSourceImageProvenancePlane(original, source_image_name="DNA"),
            RuntimeSourceImageProvenancePlane(repeated, source_image_name="DNA"),
            RuntimeSourceImageProvenancePlane(distinct, source_image_name="DNA"),
            RuntimeSourceImageProvenancePlane(original, source_image_name="RNA"),
        )
    )
    contributors = planes.as_contributors()
    assert tuple(plane.path for plane in contributors.planes) == (
        "/site1.tif", "/site2.tif", "/site1.tif"
    )
    provenance = SourceImageProvenance.stack(
        (SourceImageProvenance(source_image_provenance_planes=contributors),)
    )
    with pytest.raises(ValueError, match="exactly one identity.*found 2"):
        provenance.for_source_image("DNA")
    assert provenance.for_source_image("RNA").source_image_provenance_planes.paths == (
        "/site1.tif",
    )

    repeated.component_metadata = {"site": "changed"}
    assert planes.as_contributors().contributor_count == 4
    unknown = RuntimeSourceImageProvenancePlane(source_image_name="Unknown")
    assert SourceImageProvenancePlanes((unknown, unknown)).as_contributors().contributor_count == 2


def test_factored_provenance_preserves_current_facts_and_independent_wire_occurrences():
    from openhcs.serialization.json import to_jsonable

    shared = SourceImageIdentity("birth.tif", {"source_metadata": {"site": "001"}})
    birth = shared.identity
    shared.path = "current.tif"
    equal_current = SourceImageIdentity("current.tif", shared.component_metadata)
    planes = SourceImageProvenancePlanes(
        (
            RuntimeSourceImageProvenancePlane(
                shared,
                (
                    SourceImageProvenanceContributor(
                        shared, source_image_name="original"
                    ),
                    SourceImageProvenanceContributor(
                        equal_current, source_image_name="rescaled"
                    ),
                ),
                "saved",
            ),
        )
    )
    wire = to_jsonable(planes)
    assert len(wire["identities"]) == 1
    assert shared.identity == birth and equal_current.identity != birth
    restored = SourceImageProvenancePlanes.from_mapping(wire)
    runtime = restored.planes[0]
    occurrences = (runtime, *runtime.contributors)
    assert tuple(p.source_image_name for p in occurrences) == (
        "saved",
        "original",
        "rescaled",
    )
    assert all(p.path == "current.tif" for p in occurrences)
    assert len({id(p.source_identity) for p in occurrences}) == 3
    assert len({id(p.component_metadata["source_metadata"]) for p in occurrences}) == 3
    runtime.component_metadata["source_metadata"]["site"] = "002"
    assert (
        runtime.contributors[0].component_metadata["source_metadata"]["site"] == "001"
    )
    assert shared.component_metadata["source_metadata"]["site"] == "001"
    historic = [
        {
            "path": "current.tif",
            "component_metadata": wire["identities"][0]["component_metadata"],
            "identity_kind": "runtime_plane",
            "source_image_name": "saved",
            "contributors": [
                {
                    "path": "current.tif",
                    "component_metadata": wire["identities"][0]["component_metadata"],
                    "identity_kind": "pixel_contributor",
                    "source_image_name": name,
                    "contributors": [],
                }
                for name in ("original", "rescaled")
            ],
        }
    ]
    assert to_jsonable(SourceImageProvenancePlanes.from_mapping(historic)) == wire


@pytest.mark.parametrize(
    "wire",
    (
        {"identities": [], "planes": [{"identity": 0, "identity_kind": "runtime_plane"}]},
        {"identities": [{}], "planes": [{"identity": True, "identity_kind": "runtime_plane"}]},
        {"identities": [{}], "planes": [{"identity": -1, "identity_kind": "runtime_plane"}]},
        {"identities": [{}], "planes": [{"identity": 0, "identity_kind": "unknown"}]},
        {"identities": [{"extra": "unreferenced"}], "planes": []},
        {"identities": [{}], "planes": [{"identity": 0, "path": "extra.tif"}]},
        {"identities": [], "planes": [], "extra": True},
    ),
)
def test_factored_provenance_rejects_invalid_identity_and_plane_declarations(wire):
    with pytest.raises((ValueError, TypeError)):
        SourceImageProvenancePlanes.from_mapping(wire)
