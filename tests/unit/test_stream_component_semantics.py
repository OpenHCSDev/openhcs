from types import MappingProxyType

import pytest

from openhcs.constants.constants import AllComponents
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import ORIGINAL_SOURCE_METADATA_FIELD
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.stream_component_semantics import (
    StreamExecutionAxisDomainProvider,
    StreamImagePayloadMetadataProjector,
    StreamSourceComponentMetadataItems,
    StreamViewerComponentMetadataProjector,
)
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.debug import NoOpDebugExecutionPolicy
from openhcs.core.orchestrator.worker_lanes import (
    WorkerAssignmentPlan,
    WorkerLaneExecutionContext,
)


def test_streaming_domain_spans_worker_lanes_without_mirroring_worker_identity():
    assignments = WorkerAssignmentPlan(
        {"worker_0": ["R02C05", "R04C04"], "worker_1": ["R04C02", "R07C02"]},
        {},
    )
    domains = []
    for slot in assignments.worker_assignments:
        lane = WorkerLaneExecutionContext(
            execution_id="execution",
            plate_id="plate",
            debug_execution_policy=NoOpDebugExecutionPolicy(),
            worker_slot=slot,
            worker_assignments=assignments.worker_assignments,
        )
        context = ProcessingContext()
        context.bind_execution_runtime(lane)
        assert context.execution_runtime is lane
        assert lane.worker_assignments is assignments.worker_assignments
        assert lane.owned_wells == tuple(assignments.worker_assignments[slot])
        provider = StreamExecutionAxisDomainProvider.build_for_component(
            context=context,
            component=StreamExecutionAxisDomainProvider.axis_component,
            metadata_roots=(),
        )
        domains.append(provider.domain_metadata_items())
    assert domains[0] == domains[1]
    assert {
        item[StreamExecutionAxisDomainProvider.axis_component] for item in domains[0]
    } == {
        "R02C05",
        "R04C04",
        "R04C02",
        "R07C02",
    }


def test_streaming_domain_requires_bound_execution():
    with pytest.raises(RuntimeError, match="execution_runtime"):
        StreamExecutionAxisDomainProvider.build_for_component(
            context=ProcessingContext(),
            component=StreamExecutionAxisDomainProvider.axis_component,
            metadata_roots=(),
        )


def test_stream_viewer_component_metadata_projector_keeps_only_declared_axes():
    projector = StreamViewerComponentMetadataProjector(
        ("well", "site", "channel", "timepoint")
    )

    projected = projector.project(
        {
            "well": "A01",
            "Site": "2",
            "ChannelNumber": "5",
            "extension": ".tif",
            "UndeclaredField": "ignored",
            ORIGINAL_SOURCE_METADATA_FIELD: MappingProxyType({"FrameNumber": "0011"}),
        }
    )

    assert projected == {
        "well": "A01",
        "site": 2,
        "channel": 5,
    }


def test_stream_source_component_metadata_items_project_viewer_metadata_by_index():
    source_metadata = StreamSourceComponentMetadataItems.from_values(
        (
            {
                "well": "A01",
                "site": "1",
                "channel": "2",
                ORIGINAL_SOURCE_METADATA_FIELD: MappingProxyType(
                    {"FrameNumber": "0011"}
                ),
            },
        )
    )

    viewer_metadata = source_metadata.viewer_source_metadata(("well", "channel"))

    assert viewer_metadata.metadata_by_index == (
        {
            "well": "A01",
            "channel": 2,
        },
    )


def test_stream_viewer_component_metadata_projector_requires_source_metadata():
    projector = StreamViewerComponentMetadataProjector(("well",))

    with pytest.raises(ValueError, match="requires source component metadata"):
        projector.project_required(index=3, metadata=None)


def test_stream_route_metadata_excludes_payload_local_plane_component() -> None:
    projector = StreamViewerComponentMetadataProjector.for_item_fields(
        ("well", "site", "channel", "z_index", "timepoint"),
        {
            "plane_axis": RuntimePlaneAxis.RUNTIME_SLICE.value,
            "plane_component_values": {"channel": ("1", "2")},
        },
    )

    assert projector.project_required(
        index=0,
        metadata={
            "well": "A49",
            "site": "1",
            "z_index": "1",
            "timepoint": "1",
        },
    ) == {
        "well": "A49",
        "site": 1,
        "z_index": 1,
        "timepoint": 1,
    }


@pytest.mark.parametrize("well", (1, "1", "A01"))
def test_stream_source_declared_domains_reuse_route_component_projection(well):
    source_metadata = StreamSourceComponentMetadataItems.from_values(
        (
            {
                "well": well,
                "Site": "02",
                "ChannelNumber": 5,
                "custom_axis": "unchanged",
                "undeclared": "omitted",
            },
            None,
        )
    )
    order = ("well", "site", "channel", "custom_axis")
    declared_items = source_metadata.domain_metadata_items(order)
    route_items = (
        StreamSourceComponentMetadataItems.from_values(source_metadata.values[:1])
        .viewer_source_metadata(order)
        .metadata_by_index
    )
    assert declared_items == route_items
    assert declared_items == (
        {"well": str(well), "site": 2, "channel": 5, "custom_axis": "unchanged"},
    )


def test_stream_image_metadata_projects_exact_source_spatial_domain_in_band():
    fields = StreamImagePayloadMetadataProjector.item_fields(
        ImagePayloadMetadata(
            source_spatial_domain=SourceSpatialDomain(
                origin_yx=(3, 5),
                source_shape_yx=(20, 30),
            )
        ),
        ("well", "site", "channel"),
    )

    assert fields == {
        "spatial_origin_yx": (3, 5),
        "source_spatial_shape_yx": (20, 30),
        "image_metadata": ImagePayloadMetadata(
            source_spatial_domain=SourceSpatialDomain((3, 5), (20, 30))
        ).to_viewer_image_metadata(),
    }


def _plane_metadata(axis, coordinates):
    return ImagePayloadMetadata(
        plane_axis=axis,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(
                f"/source/plane-{index}.tif" for index in range(len(coordinates))
            ),
            component_metadata=coordinates,
        ),
    )


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
@pytest.mark.parametrize("component", tuple(AllComponents))
def test_retained_image_plane_domain_does_not_require_artifact_storage_axes(
    axis, component
):
    metadata = _plane_metadata(
        axis,
        ({component.value: "1"}, {component.value: "2"}),
    )

    fields = StreamImagePayloadMetadataProjector.item_fields_for_plane_components(
        metadata, ()
    )

    assert fields["plane_axis"] == axis.value
    assert fields["plane_component_values"] == {component.value: ("1", "2")}
    assert (
        metadata.retained_plane_component_values() == fields["plane_component_values"]
    )


def test_projected_contributors_do_not_declare_a_retained_pixel_plane_domain():
    metadata = _plane_metadata(None, ({"channel": "1"}, {"channel": "2"}))

    assert metadata.retained_plane_component_values() == {}
    wire = StreamImagePayloadMetadataProjector.item_fields_for_plane_components(
        metadata, (AllComponents.CHANNEL,)
    )
    assert "plane_axis" not in wire
    assert "plane_component_values" not in wire
    assert (
        ImagePayloadMetadata.from_viewer_image_metadata(
            wire["image_metadata"]
        ).plane_axis
        is None
    )


@pytest.mark.parametrize("storage_components", [(), (AllComponents.CHANNEL,)])
def test_retained_plane_domain_rejects_multiple_varying_components(storage_components):
    metadata = _plane_metadata(
        RuntimePlaneAxis.SOURCE_BINDING,
        ({"channel": "1", "z_index": "1"}, {"channel": "2", "z_index": "2"}),
    )

    with pytest.raises(ValueError, match="multiple varying OpenHCS components"):
        StreamImagePayloadMetadataProjector.item_fields_for_plane_components(
            metadata, storage_components
        )


def test_singleton_plane_projection_remains_exactly_compiler_owned():
    metadata = _plane_metadata(
        RuntimePlaneAxis.RUNTIME_SLICE,
        ({"site": "3", "channel": "7"},),
    )

    assert StreamImagePayloadMetadataProjector.item_fields_for_plane_components(
        metadata, (AllComponents.SITE,)
    )["plane_component_values"] == {"site": ("3",)}
    with pytest.raises(ValueError, match="exactly one exact component"):
        StreamImagePayloadMetadataProjector.item_fields_for_plane_components(
            metadata, ()
        )


def test_singleton_plane_projection_rejects_ambiguous_compiler_components():
    metadata = _plane_metadata(
        RuntimePlaneAxis.RUNTIME_SLICE,
        ({"site": "3", "channel": "7"},),
    )

    with pytest.raises(ValueError, match="exactly one"):
        StreamImagePayloadMetadataProjector.item_fields_for_plane_components(
            metadata, (AllComponents.SITE, AllComponents.CHANNEL)
        )
