from types import MappingProxyType

import pytest

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
    }
