"""Selection and aggregation own different source-projection contracts."""

from dataclasses import dataclass, field, replace

import numpy as np
import pytest

from openhcs.core.projected_image_output import (
    SourcePlaneSelectionImageOutput,
    SourceProjectedImageOutput,
)
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes


@dataclass(frozen=True)
class AggregateField(SourceProjectedImageOutput):
    data: RuntimeArrayData

    def with_data(self, data: RuntimeArrayData) -> "AggregateField":
        return replace(self, data=data)

    def resolve_source_context(self, source, projection):
        assert projection is not None and projection.plane_index is None
        assert projection.axis_size == source.shape[0]
        return source.metadata.collapse_leading_plane_axis().payload_with(
            self.data, None
        )


def observation_source():
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/synthetic/observation_{i}.tif" for i in range(3)),
            component_metadata=tuple(
                {"well": "A01", "site": str(i), "channel": "1"} for i in range(3)
            ),
        ),
    )
    return metadata.payload_with(np.zeros((3, 3, 4), dtype=np.float32))


@pytest.mark.parametrize("shape", [(3, 4), (2, 3, 4)])
def test_aggregate_member_is_not_required_to_select_source_planes(shape):
    field = AggregateField(np.full(shape, 1.25, dtype=np.float32))
    assert field.shape == shape
    converted = field.with_data(np.asarray(field).astype(np.float64))
    assert converted.dtype == np.float64
    np.testing.assert_array_equal(np.asarray(converted), np.asarray(field))


def test_aggregate_context_retains_all_contributors_without_a_pixel_axis():
    source = observation_source()
    field = AggregateField(np.full((3, 4), 1.25, dtype=np.float32))
    result = field.resolve_source_context(
        source,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=3
        ),
    )
    metadata = result.metadata
    assert result.shape == (3, 4)
    assert metadata.plane_axis is None
    assert metadata.source_image_provenance_planes.contributor_count == 3
    assert metadata.source_image_paths == source.metadata.source_image_paths
    np.testing.assert_array_equal(np.asarray(result), np.asarray(field))


class ProjectionAudit:
    def resolve_source_context(self, source, projection):
        self.calls.append("before")
        result = super().resolve_source_context(source, projection)
        self.calls.append("after")
        return result


@dataclass(frozen=True)
class AuditedSelection(ProjectionAudit, SourcePlaneSelectionImageOutput):
    data: RuntimeArrayData
    source_indices: tuple[int, ...]
    calls: list[str] = field(default_factory=list, compare=False)

    def selected_source_plane_indices(self):
        return self.source_indices

    def with_data(self, data):
        return replace(self, data=data)


@pytest.mark.parametrize("indices", [(2,), (2, 0)])
def test_independent_selection_member_composes_the_shared_projection(indices):
    source = observation_source()
    data = np.asarray(source)[list(indices)] + 0.25
    output = AuditedSelection(data, indices)
    result = output.resolve_source_context(
        source,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=3
        ),
    )
    metadata = result.metadata
    paths = source.metadata.source_image_paths
    assert metadata.source_image_paths == tuple(paths[i] for i in indices)
    assert output.calls == ["before", "after"]
    if len(indices) == 1:
        assert result.shape == (3, 4)
        assert metadata.plane_axis is None
        np.testing.assert_array_equal(np.asarray(result), data[0])
    else:
        assert result.shape == (2, 3, 4)
        assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
        np.testing.assert_array_equal(np.asarray(result), data)
