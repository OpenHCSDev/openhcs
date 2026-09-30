"""Exercise real output contextualization, not just the fixture's raw return.

These source controls do not prove BioFormats discovery, compilation, native
execution, saved CSV/ROI publication, an installed MCP journey, or biology.
"""

import importlib.util
from pathlib import Path
import sys

import numpy as np
import pytest

from openhcs.constants import AllComponents
from openhcs.core.artifacts import ArtifactOutputPlan, ArtifactSpec, ArtifactSpecCollection, ImageArtifactType
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data, image_payload_metadata
from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.core.steps.function_runtime import ImageFunctionOutputContextStrategy, ObjectLabelsFunctionOutputContextStrategy


spec = importlib.util.spec_from_file_location(
    "volume_projection_acceptance_fixture_v2",
    Path(__file__).parents[1] / "diagnostics/volume_projection_fixture.py",
)
fixture = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fixture
spec.loader.exec_module(fixture)


@pytest.fixture
def source_volume():
    pixels = np.zeros((3, 8, 9), dtype=np.uint16)
    for index in range(3):
        pixels[index, 1:index + 3, 1:index + 3] = index + 11
    addresses = tuple(OpenHCSPlaneAddress.from_values("image.ome.tif", 1, 1, z + 1, 1) for z in range(3))
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic-unit-input/image.ome.tif",) * 3,
            component_metadata=tuple(address.as_component_metadata() for address in addresses),
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    return metadata.payload_with(pixels)


def output_plan(declaration):
    source = ArtifactSpec.input("source_volume", ImageArtifactType)
    bound = declaration.bind_main_flow_source(ArtifactSpecCollection((source,)))
    return ArtifactOutputPlan(
        name=bound.name, path="/synthetic-unit-output/" + bound.name,
        artifact_type=bound.artifact_type, relations=bound.relations,
        variable_components=(AllComponents.Z_INDEX,),
    )


@pytest.mark.parametrize("indices", [(), (2, 0, 1), (2, 0), (1,)])
def test_selected_then_full_stack_outputs_keep_exact_source_context(source_volume, indices):
    original_pixels = image_payload_data(source_volume)
    selected_indices = indices or (0, 1, 2)
    selection = fixture.select_volume_fixture_planes_v2(source_volume, indices)
    projected = ImageFunctionOutputContextStrategy().contextualize(
        source_volume, selection, output_plan(fixture.SELECTED_VOLUME),
        RuntimePlaneAxisValueProjection(RuntimePlaneAxis.RUNTIME_SLICE, (), None, 3),
    )
    expected = original_pixels[list(selected_indices)]
    source_metadata = image_payload_metadata(source_volume)
    # for_source_planes intentionally consumes a singleton plane axis. This
    # declaration instead returns a 3-D stack, including for one selected plane.
    expected_provenance = source_metadata.for_source_planes(selected_indices).source_provenance.with_source_image_provenance_planes(
        source_metadata.source_image_provenance_planes.select(selected_indices),
    )
    np.testing.assert_array_equal(image_payload_data(projected), expected)
    assert image_payload_metadata(projected).source_provenance == expected_provenance
    assert image_payload_metadata(projected).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    projection = RuntimePlaneAxisValueProjection(RuntimePlaneAxis.RUNTIME_SLICE, (), None, len(selected_indices))
    for _ in range(2):
        image, labels, rows = fixture.inspect_volume_fixture_v2(projected)
        contextual_image = ImageFunctionOutputContextStrategy().contextualize(
            projected, image, output_plan(fixture.VOLUME_IMAGE), projection,
        )
        contextual_labels = ObjectLabelsFunctionOutputContextStrategy().contextualize(
            projected, labels, output_plan(fixture.VOLUME_LABELS), projection,
        )
        np.testing.assert_array_equal(image_payload_data(contextual_image), expected)
        np.testing.assert_array_equal(object_label_dense_array(contextual_labels), expected.astype(np.int32))
        assert image_payload_metadata(contextual_image).source_provenance == expected_provenance
        assert contextual_labels.source_provenance == expected_provenance
        assert contextual_labels.declared_plane_count() == len(selected_indices)
        contextual_labels.validate_source_alignment(fixture.VOLUME_LABELS.name)
        np.testing.assert_array_equal(rows.column_values("slice_index"), np.arange(len(selected_indices)))
        np.testing.assert_array_equal(rows.column_values("object_label"), [11 + index for index in selected_indices])
        np.testing.assert_array_equal(rows.column_values("pixel_count"), [(index + 2) ** 2 for index in selected_indices])
        projected = contextual_image


@pytest.mark.parametrize("indices", [(0, 0), (-1,), (3,), (True,), (0.5,)])
def test_projection_owner_rejects_invalid_selection(source_volume, indices):
    with pytest.raises((ValueError, IndexError, TypeError)):
        fixture.select_volume_fixture_planes_v2(source_volume, indices)


def test_empty_label_stack_keeps_schema_and_exact_plane_context(source_volume):
    empty = image_payload_metadata(source_volume).payload_with(np.zeros((3, 8, 9), dtype=np.uint16))
    image, labels, rows = fixture.inspect_volume_fixture_v2(empty)
    projection = RuntimePlaneAxisValueProjection(RuntimePlaneAxis.RUNTIME_SLICE, (), None, 3)
    contextual = ObjectLabelsFunctionOutputContextStrategy().contextualize(
        image, labels, output_plan(fixture.VOLUME_LABELS), projection,
    )
    assert contextual.declared_plane_count() == 3
    assert contextual.measurement_plane_domains() == ((), (), ())
    contextual.validate_source_alignment(fixture.VOLUME_LABELS.name)
    assert len(rows) == 0 and rows.row_type is fixture.VolumeProjectionFixtureRow
    assert all(len(rows.column_values(field.name)) == 0 for field in rows.fields)
