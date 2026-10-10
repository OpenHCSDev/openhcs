"""Named source origins select pixel authority, not just a provenance alias."""

from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_adapters import RuntimeAdapterRequest
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_binding_selection import (
    PipelineStartSourceUniverseRequest,
    SourceUniverseRequest,
    StepInputSourceUniverseRequest,
)
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    ComponentSelector,
    NamedSourceBinding,
    SourceBindingOrigin,
    SourceSelector,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.domains.microscopy.axes import Microscopy


@pytest.mark.parametrize("alias", ("Raw", "Response"))
def test_step_input_names_current_pixels_without_loading_workspace(alias):
    data = np.arange(20, dtype=np.uint8).reshape(4, 5)
    payload = ImagePayloadMetadata(
        source_path="/synthetic/raw.tif",
        source_component_metadata={"channel": "1"},
        source_image_names=("Raw",),
    ).payload_with(data)
    binding = NamedSourceBinding(alias=alias)
    request = RuntimeAdapterRequest(
        context=SimpleNamespace(),
        source_payload=payload,
        source_binding_plan=CompiledSourceBindingPlan(bindings=(binding,)),
        axis_scope=RuntimeExecutionAxisScope("A01"),
    )

    result = request.source_artifact_payload(binding.input_spec().ref())

    assert result.data is data
    assert result.metadata.source_image_names == (alias,)
    assert result.metadata.source_path == "/synthetic/raw.tif"


def test_step_input_selects_current_component_planes_not_original_aliases():
    data = np.stack((np.full((4, 5), 7), np.full((4, 5), 91)))
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("Raw1", "Raw2"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic/ch1.tif", "/synthetic/ch2.tif"),
            component_metadata=({"channel": "1"}, {"channel": "2"}),
        ),
    ).payload_with(data)
    binding = NamedSourceBinding(
        alias="Processed2",
        selector=SourceSelector(components=(ComponentSelector(Microscopy.Channel, "2"),)),
    )

    result = binding.project_step_input_payload(payload)

    np.testing.assert_array_equal(result.data, data[1])
    assert result.metadata.source_image_names == ("Processed2",)
    assert result.metadata.source_path == "/synthetic/ch2.tif"
    missing = NamedSourceBinding(
        alias="Absent",
        selector=SourceSelector(components=(ComponentSelector(Microscopy.Channel, "3"),)),
    )
    with pytest.raises(ValueError, match="selects no current planes"):
        missing.project_step_input_payload(payload)


def test_binding_origin_uses_existing_registered_universe_family():
    assert SourceUniverseRequest.for_binding(NamedSourceBinding(alias="Response")) is StepInputSourceUniverseRequest
    assert SourceUniverseRequest.for_binding(
        NamedSourceBinding(alias="Raw", origin=SourceBindingOrigin.PIPELINE_START)
    ) is PipelineStartSourceUniverseRequest


@pytest.mark.parametrize("axis", (RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING))
@pytest.mark.parametrize("aliases", (("Process", "Nuclear"), ("Nuclear", "Process")))
def test_named_step_inputs_select_distinct_current_pixels_independent_of_order(axis, aliases):
    values = {"Process": 7, "Nuclear": 91}
    data = np.stack(tuple(np.full((4, 5), values[alias]) for alias in aliases))
    payload = ImagePayloadMetadata(
        plane_axis=axis,
        source_image_names=aliases,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/synthetic/{alias}.tif" for alias in aliases),
            component_metadata=tuple({"channel": str(index + 1)} for index in range(2)),
        ),
    ).payload_with(data)
    bindings = tuple(NamedSourceBinding(alias=alias) for alias in reversed(aliases))
    request = RuntimeAdapterRequest(
        context=SimpleNamespace(),
        source_payload=payload,
        source_binding_plan=CompiledSourceBindingPlan(bindings=bindings),
        axis_scope=RuntimeExecutionAxisScope("A01"),
    )

    for binding in bindings:
        result = request.source_artifact_payload(binding.input_spec().ref())
        np.testing.assert_array_equal(result.data, np.full((4, 5), values[binding.alias]))
        metadata = result.metadata
        assert metadata.source_image_names == (binding.alias,)
        assert metadata.source_path == f"/synthetic/{binding.alias}.tif"
        assert metadata.plane_axis is None
    np.testing.assert_array_equal(payload.data, data)


def test_existing_alias_and_explicit_selector_must_agree():
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("Raw1", "Raw2"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic/ch1.tif", "/synthetic/ch2.tif"),
            component_metadata=({"channel": "1"}, {"channel": "2"}),
        ),
    ).payload_with(np.ones((2, 4, 5)))
    binding = NamedSourceBinding(
        alias="Raw1",
        selector=SourceSelector(components=(ComponentSelector(Microscopy.Channel, "2"),)),
    )
    with pytest.raises(ValueError, match="selects no current planes"):
        binding.project_step_input_payload(payload)


def test_named_step_input_preserves_all_planes_of_a_multi_plane_image():
    data = np.stack(tuple(np.full((4, 5), value) for value in (7, 11, 91)))
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("Volume", "Volume", "Other"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic/z1.tif", "/synthetic/z2.tif", "/synthetic/other.tif"),
            component_metadata=({"z_index": "1"}, {"z_index": "2"}, {"z_index": "1"}),
        ),
    ).payload_with(data)

    result = NamedSourceBinding(alias="Volume").project_step_input_payload(payload)

    np.testing.assert_array_equal(result.data, data[:2])
    assert result.metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert result.metadata.source_provenance.source_plane_count == 2


def test_new_alias_without_selectors_still_names_the_complete_current_stack():
    data = np.ones((2, 4, 5))
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("Raw1", "Raw2"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic/ch1.tif", "/synthetic/ch2.tif"),
        ),
    ).payload_with(data)

    result = NamedSourceBinding(alias="Response").project_step_input_payload(payload)

    assert result.data is data
    assert result.metadata.source_image_names == ("Response",)
    assert result.metadata.source_provenance.source_plane_count == 2
