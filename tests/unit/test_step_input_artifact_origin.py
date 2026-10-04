"""Named source origins select pixel authority, not just a provenance alias."""

from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.constants.constants import AllComponents
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_adapters import RuntimeAdapterRequest
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_metadata,
)
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

    assert image_payload_data(result) is data
    assert image_payload_metadata(result).source_image_names == (alias,)
    assert image_payload_metadata(result).source_path == "/synthetic/raw.tif"


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
        selector=SourceSelector(components=(ComponentSelector(AllComponents.CHANNEL, "2"),)),
    )

    result = binding.project_step_input_payload(payload)

    np.testing.assert_array_equal(image_payload_data(result), data[1])
    assert image_payload_metadata(result).source_image_names == ("Processed2",)
    assert image_payload_metadata(result).source_path == "/synthetic/ch2.tif"
    missing = NamedSourceBinding(
        alias="Absent",
        selector=SourceSelector(components=(ComponentSelector(AllComponents.CHANNEL, "3"),)),
    )
    with pytest.raises(ValueError, match="selects no current planes"):
        missing.project_step_input_payload(payload)


def test_binding_origin_uses_existing_registered_universe_family():
    assert SourceUniverseRequest.for_binding(NamedSourceBinding(alias="Response")) is StepInputSourceUniverseRequest
    assert SourceUniverseRequest.for_binding(
        NamedSourceBinding(alias="Raw", origin=SourceBindingOrigin.PIPELINE_START)
    ) is PipelineStartSourceUniverseRequest
