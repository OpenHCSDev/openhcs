"""Direct artifact values retain source ownership across call mutation."""

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType, MeasurementsArtifactType
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_metadata,
)
from openhcs.interop.cellprofiler.runtime.artifact_binding import RuntimeArtifactTypeStrategy


def test_integer_call_mutation_does_not_replace_post_call_source():
    spec = ArtifactSpec.input("DNA", ImageArtifactType)
    pixels = np.arange(12, dtype=np.uint8).reshape(3, 4)
    source = ImagePayloadMetadata(source_image_names=("Original",)).payload_with(pixels)
    strategy = RuntimeArtifactTypeStrategy.for_artifact_type(spec.artifact_type)
    raw = strategy.raw_runtime_input_value(spec, source)
    assert image_payload_data(raw) is pixels
    assert image_payload_metadata(raw) is not image_payload_metadata(source)
    bound = strategy.runtime_input_value(spec, source)
    assert not np.shares_memory(image_payload_data(bound), pixels)
    image_payload_data(bound)[:] = -1
    image_payload_metadata(bound).source_image_names = ("ChangedByCallable",)

    post_call = strategy.runtime_input_value(spec, source)
    np.testing.assert_array_equal(image_payload_data(post_call), pixels.astype(np.float32) / 255)
    assert image_payload_metadata(post_call).source_image_names == (spec.name,)
    assert image_payload_metadata(source).source_image_names == ("Original",)
    assert image_payload_data(source) is pixels


def test_raw_source_derivation_preserves_live_nested_source_mapping():
    spec = ArtifactSpec.input("DNA", ImageArtifactType)
    source = ImagePayloadMetadata(
        source_component_metadata={"nested": {"selected": "before"}},
    ).payload_with(np.zeros((2, 3), dtype=np.uint8))
    strategy = RuntimeArtifactTypeStrategy.for_artifact_type(spec.artifact_type)
    first = strategy.raw_runtime_input_value(spec, source)
    nested = image_payload_metadata(source).source_component_metadata["nested"]
    assert image_payload_metadata(first) is not image_payload_metadata(source)
    assert image_payload_metadata(first).source_component_metadata["nested"] is nested
    image_payload_metadata(source).source_component_metadata["nested"]["selected"] = "after"
    second = strategy.raw_runtime_input_value(spec, source)
    assert image_payload_metadata(first).source_component_metadata["nested"]["selected"] == "after"
    assert image_payload_metadata(second).source_component_metadata["nested"]["selected"] == "after"


def test_measurement_type_errors_remain_at_value_consumption():
    spec = ArtifactSpec.input("Intensity", MeasurementsArtifactType)
    strategy = RuntimeArtifactTypeStrategy.for_artifact_type(spec.artifact_type)
    with pytest.raises(TypeError, match="Measurement artifact 'Intensity' requires a MeasurementTable, got object"):
        strategy.runtime_input_value(spec, object())
    with pytest.raises(TypeError, match="Measurement artifact 'Intensity' requires a MeasurementTable, got object"):
        strategy.source_image_name(spec, object())
