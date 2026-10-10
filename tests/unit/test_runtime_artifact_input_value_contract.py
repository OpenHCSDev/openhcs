"""Direct artifact values retain source ownership across call mutation."""

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType, MeasurementsArtifactType
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.interop.cellprofiler.runtime.output_recording import (
    CellProfilerOutputRecorder,
)


def test_integer_call_mutation_does_not_replace_post_call_source():
    spec = ArtifactSpec.input("DNA", ImageArtifactType)
    pixels = np.arange(12, dtype=np.uint8).reshape(3, 4)
    source = ImagePayloadMetadata(source_image_names=("Original",)).payload_with(pixels)
    strategy = CellProfilerOutputRecorder.for_artifact_type(spec.artifact_type)
    raw = strategy.raw_runtime_input_value(spec, source)
    assert raw.data is pixels
    assert raw.metadata is not source.metadata
    bound = strategy.runtime_input_value(spec, source)
    assert not np.shares_memory(bound.data, pixels)
    bound.data[:] = -1
    bound.metadata.source_image_names = ("ChangedByCallable",)

    post_call = strategy.runtime_input_value(spec, source)
    np.testing.assert_array_equal(post_call.data, pixels.astype(np.float32) / 255)
    assert post_call.metadata.source_image_names == (spec.name,)
    assert source.metadata.source_image_names == ("Original",)
    assert source.data is pixels


def test_raw_source_derivation_preserves_live_nested_source_mapping():
    spec = ArtifactSpec.input("DNA", ImageArtifactType)
    source = ImagePayloadMetadata(
        source_component_metadata={"nested": {"selected": "before"}},
    ).payload_with(np.zeros((2, 3), dtype=np.uint8))
    strategy = CellProfilerOutputRecorder.for_artifact_type(spec.artifact_type)
    first = strategy.raw_runtime_input_value(spec, source)
    nested = source.metadata.source_component_metadata["nested"]
    assert first.metadata is not source.metadata
    assert first.metadata.source_component_metadata["nested"] is nested
    source.metadata.source_component_metadata["nested"]["selected"] = "after"
    second = strategy.raw_runtime_input_value(spec, source)
    assert first.metadata.source_component_metadata["nested"]["selected"] == "after"
    assert second.metadata.source_component_metadata["nested"]["selected"] == "after"


def test_measurement_type_errors_remain_at_value_consumption():
    spec = ArtifactSpec.input("Intensity", MeasurementsArtifactType)
    strategy = CellProfilerOutputRecorder.for_artifact_type(spec.artifact_type)
    with pytest.raises(TypeError, match="Measurement artifact 'Intensity' requires a MeasurementTable, got object"):
        strategy.runtime_input_value(spec, object())
    with pytest.raises(TypeError, match="Measurement artifact 'Intensity' requires a MeasurementTable, got object"):
        strategy.source_image_name(spec, object())
