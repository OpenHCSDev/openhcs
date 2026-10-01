"""Dense full-stack ABI must consume aligned source/artifact values correctly."""

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    ImagePayloadExecutionMode,
    compose_aligned_image_payload,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.processing.backends.cellprofiler.intensity import rescale_intensity


def test_real_rescale_full_stack_materializes_composed_runtime_sources():
    data = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    ).payload_with(data, None)
    composition = compose_aligned_image_payload(
        "synthetic source inputs", (source, source)
    )
    assert isinstance(composition.payload, AlignedImageStack)
    contract = CallableContract.from_callable(rescale_intensity)
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        composition.payload,
        {},
        execution_mode=contract.runtime_image_execution_mode,
    )
    expected = np.stack((data, data), axis=1) / 23.0
    np.testing.assert_allclose(image_payload_data(result), expected)
