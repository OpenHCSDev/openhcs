"""Unwaived synthetic reproducer for PR394's canonical raw-call boundary.

Invoke explicitly with pytest. It is intentionally not a passing acceptance
receipt until the existing executor owner repairs the canonical ndarray ABI.
No persisted scientific inputs, jobs, registration or viewer are used.
"""

from __future__ import annotations

import numpy as np

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.morphology import morph, MorphOperation, RepeatMode


def test_original_registered_distance_raw_abi_keeps_planar_geometry():
    labels = np.zeros((1, 9, 9), dtype=np.int32)
    labels[0, 2:7, 2:7] = 29
    original = labels.copy()
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("saved_foreground",),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic/A01_s001_w2_labels.tif",),
            component_metadata=({"well": "A01", "site": "1", "channel": "2"},),
        ),
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
    ).payload_with(labels, None)
    contract = CallableContract.from_callable(morph)
    result = CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), source,
        {"operation": MorphOperation.DISTANCE, "repeat_mode": RepeatMode.ONCE, "rescale_values": False},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
    )
    pixels = image_payload_data(result)
    assert pixels.shape == labels.shape
    assert pixels.dtype == np.float32
    assert pixels[0, 4, 4] == 3.0
    assert pixels[0, 0, 0] == 0.0
    np.testing.assert_array_equal(labels, original)
