import numpy as np
from arraybridge import MemoryType
from arraybridge.devices import AcceleratorDevice

from openhcs.core.runtime_array_values import ArrayPlacement
from openhcs.processing.backends.analysis.cell_counting_cupy import (
    _watershed_with_cpu_partition,
)


def test_watershed_labels_return_to_the_device_of_the_image(
    cupy_arrays_that_record_their_device,
) -> None:
    device_array, state = cupy_arrays_that_record_their_device
    image = device_array(
        np.array([[0.0, 1.0, 0.0], [1.0, 2.0, 1.0], [0.0, 1.0, 0.0]]), 1
    )
    markers = device_array(np.array([[1, 0, 0], [0, 0, 0], [0, 0, 2]]), 1)
    mask = device_array(np.ones((3, 3), dtype=bool), 1)

    labels = _watershed_with_cpu_partition(image, markers, mask=mask)

    assert labels.shape == image.shape
    assert ArrayPlacement.of(labels) == ArrayPlacement(
        MemoryType.CUPY.library, AcceleratorDevice(1)
    )
    assert state["downloads"] == [1, 1, 1]
    assert state["uploads"] == [1]
    assert set(np.unique(labels.values)) == {1, 2}
