import numpy as np

from arraybridge import MemoryType
from arraybridge.devices import AcceleratorDevice

from openhcs.processing.backends.analysis.cell_counting_cupy import (
    _watershed_with_cpu_partition,
)


def test_watershed_partition_roundtrips_through_declared_cupy_device(
    monkeypatch,
) -> None:
    restored_devices = []
    cupy = type(MemoryType.CUPY.library)
    monkeypatch.setattr(cupy, "device_of", lambda _library, _value: AcceleratorDevice(3))
    monkeypatch.setattr(cupy, "to_numpy", lambda _library, value: np.asarray(value))
    monkeypatch.setattr(
        cupy,
        "from_numpy",
        lambda _library, value, device: (restored_devices.append(device), value)[1],
    )
    image = np.array([[0.0, 1.0, 0.0], [1.0, 2.0, 1.0], [0.0, 1.0, 0.0]])
    markers = np.array([[1, 0, 0], [0, 0, 0], [0, 0, 2]])
    mask = np.ones_like(markers, dtype=bool)

    labels = _watershed_with_cpu_partition(image, markers, mask=mask)

    assert labels.shape == image.shape
    assert restored_devices == [AcceleratorDevice(3)]
