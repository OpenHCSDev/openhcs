"""A function's returned array reaches host memory through one conversion.

Image files and object labels are both stored as NumPy arrays. Whatever array
library a function returns them in, the copy to host memory is made by
``host_array``; the label builder and the image file writer both use it.
"""

from __future__ import annotations

import sys
import types

import numpy as np
import pytest
from arraybridge import MemoryType

from openhcs.core.device_assignment import DevicePreference, DeviceRule
from openhcs.core.artifacts.kinds import ObjectLabelsArtifactType
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.runtime_array_values import host_array
from openhcs.core.runtime_image_values import (
    ImagePayload,
    ImagePayloadMetadata,
    as_runtime_value,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisValueProjection,
    RuntimeSlicePlaneAxis,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues


def _label_pixels() -> np.ndarray:
    labels = np.zeros((2, 16, 16), dtype=np.int32)
    labels[0, 2:6, 2:6] = 1
    labels[1, 8:12, 8:12] = 2
    return labels


class _DeviceArray:
    """Stands in for ``cupy.ndarray``: no implicit host copy, ``get()`` copies."""

    def __init__(self, host: np.ndarray) -> None:
        self._host = host
        self.host_copies = 0

    @property
    def shape(self) -> tuple[int, ...]:
        return self._host.shape

    @property
    def ndim(self) -> int:
        return self._host.ndim

    @property
    def dtype(self) -> np.dtype:
        return self._host.dtype

    def __len__(self) -> int:
        return len(self._host)

    def __getitem__(self, key: object) -> "_DeviceArray":
        return type(self)(self._host[key])

    def __array__(self, dtype: object = None, copy: object = None) -> np.ndarray:
        raise TypeError(
            "Implicit conversion to a NumPy array is not allowed. "
            "Please use `.get()` to construct a NumPy array explicitly."
        )

    def get(self) -> np.ndarray:
        self.host_copies += 1
        return self._host.copy()


_DeviceArray.__module__ = "cupy"


@pytest.fixture
def device_array(monkeypatch):
    """Build arrays ArrayBridge recognises as CuPy, without CuPy or a GPU."""
    module = types.ModuleType("cupy")
    module.ndarray = _DeviceArray
    monkeypatch.setitem(sys.modules, "cupy", module)
    return _DeviceArray


def _torch_cpu(pixels: np.ndarray) -> object:
    torch = pytest.importorskip("torch", reason="torch is an optional dependency")
    return torch.from_numpy(pixels.copy())


def _on_assigned_accelerator(memory_type: MemoryType, pixels: np.ndarray) -> object:
    """``pixels`` in the library, on the accelerator this process assigns it."""
    library = memory_type.library
    if not library.is_installed():
        pytest.skip(f"{library.display_name} is an optional dependency")
    try:
        assigned = DeviceRule.assign(library, DevicePreference())
    except ValueError as no_device:
        pytest.skip(str(no_device))
    if assigned.device in library.host_devices():
        pytest.skip(f"{assigned.describe()}: no accelerator array to test")
    return library.from_numpy(pixels.copy(), assigned.device)


def _torch_cuda(pixels: np.ndarray) -> object:
    return _on_assigned_accelerator(MemoryType.TORCH, pixels)


def _cupy(pixels: np.ndarray) -> object:
    return _on_assigned_accelerator(MemoryType.CUPY, pixels)


REAL_LIBRARY_ARRAYS = pytest.mark.parametrize(
    "to_library", (_torch_cpu, _torch_cuda, _cupy), ids=("torch-cpu", "torch-cuda", "cupy")
)


def _assert_host_labels(value: object, expected: np.ndarray) -> None:
    assert type(value.labels) is np.ndarray
    np.testing.assert_array_equal(value.labels, expected)
    assert value.domain.declared_object_ids == (1, 2)


def test_device_array_refuses_an_implicit_host_copy(device_array):
    with pytest.raises(TypeError, match="Implicit conversion"):
        np.asarray(device_array(_label_pixels()))


def test_host_array_copies_a_device_array_to_numpy_once(device_array):
    labels = device_array(_label_pixels())

    host = host_array(labels)

    assert type(host) is np.ndarray
    np.testing.assert_array_equal(host, _label_pixels())
    assert labels.host_copies == 1


def test_host_array_returns_a_numpy_array_unchanged():
    pixels = _label_pixels()
    assert host_array(pixels) is pixels
    assert host_array(ImagePayload.of(pixels)) is pixels


def test_numpy_reads_an_image_payload_through_host_array(device_array):
    payload = ImagePayload.of(device_array(_label_pixels()))

    np.testing.assert_array_equal(np.asarray(payload), _label_pixels())


def test_label_output_in_a_device_array_becomes_host_labels(device_array):
    image = ImagePayload.of(np.ones((2, 16, 16), dtype=np.float32))

    labels = ObjectLabelsArtifactType.contextualize_image(
        image, ImagePayload.of(device_array(_label_pixels())), None, None
    )

    _assert_host_labels(labels, _label_pixels())


def test_plane_scoped_label_output_in_a_device_array_becomes_host_labels(
    device_array,
):
    image = ImagePayloadMetadata(plane_axis=RuntimeSlicePlaneAxis).payload_with(
        np.ones((2, 16, 16), dtype=np.float32)
    )
    labels = ObjectLabelsArtifactType.contextualize_image(
        image,
        ImagePayload.of(device_array(_label_pixels())),
        None,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimeSlicePlaneAxis, axis_size=2
        ),
    )

    assert type(labels.labels) is np.ndarray
    np.testing.assert_array_equal(labels.labels, _label_pixels())


def test_image_file_and_label_output_make_the_same_host_copy(device_array):
    pixels = _label_pixels()
    image = ImagePayload.of(np.ones((2, 16, 16), dtype=np.float32))

    written = ImageFileFormat.require_path("labels.tif").prepare(
        ImagePayload.of(device_array(pixels))
    )
    labels = ObjectLabelsArtifactType.contextualize_image(
        image, ImagePayload.of(device_array(pixels)), None, None
    )

    np.testing.assert_array_equal(np.asarray(written), labels.labels)


@REAL_LIBRARY_ARRAYS
def test_label_output_in_a_real_library_becomes_host_labels(to_library):
    image = ImagePayload.of(np.ones((2, 16, 16), dtype=np.float32))

    labels = ObjectLabelsArtifactType.contextualize_image(
        image, ImagePayload.of(to_library(_label_pixels())), None, None
    )

    _assert_host_labels(labels, _label_pixels())


@REAL_LIBRARY_ARRAYS
def test_numpy_reads_a_real_library_image_payload(to_library):
    payload = ImagePayload.of(to_library(_label_pixels()))

    np.testing.assert_array_equal(np.asarray(payload), _label_pixels())


def test_file_writers_receive_a_device_array_as_a_host_array(device_array):
    stored = as_runtime_value(device_array(_label_pixels())).array_data

    assert type(stored) is np.ndarray
    np.testing.assert_array_equal(stored, _label_pixels())


@REAL_LIBRARY_ARRAYS
def test_file_writers_receive_a_real_library_array_as_a_host_array(to_library):
    stored = as_runtime_value(to_library(_label_pixels())).array_data

    assert type(stored) is np.ndarray
    np.testing.assert_array_equal(stored, _label_pixels())


@pytest.mark.parametrize("to_library", (_torch_cuda, _cupy), ids=("torch-cuda", "cupy"))
def test_image_output_of_per_slice_sources_stays_in_its_library(to_library):
    """An image output is not a stored value yet: it must not be copied to host."""
    sources = RuntimeSliceAlignedValues(
        tuple(ImagePayload.of(np.ones((16, 16), dtype=np.float32)) for _ in range(2))
    )
    pixels = to_library(_label_pixels())

    output = sources.contextualize_image_output(
        ImagePayload.of(pixels),
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimeSlicePlaneAxis, axis_size=2
        ),
    )

    assert type(output.data) is type(pixels)
    np.testing.assert_array_equal(host_array(output), _label_pixels())


def test_slicing_a_masked_image_does_not_copy_its_mask_to_host(device_array):
    mask = device_array(np.ones((2, 16, 16), dtype=bool))
    image = ImagePayloadMetadata(plane_axis=RuntimeSlicePlaneAxis).payload_with(
        device_array(np.ones((2, 16, 16), dtype=np.float32)), mask
    )

    planes = image.alignment_slices()

    assert [type(plane.mask) for plane in planes] == [device_array, device_array]
    assert [plane.mask.shape for plane in planes] == [(16, 16), (16, 16)]


@pytest.mark.parametrize("to_library", (_torch_cuda, _cupy), ids=("torch-cuda", "cupy"))
def test_slicing_a_masked_gpu_image_keeps_its_mask_on_the_gpu(to_library):
    mask = to_library(np.ones((2, 16, 16), dtype=bool))
    image = ImagePayloadMetadata(plane_axis=RuntimeSlicePlaneAxis).payload_with(
        to_library(np.ones((2, 16, 16), dtype=np.float32)), mask
    )

    planes = image.alignment_slices()

    assert [type(plane.mask) for plane in planes] == [type(mask), type(mask)]
