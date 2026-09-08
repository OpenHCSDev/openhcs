"""Reject ambiguous or invalid image-source selections at their owner."""

import numpy as np
import pytest

from openhcs.core.projected_image_output import SelectedPlaneImageOutput
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)


@pytest.mark.parametrize("indices", [(), (0, 0), (-1,), (True,), (0.5,)])
def test_selected_output_rejects_invalid_indices(indices):
    with pytest.raises(ValueError, match="Selected source planes"):
        SelectedPlaneImageOutput(np.zeros((len(indices), 3, 4)), indices)


@pytest.mark.parametrize("shape", [(3, 4), (2, 3, 4), (1, 2, 3, 4)])
def test_selected_output_requires_one_plane_per_index(shape):
    with pytest.raises(ValueError, match="one plane per source index"):
        SelectedPlaneImageOutput(np.zeros(shape), (0,))


@pytest.mark.parametrize("selected_plane", [None, 0])
def test_selected_output_requires_complete_projection(selected_plane):
    output = SelectedPlaneImageOutput(np.zeros((1, 3, 4)), (0,))
    projection = (
        None
        if selected_plane is None
        else RuntimePlaneAxisValueProjection(
            RuntimePlaneAxis.RUNTIME_SLICE, (), selected_plane, 2
        )
    )
    with pytest.raises(ValueError, match="complete input stack projection"):
        output.resolve_source_context(np.zeros((2, 3, 4)), projection)


def test_selected_output_rejects_out_of_range_source_plane():
    output = SelectedPlaneImageOutput(np.zeros((1, 3, 4)), (2,))
    projection = RuntimePlaneAxisValueProjection(
        RuntimePlaneAxis.RUNTIME_SLICE, (), None, 2
    )
    with pytest.raises(ValueError, match="outside the input stack"):
        output.resolve_source_context(np.zeros((2, 3, 4)), projection)


def test_selected_output_array_interop_and_conversion_preserve_selection():
    data = np.arange(12).reshape(1, 3, 4)
    output = SelectedPlaneImageOutput(data, (1,))
    np.testing.assert_array_equal(np.asarray(output), data)
    converted = output.with_data(data.astype(np.float32))
    assert converted.source_indices == (1,)
    assert converted.dtype == np.float32
    with pytest.raises(ValueError, match="one plane per source index"):
        output.with_data(np.zeros((2, 3, 4)))
