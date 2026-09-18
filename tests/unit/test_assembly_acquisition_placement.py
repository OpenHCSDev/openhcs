"""Synthetic native CPU/GPU checks of the existing assemblers' XY transform."""

import numpy as np
import pytest
from scipy.ndimage import center_of_mass

from openhcs.constants.constants import MemoryType
from openhcs.core.callable_contract import CallableContract
from openhcs.processing.backends.assemblers.assemble_stack_cpu import assemble_stack_cpu
from openhcs.processing.backends.assemblers.assemble_stack_cupy import (
    assemble_stack_cupy,
)
from openhcs.processing.backends.assemblers.blending import TileBlendMethod
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.utils.environment import OpenHCSProcessEnvironment
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


@pytest.fixture(params=("cpu", "gpu"))
def assemble(request):
    if request.param == "cpu":
        return CallableContract.from_callable(
            assemble_stack_cpu
        ).resolve_raw_runtime_callable()
    cp = pytest.importorskip("cupy")
    try:
        if not cp.cuda.runtime.getDeviceCount():
            pytest.skip("native CUDA device unavailable")
    except cp.cuda.runtime.CUDARuntimeError:
        pytest.skip("native CUDA runtime unavailable")
    from cupy_backends.cuda.libs import nvrtc

    try:
        nvrtc.getVersion()
    except RuntimeError as exc:
        pytest.skip(f"native CuPy NVRTC dependency unavailable: {exc}")
    function = CallableContract.from_callable(
        assemble_stack_cupy
    ).resolve_raw_runtime_callable()

    def run(tiles, positions, **kwargs):
        return cp.asnumpy(function(cp.asarray(tiles), positions, **kwargs))

    return run


@pytest.mark.parametrize("xy", ((-1.25, -0.75), (0.75, 0.25)))
def test_signed_fractional_impulse_is_translated_positive_not_negative(assemble, xy):
    image = np.zeros((1, 5, 7), np.float32)
    image[0, 2, 3] = 1
    result = assemble(image, [xy], blend_method=TileBlendMethod.NONE)
    assert result.shape == (6, 8)
    assert center_of_mass(result) == pytest.approx((2.25, 3.75), abs=1e-6)
    assert result[2:4, 3:5] == pytest.approx(
        np.array([[0.1875, 0.5625], [0.0625, 0.1875]]), abs=1e-6
    )


def test_fractional_linear_ramp_and_coverage_retain_full_boundary_extent(assemble):
    rows, columns = np.indices((5, 7))
    tile = (10 * rows + columns).astype(np.float32)
    result = assemble(tile[None], [(-1.25, -0.75)], blend_method=TileBlendMethod.NONE)
    assert result[1:5, 1:7] == pytest.approx(
        (10 * (rows[1:, 1:] - 0.25) + columns[1:, 1:] - 0.75), abs=1e-5
    )
    assert result[-1, -1] == pytest.approx(tile[-1, -1])
    assert result[0, 0] == pytest.approx(tile[0, 0])


@pytest.mark.parametrize(
    "xy", ((1.000000001, -1.000000001), (-0.000000001, 0.000000001))
)
def test_near_integer_floor_ceil_do_not_round_positions_to_float32(assemble, xy):
    result = assemble(
        np.full((1, 3, 4), 111, np.uint16), [xy], blend_method=TileBlendMethod.NONE
    )
    assert result.shape == (4, 5)
    assert np.array_equal(result, np.full((4, 5), 111, np.uint16))


def test_exact_integer_positions_preserve_raw_dtype_and_all_intensities(assemble):
    tile = np.arange(35, dtype=np.uint16).reshape(5, 7)
    result = assemble(tile[None], [(-3.0, 8.0)], blend_method=TileBlendMethod.NONE)
    assert result.dtype == tile.dtype
    assert np.array_equal(result, tile)


def test_empty_tile_axis_returns_empty_slice_with_source_dtype(assemble):
    result = assemble(np.empty((0, 3, 4), np.float32), [])
    assert result.shape == (0, 0)
    assert result.dtype == np.float32


def test_shared_sparse_tiles_leave_holes_and_use_one_paired_canvas(assemble):
    positions = [(-2.25, -0.5), (8.75, -0.5)]
    a = assemble(
        np.full((2, 4, 5), 101, np.uint16), positions, blend_method=TileBlendMethod.NONE
    )
    b = assemble(
        np.full((2, 4, 5), 202, np.uint16), positions, blend_method=TileBlendMethod.NONE
    )
    assert a.shape == b.shape == (5, 17)
    assert np.array_equal(b, 2 * a)
    assert np.array_equal(a[:, 6:11], np.zeros((5, 5), np.uint16))


@pytest.mark.parametrize("blend", tuple(TileBlendMethod))
def test_overlapping_seam_resamples_pixels_and_blend_coverage_together(assemble, blend):
    result = assemble(
        np.full((2, 12, 14), 1001, np.uint16),
        [(-1.25, -0.75), (6.125, 2.375)],
        blend_method=blend,
    )
    # Fixed masks genuinely have zero-weight boundary pixels; no synthetic fill.
    assert set(np.unique(result)) <= {0, 1001}
    assert result[5, 10] == 1001


def test_cpu_and_gpu_share_the_same_site_contraction_contract():
    functions = [assemble_stack_cpu]
    # CPU-only mode excludes GPU framework declarations from the registry
    # surface; the comparison admits the cupy declaration through the same
    # process-admission authority the registry itself consults.
    if MemoryType.CUPY.is_installed() and not (
        OpenHCSProcessEnvironment.cpu_only_mode()
    ):
        functions.append(assemble_stack_cupy)
    for function in functions:
        metadata = OpenHCSRegistry.metadata_for_declared_callable(function)
        assert metadata.contract is ProcessingContract.VOLUMETRIC_TO_SLICE


def test_positions_reject_nonfinite_before_canvas_allocation(assemble):
    with pytest.raises(ValueError, match="finite XY"):
        assemble(np.zeros((1, 3, 4), np.float32), [(float("nan"), 0)])
