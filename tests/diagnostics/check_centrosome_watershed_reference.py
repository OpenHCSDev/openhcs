"""Finite synthetic watershed parity against the existing CP 4.2 oracle kernel.

The launcher supplies reviewed OpenHCS/dependency source paths. No frozen
analysis, image, expected-answer file or native execution server is used.
"""

import argparse
from io import BytesIO
from pathlib import Path
import subprocess
import sys

import numpy as np

from openhcs.processing.backends.cellprofiler._backend import CellProfilerBackendProvider
from openhcs.processing.backends.cellprofiler.watershed import cellprofiler_legacy_watershed


def assert_reference_parity(
    oracle_python: Path, *, image, markers, mask, connectivity
) -> None:
    worker = Path(__file__).with_name("centrosome_watershed_reference_worker.py")
    original_image = image.copy()
    original_markers = markers.copy()
    original_mask = mask.copy()
    fixture = BytesIO()
    np.savez(
        fixture, image=image, markers=markers, mask=mask,
        connectivity=np.asarray(connectivity),
    )
    completed = subprocess.run(
        [str(oracle_python), "-B", str(worker)],
        input=fixture.getvalue(), capture_output=True, check=True, timeout=5,
    )
    expected = np.load(BytesIO(completed.stdout), allow_pickle=False)
    actual = cellprofiler_legacy_watershed(
        image, markers=markers, mask=mask, connectivity=connectivity,
        backend_provider=CellProfilerBackendProvider.CENTROSOME,
    )
    np.testing.assert_array_equal(actual, expected)
    assert actual.dtype == expected.dtype == np.int32
    np.testing.assert_array_equal(actual[~mask], 0)
    np.testing.assert_array_equal(image, original_image)
    np.testing.assert_array_equal(markers, original_markers)
    np.testing.assert_array_equal(mask, original_mask)


def check_reference(oracle_python: Path) -> None:
    rng = np.random.default_rng(20260930)
    cases = 0
    for shape, connectivity in (
        ((7, 9), 1),
        ((7, 9), np.ones((3, 3), dtype=bool)),
        ((3, 5, 7), 1),
    ):
        image = rng.random(shape)
        mask = np.ones(shape, dtype=bool)
        mask.flat[::13] = False
        first_seed = (1,) * len(shape)
        second_seed = tuple(size - 2 for size in shape)
        mask[first_seed] = mask[second_seed] = True
        for sign in (1, -1):
            markers = np.zeros(shape, dtype=np.int32)
            markers[first_seed] = sign * 7
            markers[second_seed] = sign * 203
            assert_reference_parity(
                oracle_python, image=image, markers=markers, mask=mask,
                connectivity=connectivity,
            )
            cases += 1
            print(f"PASS CP4.2 kernel: shape={shape}, marker_sign={sign}, pixels={image.size}")

    # A tied-priority planar case independently checks the original FIFO and
    # negative-marker semantics from the signed-primary-object call path.
    for sign in (1, -1):
        image = np.array([[0.0, 1.0, 0.0]])
        markers = sign * np.array([[1, 0, 2]], dtype=np.int32)
        mask = np.ones(image.shape, dtype=bool)
        connectivity = np.ones((1, 3), dtype=bool)
        assert_reference_parity(
            oracle_python, image=image, markers=markers, mask=mask,
            connectivity=connectivity,
        )
        cases += 1
        print(f"PASS CP4.2 kernel: tied_priority, marker_sign={sign}")
    print(f"{cases} exact synthetic reference cases passed; no CP pipeline/native/installed claim")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oracle-python", type=Path, required=True)
    try:
        check_reference(parser.parse_args().oracle_python)
    except subprocess.CalledProcessError as error:
        sys.stderr.buffer.write(error.stderr)
        raise
