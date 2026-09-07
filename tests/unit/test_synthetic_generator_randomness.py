"""Synthetic fixtures own their random state across concurrent requests."""

import random
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier

import numpy as np
import pytest
import tifffile

from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator


def _generator(path, seed):
    return SyntheticMicroscopyGenerator(
        output_dir=str(path),
        grid_size=(1, 1),
        tile_size=(32, 32),
        wavelengths=2,
        z_stack_levels=2,
        num_cells=4,
        wells=["A01", "B01"],
        random_seed=seed,
    )


def _images(generator):
    return np.stack(
        [
            generator.generate_cell_image(wavelength, z, "A01")
            for wavelength in (1, 2)
            for z in (0, 1)
        ]
    )


@pytest.mark.parametrize("seed", (1, 7))
def test_seeded_planes_preserve_legacy_global_rng_pixels(monkeypatch, tmp_path, seed):
    # Compare the original global-MT19937 leaf on this exact numerical stack.
    # No platform-specific golden hashes or duplicate generation algorithm.
    def legacy_random_state(seed):
        np.random.seed(seed)
        return np.random

    baseline = tmp_path / "legacy"
    numpy_state = np.random.get_state()
    try:
        with monkeypatch.context() as patch:
            patch.setattr(np.random, "RandomState", legacy_random_state)
            _generator(baseline, seed).generate_dataset()
    finally:
        np.random.set_state(numpy_state)

    isolated = tmp_path / "isolated"
    _generator(isolated, seed).generate_dataset()
    relative_paths = sorted(
        path.relative_to(baseline) for path in baseline.rglob("*.tif")
    )
    assert len(relative_paths) == 8
    assert relative_paths == sorted(
        path.relative_to(isolated) for path in isolated.rglob("*.tif")
    )
    for path in relative_paths:
        np.testing.assert_array_equal(
            tifffile.imread(baseline / path), tifffile.imread(isolated / path)
        )


@pytest.mark.parametrize("seed", (1, 7, None))
def test_generation_does_not_mutate_caller_random_state(tmp_path, seed):
    numpy_state = np.random.get_state()
    python_state = random.getstate()
    generator = _generator(tmp_path, seed)
    generator.generate_dataset()
    actual = np.random.get_state()
    assert actual[0] == numpy_state[0]
    np.testing.assert_array_equal(actual[1], numpy_state[1])
    assert actual[2:] == numpy_state[2:]
    assert random.getstate() == python_state


def test_interleaved_generators_preserve_each_seeded_result(tmp_path):
    expected = [
        _images(_generator(tmp_path / f"serial-{seed}", seed)) for seed in (1, 7)
    ]
    first = _generator(tmp_path / "first", 1)
    second = _generator(tmp_path / "second", 7)
    np.testing.assert_array_equal(_images(first), expected[0])
    np.testing.assert_array_equal(_images(second), expected[1])


def test_concurrent_generators_preserve_each_seeded_result(tmp_path):
    expected = [
        _images(_generator(tmp_path / f"serial-{seed}", seed)) for seed in (1, 7)
    ]
    started = Barrier(2)

    def generate(seed):
        generator = _generator(tmp_path / f"parallel-{seed}", seed)
        started.wait(timeout=5)
        return _images(generator)

    with ThreadPoolExecutor(max_workers=2) as executor:
        actual = list(executor.map(generate, (1, 7)))
    for values, baseline in zip(actual, expected, strict=True):
        np.testing.assert_array_equal(values, baseline)
