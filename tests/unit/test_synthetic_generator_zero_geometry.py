"""Zero overlap/jitter retain literal geometry in both declared plate layouts."""

import numpy as np
import pytest
import tifffile

from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator


@pytest.mark.parametrize("format", ("ImageXpress", "OperaPhenix"))
@pytest.mark.parametrize("native", (False, True))
@pytest.mark.parametrize("grid", ((1, 1), (2, 2)))
def test_zero_geometry_generates_deterministic_requested_tiles(
    tmp_path, format, native, grid
):
    outputs = []
    for run in range(2):
        root = tmp_path / str(run)
        generator = SyntheticMicroscopyGenerator(
            output_dir=str(root),
            grid_size=grid,
            tile_size=(64, 64),
            overlap_percent=0,
            stage_error_px=0,
            wavelengths=1,
            z_stack_levels=1,
            num_cells=4,
            wells=["A01"],
            format=format,
            openhcs_format=native,
            random_seed=7,
        )
        assert generator.image_size == (64 * grid[1], 64 * grid[0])
        for row in range(grid[0]):
            for col in range(grid[1]):
                assert generator._site_position(row, col) == (64 * col, 64 * row)
        generator.generate_dataset()
        images = {
            path.relative_to(root): tifffile.imread(path)
            for path in root.rglob("*.tif*")
        }
        assert len(images) == grid[0] * grid[1]
        assert all(image.shape == (64, 64) for image in images.values())
        outputs.append(images)
    assert outputs[0].keys() == outputs[1].keys()
    for path in outputs[0]:
        np.testing.assert_array_equal(outputs[0][path], outputs[1][path])


def test_subpixel_overlap_does_not_sample_an_empty_pixel_region(tmp_path):
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(tmp_path),
        grid_size=(1, 1),
        tile_size=(32, 64),
        overlap_percent=1,
        stage_error_px=0,
        wavelengths=1,
        z_stack_levels=1,
        num_cells=4,
        wells=["A01"],
        random_seed=7,
    )
    generator.generate_dataset()
    assert len(list(tmp_path.rglob("*.tif"))) == 1
