"""The live fixture uses the numerical control and the real acquisition parser."""

import numpy as np
import pytest

from openhcs.constants import AllComponents
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.microscopes.imagexpress import ImageXpressHandler

# Initialize OpenHCS's existing metadata configuration before PolyStore.
# isort: split
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager

from tests.diagnostics.basicpy_observation_fixture import shaded_observations
from tests.diagnostics.create_basicpy_acquisition_fixture import create_acquisition


def test_saved_numerical_control_has_real_independent_site_calibration(tmp_path):
    plate = tmp_path / "basic-control"
    receipt = create_acquisition(plate)
    handler = ImageXpressHandler(FileManager({"disk": DiskStorageBackend()}))
    observations, truth = shaded_observations()
    assert receipt["shape_nyx"] == [24, 32, 32]
    assert handler.metadata_handler.get_pixel_size(plate) == 0.65
    files = sorted((plate / "TimePoint_1").glob("*.tif"))
    assert len(files) == observations.shape[0]
    sites = []
    for path, expected in zip(files, observations, strict=True):
        parsed = handler.parser.parse_filename(path.name)
        assert parsed is not None
        sites.append(parsed.required_value(AllComponents.SITE))
        assert parsed.required_value(AllComponents.CHANNEL) == 1
        assert parsed.required_value(AllComponents.Z_INDEX) == 1
        np.testing.assert_array_equal(ImageFileFormat.require_path(path).read(path), expected)
    assert sites == list(range(1, 25))
    np.testing.assert_array_equal(
        np.load(plate / "synthetic-flatfield-truth.npy"), truth
    )
    original = [path.read_bytes() for path in files]
    with pytest.raises(FileExistsError):
        create_acquisition(plate)
    assert [path.read_bytes() for path in files] == original
