"""Persist the existing bounded numerical control as an ImageXpress acquisition."""

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

from openhcs.constants import AllComponents
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.microscopes.imagexpress import ImageXpressFilenameParser

# Initialize OpenHCS's existing metadata configuration before PolyStore.
# isort: split
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager

from tests.diagnostics.basicpy_observation_fixture import shaded_observations


def create_acquisition(destination: Path) -> dict:
    """Never replace a previous fixture or its original receipt."""
    destination.mkdir(parents=True, exist_ok=False)
    raw = destination / "TimePoint_1"
    raw.mkdir()
    observations, truth = shaded_observations()
    (destination / "plate.HTD").write_text(
        '"XSites", 6\n"YSites", 4\n"PixelSizeUM", 0.65\n'
    )
    parser = ImageXpressFilenameParser(FileManager({"disk": DiskStorageBackend()}))
    paths = []
    for site, pixels in enumerate(observations, start=1):
        components = FilenameParseResult(
            (
                (AllComponents.WELL, "A01"),
                (AllComponents.SITE, site),
                (AllComponents.CHANNEL, 1),
                (AllComponents.Z_INDEX, 1),
                (AllComponents.TIMEPOINT, 1),
            ),
            extension=".tif",
        )
        path = raw / parser.construct_filename(components)
        ImageFileFormat.require_path(path).write(path, pixels)
        paths.append(
            {"path": str(path.relative_to(destination)),
             "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        )
    np.save(destination / "synthetic-flatfield-truth.npy", truth)
    return {
        "purpose": "Synthetic fit/publication control; not a blind biological assay",
        "plate_path": str(destination),
        "shape_nyx": list(observations.shape),
        "dtype": str(observations.dtype),
        "independent_component": AllComponents.SITE.value,
        "source_xy_spacing_um": 0.65,
        "files": paths,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    if args.destination.exists():
        parser.error("Refusing to overwrite an existing fixture.")
    print(json.dumps(create_acquisition(args.destination), indent=2))


if __name__ == "__main__":
    main()
