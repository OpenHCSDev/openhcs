"""Read-only installed synthetic fit and complete typed publication witness."""

import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import tifffile

from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection


def main(root: Path) -> None:
    output = root / "outputs" / "synthetic_openhcs"
    receipts = root / "mcp-installed"
    status = json.loads((receipts / "receipt-015.json").read_text())
    execution = status["payload"]["results"][0]["payloads"][0]
    assert status["returncode"] == 0 and execution["status"] == "complete"
    assert execution["response"]["execution"]["error"] is None
    fixture = json.loads((root / "fixture.json").read_text())
    for entry in fixture["files"]:
        assert hashlib.sha256((root / "synthetic" / entry["path"]).read_bytes()).hexdigest() == entry["sha256"]
    metadata = json.loads((output / "openhcs_metadata.json").read_text())
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(output, metadata)
    inventory = {}
    for name, expected_count in (("images", 24), ("checkpoints", 48), ("checkpoints_results", 2)):
        entry = metadata["subdirectories"][name]
        paths = {str(path.relative_to(output)) for path in (output / name).glob("*.tif")}
        assert len(paths) == expected_count
        assert set(entry["image_files"]) == paths
        assert {item["virtual_path"] for item in entry["source_projection"]} == paths
        assert paths.issubset(reopened.source_projections_by_virtual_path)
        for item in entry["source_projection"]:
            retained = ImagePayloadMetadata.from_mapping(item["image_metadata"])
            assert retained.source_voxel_spacing == SourceVoxelSpacing((0.65, 0.65))
            assert retained.source_spatial_domain.source_shape_yx == (32, 32)
            if name == "checkpoints_results":
                assert retained.source_image_provenance_planes.contributor_count == 24
                assert retained.plane_axis is None
        inventory[name] = expected_count
    flat = tifffile.imread(output / "checkpoints_results" / "A01_w1_basic_flatfield_step0.tif")
    dark = tifffile.imread(output / "checkpoints_results" / "A01_w1_basic_darkfield_step0.tif")
    assert flat.shape == dark.shape == (32, 32)
    assert flat.dtype == dark.dtype == np.dtype("float32")
    assert np.isfinite(flat).all() and (flat > 0).all()
    assert np.count_nonzero(dark) == 0
    corrected_files = sorted((output / "images").glob("*.tif"))
    max_error = 0.0
    fractional_count = 0
    for index, path in enumerate(corrected_files, start=1):
        raw = tifffile.imread(root / "synthetic" / "TimePoint_1" / f"A01_s{index:03d}_w1_z001_t001.tif")
        corrected = tifffile.imread(path)
        assert corrected.dtype == np.dtype("float32")
        assert corrected.shape == raw.shape == (32, 32)
        np.testing.assert_array_equal(corrected, tifffile.imread(output / "checkpoints" / path.name))
        expected = (raw.astype(np.float32) - dark) / flat
        np.testing.assert_allclose(corrected, expected, rtol=2e-6, atol=2e-3)
        max_error = max(max_error, float(np.max(np.abs(corrected - expected))))
        fractional_count += int(np.count_nonzero(corrected != np.floor(corrected)))
    assert fractional_count > 0
    for index, expected in ((18, tifffile.imread(corrected_files[0])), (19, dark), (20, flat)):
        receipt = json.loads((receipts / f"receipt-{index:03d}.json").read_text())
        assert receipt["returncode"] == 0
        payload = receipt["payload"]["results"][0]["payloads"][0]
        assert payload["observed"] and payload["sample_omitted_count"] == 0
        record = payload["records"][0]
        assert record["components"]["site"] == 1
        np.testing.assert_array_equal(np.asarray(record["array_values"], dtype=np.float32), expected)
    print(json.dumps({"pipeline_status": "COMPLETE", "typed_file_inventory": inventory,
                      "max_same_fit_formula_error": max_error, "fractional_pixels": fractional_count,
                      "mcp_exact_full_plane_matches": 3, "source_pixels_unchanged": True,
                      "biological_acceptance": "NOT_ASSESSED"}))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
