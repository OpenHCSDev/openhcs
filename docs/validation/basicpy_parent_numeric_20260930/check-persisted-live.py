"""Read-only numeric witness for the retained synthetic failed live run.

This checks pixels and MCP transport, not successful metadata publication or
biological validity. It neither fits a new model nor modifies scientific data.
"""

import json
import sys
from pathlib import Path

import numpy as np
import tifffile


def main(root: Path) -> None:
    output = root / "outputs" / "synthetic_openhcs"
    flat = tifffile.imread(output / "checkpoints_results" / "A01_w1_basic_flatfield_step0.tif")
    dark = tifffile.imread(output / "checkpoints_results" / "A01_w1_basic_darkfield_step0.tif")
    assert flat.shape == dark.shape == (32, 32)
    assert flat.dtype == dark.dtype == np.dtype("float32")
    assert np.isfinite(flat).all() and (flat > 0).all()
    assert np.count_nonzero(dark) == 0
    corrected_files = sorted((output / "images").glob("*.tif"))
    assert len(corrected_files) == 24
    max_error = 0.0
    fractional_count = 0
    for index, path in enumerate(corrected_files, start=1):
        source_name = f"A01_s{index:03d}_w1_z001_t001.tif"
        raw = tifffile.imread(root / "synthetic" / "TimePoint_1" / source_name)
        corrected = tifffile.imread(path)
        checkpoint = tifffile.imread(output / "checkpoints" / path.name)
        assert corrected.dtype == np.dtype("float32")
        assert corrected.shape == raw.shape == (32, 32)
        np.testing.assert_array_equal(corrected, checkpoint)
        expected = (raw.astype(np.float32) - dark) / flat
        np.testing.assert_allclose(corrected, expected, rtol=2e-6, atol=2e-3)
        max_error = max(max_error, float(np.max(np.abs(corrected - expected))))
        fractional_count += int(np.count_nonzero(corrected != np.floor(corrected)))
    assert fractional_count > 0
    receipts = root / "mcp-installed-paired"
    for index, expected in ((20, tifffile.imread(corrected_files[0])), (21, dark), (22, flat)):
        receipt = json.loads((receipts / f"receipt-{index:03d}.json").read_text())
        assert receipt["returncode"] == 0
        payload = receipt["payload"]["results"][0]["payloads"][0]
        assert payload["observed"] and payload["sample_omitted_count"] == 0
        record = payload["records"][0]
        assert record["components"]["site"] == 1
        np.testing.assert_array_equal(np.asarray(record["array_values"], dtype=np.float32), expected)
    print(json.dumps({"corrected_images": 24, "shape": [32, 32], "dtype": "float32", "max_same_fit_formula_error": max_error, "fractional_pixels": fractional_count, "mcp_exact_full_plane_matches": 3, "flatfield_range": [float(flat.min()), float(flat.max())], "darkfield_nonzero": 0, "pipeline_status": "FAILED_METADATA_PUBLICATION", "biological_acceptance": "NOT_ASSESSED"}))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
