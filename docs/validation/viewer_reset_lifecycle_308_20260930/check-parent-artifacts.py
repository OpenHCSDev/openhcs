"""Read-only assertions against persisted live MCP receipts and TIFF outputs."""

import json
from pathlib import Path

import numpy as np
import tifffile

from openhcs.processing.backends.processors.numpy_processor import gaussian_blur

ledger = Path(
    "/home/ts/wt/openhcs-issue-batch-20260929/viewer-reset-parent-20260930"
)
receipts = ledger / "attempt02"


def payload(index):
    receipt = json.loads((receipts / f"receipt-{index:03d}.json").read_text())
    assert receipt["returncode"] == 0, receipt
    assert not receipt["payload"]["errors"], receipt
    result = receipt["payload"]["results"][0]
    assert not result["mcp_error"], result
    return result["payloads"][0]


state = payload(29)
assert state["observed"] and state["layer_count"] == 2
raw, processed = state["layers"]
assert raw["item_count"] == 1 and processed["item_count"] == 2
assert processed["axis_component_values"]["well"] == ["A01", "B01"]
for layer in (raw, processed):
    assert layer["mounted"] and not layer["pending_update"]
    assert layer["native_transform"]["scale"][-2:] == [0.65, 0.65]
    assert layer["native_transform"]["translate"][-2:] == [0.0, 0.0]

for well in ("A01", "B01"):
    filename = f"{well}_s001_w1_z001_t001.tif"
    original = tifffile.imread(ledger / "synthetic" / "TimePoint_1" / filename)
    expected = gaussian_blur(original[np.newaxis], sigma=1.0)[0]
    for output_kind in ("images", "checkpoints"):
        actual = tifffile.imread(
            ledger / "outputs" / "synthetic_openhcs" / output_kind / filename
        )
        np.testing.assert_array_equal(actual, expected)
        assert actual.dtype == original.dtype == np.uint16

for index, image in ((30, "raw"), (31, "processed")):
    record = payload(index)["records"][0]
    assert record["components"]["well"] == "A01"
    filename = "A01_s001_w1_z001_t001.tif"
    path = (
        ledger / "synthetic" / "TimePoint_1" / filename
        if image == "raw"
        else ledger / "outputs" / "synthetic_openhcs" / "images" / filename
    )
    np.testing.assert_array_equal(
        np.asarray(record["array_values"]), tifffile.imread(path)[20:36, 20:36]
    )

print("PASS: two persisted wells/checkpoints and mounted raw/result samples match")
