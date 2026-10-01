"""Read-only verification of the installed two-well synthetic export control."""

import csv
import json
from pathlib import Path

import numpy as np
import tifffile

from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
)
from openhcs.runtime.zmq_execution_observation import ZMQRuntimeExecutionObservationExport


def main(root: Path) -> None:
    receipts = root / "mcp-image-copy-reconnected"
    status = json.loads((receipts / "receipt-017.json").read_text())
    execution = status["payload"]["results"][0]["payloads"][0]
    assert status["returncode"] == 0
    assert execution["status"] == "complete"
    assert execution["response"]["execution"]["error"] is None
    inventory_receipt = json.loads((receipts / "receipt-020.json").read_text())
    inventory = inventory_receipt["payload"]["results"][0]["payloads"][0]
    assert inventory_receipt["returncode"] == 0
    assert inventory["total_count"] == inventory["returned_count"] == 16
    assert inventory["truncated_count"] == 0
    cells_record = next(record for record in inventory["records"] if record["key"] == "Cells.csv")
    assert cells_record["preview"]["truncated"] is False
    cells = cells_record["preview"]["csv_rows"]
    assert len(cells) == 4
    assert {(row["image_number"], row["object_label"]) for row in cells} == {
        ("1", "1"), ("1", "2"), ("2", "1"), ("2", "2"),
    }
    for row in cells:
        assert row["Parent_Nuclei"] == row["object_label"]
        assert float(row["AreaShape_Area"]) == 52.0
        assert float(row["Location_Center_X"]) == float(row["AreaShape_Center_X"])
        assert float(row["Location_Center_Y"]) == float(row["AreaShape_Center_Y"])
        assert all(value != "" for value in row.values())

    output = root / "outputs-input-source-fixed" / "synthetic_openhcs"
    with (output / "results" / "Cells.csv").open(newline="") as handle:
        assert list(csv.DictReader(handle)) == cells
    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        output, json.loads((output / "openhcs_metadata.json").read_text()),
    )
    assert len({(ref.backend, ref.backend_address)
                for ref in projection.source_refs_by_virtual_path.values()}) == 4
    for well in ("A01", "B01"):
        for channel, name, step in (("1", "Nuclei", 0), ("2", "Cells", 1)):
            relative = f"results/{well}_w{channel}_{name}_step{step}.labels.tif"
            lookup = VirtualWorkspacePathLookup(relative, str(output / relative))
            source_projection = projection.require_source_projection_for(lookup)
            assert source_projection.ref.backend == "disk"
            assert source_projection.ref.backend_address == relative
            assert source_projection.image_metadata.source_spatial_domain.source_shape_yx == (32, 32)
        nuclei = tifffile.imread(output / "results" / f"{well}_w1_Nuclei_step0.labels.tif")
        expected_nuclei = np.zeros((32, 32), dtype=np.int32)
        expected_nuclei[5:9, 5:9] = 1
        expected_nuclei[22:26, 22:26] = 2
        np.testing.assert_array_equal(nuclei.squeeze(), expected_nuclei)
        cell_labels = tifffile.imread(output / "results" / f"{well}_w2_Cells_step1.labels.tif")
        assert set(np.unique(cell_labels)) == {0, 1, 2}
        assert np.count_nonzero(cell_labels == 1) == np.count_nonzero(cell_labels == 2) == 52
        dna = tifffile.imread(root / "synthetic" / "TimePoint_1" / f"{well}_s001_w1_z001_t001.tif")
        expected_dna = np.zeros((32, 32), dtype=np.uint16)
        expected_dna[5:9, 5:9] = 12000
        expected_dna[22:26, 22:26] = 18000
        np.testing.assert_array_equal(dna, expected_dna)
        actin = tifffile.imread(root / "synthetic" / "TimePoint_1" / f"{well}_s001_w2_z001_t001.tif")
        np.testing.assert_array_equal(actin, np.full((32, 32), 24000, dtype=np.uint16))

    observation = ZMQRuntimeExecutionObservationExport.read(
        root / "runtime-observation-input-source-fixed.json",
    )
    assert observation.execution_id == "bb932c48-de7a-4867-bbb2-5a090a5aa928"
    assert dict(observation.execution_success_by_axis) == {"A01": True, "B01": True}
    close_receipt = json.loads((receipts / "receipt-021.json").read_text())
    outcome = close_receipt["payload"]["results"][0]["payloads"][0]["outcome"]
    assert outcome["request_attempted"] and outcome["acknowledged"] and outcome["process_exited"]
    print("PASS: installed COMPLETE; four complete paired cell rows; four label projections; "
          "known source pixels unchanged; native export reopens; exact worker closed. "
          "Physical calibration and biological accuracy are not assessed by this control.")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    main(parser.parse_args().root)
