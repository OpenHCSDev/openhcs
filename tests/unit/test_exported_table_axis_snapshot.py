
from tests.unit.saved_output_dialect import SAVED_OUTPUT_POLICY

from benchmark.equivalence.outputs import ExportedTableAxis
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_DIALECT,
)
"""Exporter-owned row domains use physical paths before semantic namespaces."""

from pathlib import Path

import pytest

from benchmark.equivalence.outputs import RuntimeOutputSnapshot
from benchmark.equivalence.runtime import RuntimeMeasurementSnapshot
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.steps.abstract import StepExecutionObservation


def _exports(root: Path, prefix: str, numbers: tuple[int, ...]):
    root.mkdir()
    paths = tuple(
        root / f"{prefix}{subject}.csv" for subject in ("Parents", "Children", "Image")
    )
    paths[0].write_text(
        "ImageNumber,ObjectNumber,Children_Children_Count\n"
        + "".join(f"{number},7,1\n" for number in numbers)
    )
    paths[1].write_text(
        "ImageNumber,ObjectNumber,Parent_Parents\n"
        + "".join(f"{number},11,7\n" for number in numbers)
    )
    paths[2].write_text(
        "ImageNumber,Count_Parents,Count_Children\n"
        + "".join(f"{number},1,1\n" for number in numbers)
    )
    return RuntimeExportObservation.from_output_root(
        root,
        outputs=StepExecutionObservation(
            {},
            sample_numbers_by_export_path={
                path: {
                    f"W{index + 1:03}": (number,)
                    for index, number in enumerate(numbers)
                }
                for path in paths
            },
        ),
    )


@pytest.mark.parametrize("prefix", ("", "experiment_", "plate_3d_"))
@pytest.mark.parametrize("axis", ("W001", "W002"))
def test_prefixed_axis_snapshot_preserves_exact_relationships(tmp_path, prefix, axis):
    native = _exports(tmp_path / "native", prefix, (1,))
    candidate = _exports(tmp_path / "candidate", prefix, (1, 2))
    physical_contents = {path: path.read_bytes() for path in candidate.output_files}
    snapshot = RuntimeOutputSnapshot.from_export_observation(
        candidate.for_execution_axis(axis), execution_axis=ExportedTableAxis(axis, CELLPROFILER_MEASUREMENT_DIALECT)
    )
    assert all(len(table.rows) == 1 for table in snapshot.tables)
    number = "1" if axis == "W001" else "2"
    assert all(table.rows[0][0] == number for table in snapshot.tables)
    assert {table.path.name for table in snapshot.tables} == {
        "Parents.csv",
        "Children.csv",
        "Image.csv",
    }
    reference = RuntimeMeasurementSnapshot.from_output_snapshot(
        RuntimeOutputSnapshot.from_export_observation(native), policy=SAVED_OUTPUT_POLICY
    )
    actual = RuntimeMeasurementSnapshot.from_output_snapshot(snapshot, policy=SAVED_OUTPUT_POLICY)
    assert (
        actual.required_relationship_correlations()
        == reference.required_relationship_correlations()
    )
    assert {
        path: path.read_bytes() for path in candidate.output_files
    } == physical_contents


def test_prefixed_axis_snapshot_still_rejects_absent_parent(tmp_path):
    candidate = _exports(tmp_path / "candidate", "experiment_", (1, 2))
    path = tmp_path / "candidate/experiment_Children.csv"
    path.write_text("ImageNumber,ObjectNumber,Parent_Parents\n1,11,7\n2,11,8\n")
    snapshot = RuntimeOutputSnapshot.from_export_observation(
        candidate.for_execution_axis("W002"), execution_axis=ExportedTableAxis("W002", CELLPROFILER_MEASUREMENT_DIALECT)
    )
    with pytest.raises(ValueError, match="absent parent endpoint"):
        RuntimeMeasurementSnapshot.from_output_snapshot(snapshot, policy=SAVED_OUTPUT_POLICY)


def test_prefixed_axis_snapshot_still_rejects_unowned_image_id(tmp_path):
    candidate = _exports(tmp_path / "candidate", "experiment_", (1, 2))
    path = tmp_path / "candidate/experiment_Children.csv"
    path.write_text("ImageNumber,ObjectNumber,Parent_Parents\n1,11,7\n3,11,7\n")
    with pytest.raises(ValueError, match="unowned image identity"):
        RuntimeOutputSnapshot.from_export_observation(
            candidate.for_execution_axis("W002"), execution_axis=ExportedTableAxis("W002", CELLPROFILER_MEASUREMENT_DIALECT)
        )
