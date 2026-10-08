from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import pickle

from openhcs.core.artifacts import (
    ArtifactSpec,
    MeasurementsArtifactType,
)
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
    MeasurementProjectedColumnarRows,
)
from openhcs.core.runtime_artifact_values import (
    ArtifactKey,
    RuntimeValue,
)
from openhcs.core.runtime_exports import (
    RuntimeExportExpectation,
    RuntimeExportObservation,
    runtime_export_failures,
)
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.runtime_tabular_values import (
    FieldSpec,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
)
from openhcs.core.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeArtifactLocation,
    StoredRuntimeValue,
)
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.processing.materialization import CsvOptions, MaterializationSpec
from openhcs.processing.materialization.core import ColumnarCsvOutput


def test_export_observation_uses_saved_writer_shape_without_reading_csv(
    tmp_path: Path, monkeypatch,
) -> None:
    path = tmp_path / "measurements.csv"
    rows = _measurement_rows(0, 1)
    output = ColumnarCsvOutput(path=str(path), content=rows).rendered()
    path.write_bytes(output.content)
    location = RuntimeArtifactLocation.from_output(output, "disk")
    location = RuntimeArtifactLocation.from_dict(location.to_dict())
    record = _stored_measurements_record(rows=rows)
    saved = StepExecutionObservation(
        {RuntimeArtifactAddress.from_record(record): (location,)},
        runtime_export_paths=(path,),
    )

    def unexpected_read(*args, **kwargs):
        raise AssertionError("Saved tables must use their writer's shape.")

    monkeypatch.setattr(Path, "open", unexpected_read)
    observation = RuntimeExportObservation.from_output_paths((path,), outputs=saved)
    assert observation.table_headers_by_path == {path: ("slice_index",)}
    assert observation.table_row_counts_by_path == {path: 2}
    assert location == RuntimeArtifactLocation(str(path), "disk")


def test_external_export_shape_counts_multiline_records_once(tmp_path: Path) -> None:
    path = tmp_path / "external.csv"
    path.write_text('"header\ncontinued",second\n"value\ncontinued",2\n', encoding="utf-8")
    observation = RuntimeExportObservation.from_output_paths((path,))
    assert observation.table_headers_by_path == {path: ("header\ncontinued", "second")}
    assert observation.table_row_counts_by_path == {path: 1}


def test_saved_output_combine_keeps_latest_facts_and_first_destination_order(
    tmp_path: Path,
) -> None:
    from openhcs.core.orchestrator.execution_result import (
        RuntimeExecutionTransportSerialization,
    )

    first_path = tmp_path / "first.csv"
    second_path = tmp_path / "second.csv"
    first_path.write_text("updated\n1\n2\n3\n", encoding="utf-8")
    second_path.write_text("external\n4\n", encoding="utf-8")
    record = _stored_measurements_record(path=first_path)
    address = RuntimeArtifactAddress.from_record(record)
    first_old = RuntimeArtifactLocation(
        str(first_path), "disk", table_header=("old",), table_row_count=2
    )
    second_old = RuntimeArtifactLocation(
        str(second_path), "disk", table_header=("stale",), table_row_count=2
    )
    first_latest = RuntimeArtifactLocation(
        str(first_path), "disk", table_header=("updated",), table_row_count=3
    )
    second_latest = RuntimeArtifactLocation(str(second_path), "disk")
    combined = StepExecutionObservation.combine(
        (
            StepExecutionObservation({address: (first_old, second_old)}),
            StepExecutionObservation({address: (first_latest,)}),
            StepExecutionObservation({address: (second_latest,)}),
        )
    )
    RuntimeExecutionTransportSerialization.register()
    transported = pickle.loads(pickle.dumps(combined))
    locations = transported.materialized_locations_by_address[address]
    assert tuple(location.path for location in locations) == (
        str(first_path), str(second_path)
    )
    assert locations[0].table_header == ("updated",)
    assert locations[0].table_row_count == 3
    assert locations[1].table_header is None
    assert locations[1].table_row_count is None
    observation = RuntimeExportObservation.from_output_paths(
        (first_path, second_path), outputs=transported
    )
    assert observation.table_headers_by_path == {
        first_path: ("updated",), second_path: ("external",)
    }
    assert observation.table_row_counts_by_path == {first_path: 3, second_path: 1}


def test_runtime_export_validation_accepts_header_only_empty_table(
    tmp_path: Path,
) -> None:
    table_path = tmp_path / "A01_Measurements_step1.csv"
    table_path.write_text("slice_index\n", encoding="utf-8")
    record = _stored_measurements_record(path=table_path)

    failures = runtime_export_failures(
        _table_export_expectation(),
        RuntimeExportObservation.from_output_root(
            tmp_path, outputs=_saved_outputs(record)
        ),
        {"A01": (record,)},
    )

    assert failures == ()


def test_runtime_export_validation_accepts_header_only_empty_column_table(
    tmp_path: Path,
) -> None:
    table_path = tmp_path / "A01_Measurements_step1.csv"
    table_path.write_text("slice_index\n", encoding="utf-8")
    record = _stored_measurements_record(
        path=table_path,
        rows=MeasurementProjectedColumnarRows(
            columns={"slice_index": ()},
            fields=(FieldSpec("slice_index", int),),
        )
    )

    failures = runtime_export_failures(
        _table_export_expectation(),
        RuntimeExportObservation.from_output_root(
            tmp_path, outputs=_saved_outputs(record)
        ),
        {"A01": (record,)},
    )

    assert failures == ()


def test_runtime_export_validation_rejects_header_only_nonempty_table(
    tmp_path: Path,
) -> None:
    table_path = tmp_path / "A01_Measurements_step1.csv"
    table_path.write_text("slice_index\n", encoding="utf-8")
    record = _stored_measurements_record(path=table_path, rows=_measurement_rows(0))

    failures = runtime_export_failures(
        _table_export_expectation(),
        RuntimeExportObservation.from_output_root(
            tmp_path, outputs=_saved_outputs(record)
        ),
        {"A01": (record,)},
    )

    assert failures == (f"table output {table_path} has no data rows",)


def test_runtime_export_validation_checks_table_schema_fields(
    tmp_path: Path,
) -> None:
    table_path = tmp_path / "A01_Measurements_step1.csv"
    table_path.write_text("wrong_field\n0\n", encoding="utf-8")
    record = _stored_measurements_record(path=table_path, rows=_measurement_rows(0))

    failures = runtime_export_failures(
        _table_export_expectation(),
        RuntimeExportObservation.from_output_root(
            tmp_path, outputs=_saved_outputs(record)
        ),
        {"A01": (record,)},
    )

    assert failures == (
        f"table output {table_path} for artifact 'Measurements' is "
        "missing schema fields ('slice_index',)",
    )


def test_runtime_export_validation_scopes_table_outputs_by_axis(
    tmp_path: Path,
) -> None:
    a01_table_path = tmp_path / "A01_Measurements_step1.csv"
    a02_table_path = tmp_path / "A02_Measurements_step1.csv"
    a01_table_path.write_text("slice_index\n", encoding="utf-8")
    a02_table_path.write_text("slice_index\n0\n", encoding="utf-8")
    a01_record = _stored_measurements_record(path=a01_table_path, axis_id="A01")
    a02_record = _stored_measurements_record(
        path=a02_table_path,
        axis_id="A02",
        rows=_measurement_rows(0),
    )

    failures = runtime_export_failures(
        _table_export_expectation(),
        RuntimeExportObservation.from_output_root(
            tmp_path, outputs=_saved_outputs(a01_record, a02_record)
        ),
        {"A01": (a01_record,), "A02": (a02_record,)},
    )

    assert failures == ()


def test_runtime_export_validation_accepts_format_compatible_schema_fields(
    tmp_path: Path,
) -> None:
    table_path = tmp_path / "A01_Measurements_step1.csv"
    table_path.write_text("SliceIndex\n0\n", encoding="utf-8")
    record = _stored_measurements_record(path=table_path, rows=_measurement_rows(0))

    failures = runtime_export_failures(
        _table_export_expectation(),
        RuntimeExportObservation.from_output_root(
            tmp_path, outputs=_saved_outputs(record)
        ),
        {"A01": (record,)},
    )

    assert failures == ()


@dataclass(frozen=True, slots=True)
class _RuntimeExportMeasurementRow:
    slice_index: int


def _measurement_rows(*slice_indices: int) -> DataclassMeasurementColumnarRows:
    return DataclassMeasurementColumnarRows(
        tuple(_RuntimeExportMeasurementRow(value) for value in slice_indices),
        row_type=_RuntimeExportMeasurementRow,
    )


def _saved_outputs(*records: StoredRuntimeValue) -> StepExecutionObservation:
    return StepExecutionObservation(
        {
            RuntimeArtifactAddress.from_record(record): (record.location,)
            for record in records
        }
    )


def _stored_measurements_record(
    *,
    path: Path | None = None,
    axis_id: str = "A01",
    rows: ColumnarRows | None = None,
) -> StoredRuntimeValue:
    if rows is None:
        rows = _measurement_rows()
    value = RuntimeValue(
        key=ArtifactKey(
            name="Measurements",
            artifact_type=MeasurementsArtifactType,
            scope=RuntimeExecutionAxisScope(axis_id=axis_id),
        ),
        data=MeasurementTable(
            name="Measurements",
            rows=rows,
            subject=MeasurementSubject(MeasurementScope.ARTIFACT, "Measurements"),
        ),
    )
    return StoredRuntimeValue(
               key=value.key,
               data=value.data,
               materialization_source_metadata=value.materialization_source_metadata,
               location=RuntimeArtifactLocation(
                   path=str(path) if path is not None else f"results/{axis_id}_Measurements_step1.csv",
                   backend="disk",
               ),
           )


def _table_export_expectation() -> RuntimeExportExpectation:
    return RuntimeExportExpectation.from_output_specs(
        (
            ArtifactSpec.output(
                "Measurements",
                MeasurementsArtifactType,
                materialization=MaterializationSpec(CsvOptions(filename_suffix=".csv")),
            ),
        )
    )
