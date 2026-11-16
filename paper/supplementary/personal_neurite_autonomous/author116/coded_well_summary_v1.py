from dataclasses import dataclass
from math import isclose, nan
from typing import cast
from openhcs.core.artifacts import ArtifactSpec, MeasurementsArtifactType, SpecialArtifactType
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs, execution_scope, runtime_bound_parameters
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.runtime_stores import RuntimeArtifactBatch
from openhcs.core.source_metadata import SourceVoxelSpacingUnit
from openhcs.processing.materialization import CsvOptions, MaterializationSpec

SUMMARY_ROWS = ArtifactSpec.input("neurite_outgrowth_summary", MeasurementsArtifactType)
CELL_ROWS = ArtifactSpec.input("neurite_outgrowth_cells", MeasurementsArtifactType)
WELL_OUTPUT = ArtifactSpec.output("coded_well_summary", SpecialArtifactType, materialization=MaterializationSpec(CsvOptions()))

@dataclass(frozen=True)
class CodedWellRow:
    axis_id: str
    paired_fields: int
    detected_cells_field_sum: int
    detected_cells_per_field: float
    rooted_arbor_length_um_field_sum: float
    rooted_arbor_length_um_per_field: float
    rooted_arbor_length_um_per_detected_cell: float
    branches_field_sum: int
    branches_per_field: float
    branches_per_detected_cell: float
    processes_field_sum: int
    processes_per_detected_cell: float
    cells_with_processes: int
    cells_without_processes: int
    mean_process_length_um_pooled_processes: float
    mean_cell_mean_process_length_um_among_process_bearing_cells: float
    mean_cell_max_process_length_um_among_process_bearing_cells: float
    soma_area_um2_field_sum: float
    significant_growth_cells_field_sum: int

@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
@artifact_inputs(SUMMARY_ROWS, CELL_ROWS)
@artifact_outputs(WELL_OUTPUT)
def coded_well_summary_v1(*, artifact_batch: RuntimeArtifactBatch) -> DataclassMeasurementColumnarRows:
    """Aggregate current compiled well axes once, without deduplicating fields.

    Source-bound well axes must be verified in the compiled pipeline. Each
    summary record must contain exactly one paired-field row. Cell totals and
    process/branch totals must reconcile with all corresponding cell records.
    Sum lengths/counts over fields; equal-field averages use paired_fields.
    Cell averages use detected cells. Pooled process mean is summed arbor length
    divided by process count, with absent statistics exported NaN. Per-cell
    means/maxima omit zero-process sentinels and count their denominator.
    No image processing, file reads, treatment decoding or overlap deduction.
    """
    summary = artifact_batch.records(SUMMARY_ROWS.ref())
    cells = artifact_batch.records(CELL_ROWS.ref())
    if set(summary) != set(cells):
        raise ValueError("Summary and cell records have different compiled axes")
    output = []
    for axis_id in sorted(summary):
        field_rows = []
        cell_rows = []
        for record in summary[axis_id]:
            rows = cast(MeasurementTable, record.data).rows
            if rows.row_count() != 1:
                raise ValueError("Expected one summary row per paired field")
            field_rows.extend(rows.iter_row_mappings())
        for record in cells[axis_id]:
            cell_rows.extend(cast(MeasurementTable, record.data).rows.iter_row_mappings())
        if not field_rows or len(summary[axis_id]) != len(cells[axis_id]):
            raise ValueError("Missing paired-field records")
        if any(row["coordinate_unit"] != SourceVoxelSpacingUnit.MICROMETERS for row in field_rows + cell_rows):
            raise ValueError("Summary requires physical micrometer measurements")
        count = sum(int(row["number_of_cells"]) for row in field_rows)
        length = sum(float(row["total_outgrowth"]) for row in field_rows)
        branches = sum(int(row["total_branches"]) for row in field_rows)
        processes = sum(int(row["total_processes"]) for row in field_rows)
        if count != len(cell_rows) or branches != sum(int(row["branches"]) for row in cell_rows) or processes != sum(int(row["processes"]) for row in cell_rows):
            raise ValueError("Field and cell counts do not reconcile")
        if not isclose(length, sum(float(row["total_outgrowth"]) for row in cell_rows), rel_tol=1e-9, abs_tol=1e-6):
            raise ValueError("Field and cell rooted lengths do not reconcile")
        bearing = [row for row in cell_rows if int(row["processes"]) > 0]
        fields = len(field_rows)
        output.append(CodedWellRow(
            axis_id, fields, count, count / fields,
            length, length / fields, length / count if count else nan,
            branches, branches / fields, branches / count if count else nan,
            processes, processes / count if count else nan,
            len(bearing), count - len(bearing), length / processes if processes else nan,
            sum(float(row["mean_process_length"]) for row in bearing) / len(bearing) if bearing else nan,
            sum(float(row["max_process_length"]) for row in bearing) / len(bearing) if bearing else nan,
            sum(float(row["total_cell_body_area"]) for row in field_rows),
            sum(int(row["cells_significant_growth"]) for row in field_rows),
        ))
    return DataclassMeasurementColumnarRows(tuple(output), row_type=CodedWellRow)
