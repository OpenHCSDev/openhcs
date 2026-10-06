from dataclasses import dataclass
from typing import cast
import math
import statistics
from openhcs.core.artifacts import ArtifactSpec, MeasurementsArtifactType, SpecialArtifactType
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs, execution_scope, runtime_bound_parameters
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.runtime_stores import RuntimeArtifactBatch
from openhcs.processing.materialization import CsvOptions, MaterializationSpec

@dataclass(frozen=True)
class DoseRow:
    assay_block: str
    assay_role: str
    concentration: float
    concentration_unit: str
    treatment: str
    well_count: int
    finite_well_count: int
    mean_well_median_log2_ratio: float
    sd_well_median_log2_ratio: float
    sem_well_median_log2_ratio: float
    minimum_eligibility_fraction: float
    total_nuclei: int
    eligible_cells: int
    status: str

WELLS = ArtifactSpec.input("well_table", MeasurementsArtifactType)
RESULT = ArtifactSpec.output("dose_response_table", SpecialArtifactType,
    materialization=MaterializationSpec(CsvOptions()))

@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
@artifact_inputs(WELLS)
@artifact_outputs(RESULT)
def bbbc013_dose_response_v2(*, artifact_batch: RuntimeArtifactBatch,
    plate_design: tuple[tuple[str, str, str, float], ...] = (),
    source_metadata: tuple[tuple[str, str, str], ...] = ()
) -> DataclassMeasurementColumnarRows:
    """Dose points over independent wells; retain exclusions and sample SD/SEM.

    Empty-design wells appear as an excluded QC group, not a zero-cell control.
    No fitted EC50 or uncertainty from cell pseudoreplication is reported.
    """
    design = {well: (block, role, dose) for well, block, role, dose in plate_design}
    metadata = {well: (unit, treatment) for well, unit, treatment in source_metadata}
    groups = {}
    for axis, records in artifact_batch.records(WELLS.ref()).items():
        if axis not in design: raise ValueError("Missing declared design for " + axis)
        rows = [row for record in records for row in cast(MeasurementTable, record.data).rows.row_mappings()]
        if len(rows) != 1: raise ValueError("Expected one site per runtime well")
        if axis not in metadata: raise ValueError("Missing source dose units/treatment for " + axis)
        groups.setdefault((*design[axis], *metadata[axis]), []).append(rows[0])
    output = []
    for (block, role, dose, unit, treatment), rows in sorted(groups.items()):
        values = [float(r["median_log2_ratio"]) for r in rows if math.isfinite(float(r["median_log2_ratio"]))]
        mean = statistics.mean(values) if values else float("nan")
        sd = statistics.stdev(values) if len(values) >= 2 else float("nan")
        status = "excluded_empty_design_qc" if role == "empty" else "conditional_on_masks_and_eligible_cells"
        output.append(DoseRow(block, role, dose, unit, treatment, len(rows), len(values), mean, sd,
            sd/math.sqrt(len(values)) if values else float("nan"),
            min(float(r["eligibility_fraction"]) for r in rows),
            sum(int(r["nucleus_count"]) for r in rows), sum(int(r["eligible_count"]) for r in rows), status))
    return DataclassMeasurementColumnarRows(tuple(output), row_type=DoseRow)
