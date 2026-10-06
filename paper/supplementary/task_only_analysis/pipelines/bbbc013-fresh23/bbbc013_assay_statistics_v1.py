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
class AssayRow:
    assay_block: str
    metric: str
    value: float
    negative_wells: int
    positive_wells: int
    replicated_dose_levels: int
    total_wells: int
    minimum_eligibility_fraction: float
    status: str
    formula: str

WELLS = ArtifactSpec.input("well_table", MeasurementsArtifactType)
RESULT = ArtifactSpec.output("assay_statistics", SpecialArtifactType,
    materialization=MaterializationSpec(CsvOptions()))

@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
@artifact_inputs(WELLS)
@artifact_outputs(RESULT)
def bbbc013_assay_statistics_v1(*, artifact_batch: RuntimeArtifactBatch,
    plate_design: tuple[tuple[str, str, str, float], ...] = ()
) -> DataclassMeasurementColumnarRows:
    """Conditional assay statistics on per-well median log2 nucleus/cytoplasm ratio.

    Wells are replicates (sample SD ddof1). Empty-design wells are excluded.
    Zprime=1-3*(SDpositive+SDnegative)/abs(meanpositive-meannegative).
    Replicate-SD V=1-6*mean(SDdose)/range(meanDose), using dose-role groups
    with at least two finite wells. No curve fitting or well weighting by cells.
    Public plate design is supplied by the pipeline, never read from a file.
    """
    design = {well: (block, role, dose) for well, block, role, dose in plate_design}
    groups = {}
    for axis, records in artifact_batch.records(WELLS.ref()).items():
        if axis not in design:
            raise ValueError("Runtime well missing from declared public design: " + axis)
        mappings = [row for record in records for row in cast(MeasurementTable, record.data).rows.row_mappings()]
        if len(mappings) != 1:
            raise ValueError("Expected exactly one site row per well")
        block, role, dose = design[axis]
        row = mappings[0]
        groups.setdefault(block, []).append((role, dose, float(row["median_log2_ratio"]), float(row["eligibility_fraction"])))
    output = []
    for block, observations in sorted(groups.items()):
        neg = [v for role, d, v, f in observations if role == "negative_control" and math.isfinite(v)]
        pos = [v for role, d, v, f in observations if role == "positive_control" and math.isfinite(v)]
        doses = {}
        for role, dose, value, fraction in observations:
            if role == "dose" and math.isfinite(value): doses.setdefault(dose, []).append(value)
        replicated = [v for v in doses.values() if len(v) >= 2]
        fraction = min((f for role, d, v, f in observations if role != "empty"), default=float("nan"))
        z = float("nan")
        if len(neg) >= 2 and len(pos) >= 2:
            span = abs(statistics.mean(pos)-statistics.mean(neg))
            if span > 0: z = 1-3*(statistics.stdev(pos)+statistics.stdev(neg))/span
        vf = float("nan")
        if len(replicated) >= 2:
            means = [statistics.mean(v) for v in replicated]
            span = max(means)-min(means)
            if span > 0: vf = 1-6*statistics.mean(statistics.stdev(v) for v in replicated)/span
        for metric, value, formula in (("Zprime", z, "1-3*(sampleSDpositive+sampleSDnegative)/abs(meanpositive-meannegative)"),
            ("Vfactor_replicate_SD", vf, "1-6*mean(sampleSDdose)/range(meanDose)")):
            status = "conditional_on_masks_and_eligible_cells" if math.isfinite(value) else "insufficient_replicates_or_zero_span"
            output.append(AssayRow(block, metric, value, len(neg), len(pos), len(replicated), len(observations), fraction, status, formula))
    return DataclassMeasurementColumnarRows(tuple(output), row_type=AssayRow)
