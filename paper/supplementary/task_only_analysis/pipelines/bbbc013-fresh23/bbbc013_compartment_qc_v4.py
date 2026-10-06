from dataclasses import dataclass
import numpy as np
from openhcs.core.memory import numpy
from openhcs.core.artifacts import (ArtifactSpec, ImageArtifactType, MainFlowStackOutputSpec,
    MeasurementsArtifactType, ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation,
    InputImageSetContextSourceRelation, ImageMeasurementSubjectRelation)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.core.runtime_object_labels import ObjectLabelValue
from openhcs.core.runtime_measurements import RuntimeMeasurementFeatureOwner
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.materialization import CsvOptions, MaterializationSpec

class CompartmentFeatureOwner(RuntimeMeasurementFeatureOwner):
    @classmethod
    def owns_measurement_feature_name(cls, feature_name: str) -> bool:
        return feature_name in CellRow.__annotations__ or feature_name in WellRow.__annotations__
    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
        return cls.owns_measurement_feature_name(feature_name)

@dataclass(frozen=True)
class CellRow:
    slice_index: int
    object_label: int
    nucleus_area_px: int
    cell_area_px: int
    cytoplasm_area_px: int
    nuclear_gfp_mean: float
    cytoplasmic_gfp_mean: float
    nuclear_cytoplasmic_ratio: float
    log2_ratio: float
    nuclear_saturation_fraction: float
    cytoplasmic_saturation_fraction: float
    eligible: bool
    qc_reason: str

@dataclass(frozen=True)
class WellRow:
    slice_index: int
    nucleus_count: int
    cell_count: int
    eligible_count: int
    eligibility_fraction: float
    mean_ratio: float
    median_ratio: float
    mean_log2_ratio: float
    median_log2_ratio: float
    cyto_absent_count: int
    cyto_small_count: int
    nuclear_saturation_mean: float

SIGNAL = ArtifactSpec.input("gfp_unit", ImageArtifactType, parameter_name="signal")
NUCLEI = ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType, parameter_name="nuclei",
    relations=(InputImageSetContextSourceRelation(SIGNAL.ref()),))
CELLS = ArtifactSpec.input("Cells", ObjectLabelsArtifactType, parameter_name="cells",
    relations=(InputImageSetContextSourceRelation(SIGNAL.ref()),))
IMAGE = MainFlowStackOutputSpec.output("measurement_raw_gfp", ImageArtifactType)
CELL_ROWS = ArtifactSpec.output("cell_table", MeasurementsArtifactType,
    measurement_feature_owner=CompartmentFeatureOwner,
    relations=(ObjectMeasurementSubjectRelation(NUCLEI.ref(), id_field="object_label"),),
    materialization=MaterializationSpec(CsvOptions()))
WELL_ROWS = ArtifactSpec.output("well_table", MeasurementsArtifactType,
    measurement_feature_owner=CompartmentFeatureOwner,
    relations=(ImageMeasurementSubjectRelation(SIGNAL.ref()),),
    materialization=MaterializationSpec(CsvOptions()))

@numpy(contract=ProcessingContract.PURE_2D)
@artifact_inputs(SIGNAL, NUCLEI, CELLS)
@artifact_outputs(CELL_ROWS, WELL_ROWS)
def bbbc013_compartment_qc_v4(image: np.ndarray, *, signal: np.ndarray,
    nuclei: ObjectLabelValue, cells: ObjectLabelValue, minimum_cytoplasm_pixels: int = 20
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows, DataclassMeasurementColumnarRows]:
    """Measure original GFP on matched nucleus/cell IDs; never positionally join rows.

    Cytoplasm is cell support excluding every nuclear pixel. Missing/small or
    zero-signal cytoplasm remains an explicit ineligible row, without imputation.
    Mean units reconstruct acquisition byte codes from verified linear uint8/255 conversion; geometry pixels.
    """
    n = np.asarray(nuclei)
    c = np.asarray(cells)
    unit_signal = np.asarray(signal, dtype=np.float64)
    if np.any(unit_signal < 0) or np.any(unit_signal > 1.000001):
        raise ValueError("Expected catalog linear uint8/255 intensity units")
    s = 255.0 * unit_signal
    if n.shape != s.shape or c.shape != s.shape or s.ndim != 2:
        raise ValueError("Aligned single-plane DNA labels and GFP required")
    if np.any(n < 0) or np.any(c < 0) or not np.isfinite(s).all():
        raise ValueError("Invalid labels or nonfinite source")
    if np.any((n > 0) & (c != n)):
        raise ValueError("Cells do not preserve nucleus seed identities")
    ids = np.unique(n[n > 0])
    if set(np.unique(c[c > 0])) != set(ids):
        raise ValueError("Unexpected missing/extra cell IDs")
    size = int(max(n.max(initial=0), c.max(initial=0))) + 1
    na = np.bincount(n.ravel(), minlength=size)
    ca = np.bincount(c.ravel(), minlength=size)
    cy = np.where(n == 0, c, 0)
    ya = np.bincount(cy.ravel(), minlength=size)
    ns = np.bincount(n.ravel(), weights=s.ravel(), minlength=size)
    ys = np.bincount(cy.ravel(), weights=s.ravel(), minlength=size)
    satn = np.bincount(n.ravel(), weights=(unit_signal >= 1.0).ravel(), minlength=size)
    saty = np.bincount(cy.ravel(), weights=(unit_signal >= 1.0).ravel(), minlength=size)
    rows = []
    for label in ids:
        j = int(label)
        nm = float(ns[j] / na[j])
        ym = float(ys[j] / ya[j]) if ya[j] else float("nan")
        reason = "cytoplasm_absent" if not ya[j] else "cytoplasm_small" if ya[j] < minimum_cytoplasm_pixels else "zero_signal" if ym <= 0 or nm <= 0 else "eligible"
        ok = reason == "eligible"
        ratio = nm / ym if ok else float("nan")
        rows.append(CellRow(0, j, int(na[j]), int(ca[j]), int(ya[j]), nm, ym,
            ratio, float(np.log2(ratio)) if ok else float("nan"),
            float(satn[j]/na[j]), float(saty[j]/ya[j]) if ya[j] else float("nan"), ok, reason))
    good = [r for r in rows if r.eligible]
    def summary(field, mode):
        values = [getattr(r, field) for r in good]
        return float(mode(values)) if values else float("nan")
    well = WellRow(0, len(rows), len(ids), len(good), len(good)/len(rows) if rows else 0.,
        summary("nuclear_cytoplasmic_ratio", np.mean), summary("nuclear_cytoplasmic_ratio", np.median),
        summary("log2_ratio", np.mean), summary("log2_ratio", np.median),
        sum(r.qc_reason == "cytoplasm_absent" for r in rows),
        sum(r.qc_reason == "cytoplasm_small" for r in rows),
        float(np.mean([r.nuclear_saturation_fraction for r in rows])) if rows else float("nan"))
    return image, DataclassMeasurementColumnarRows(tuple(rows), row_type=CellRow), DataclassMeasurementColumnarRows((well,), row_type=WellRow)
