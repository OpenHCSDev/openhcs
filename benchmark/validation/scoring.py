"""Trusted scoring for independently referenced image-analysis corpora."""

from __future__ import annotations

import csv
import json
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import ClassVar

import imageio.v3 as iio
import numpy as np
from metaclass_registry import AutoRegisterMeta
from scipy.ndimage import binary_dilation, distance_transform_edt
from scipy.optimize import linear_sum_assignment
from skimage.segmentation import find_boundaries, relabel_sequential

from benchmark.contracts.validation import (
    PublishedAssayReference,
    ValidationAssayRole,
    ValidationEvidenceKind,
    ValidationMetricProfile,
)
from benchmark.datasets.registry import get_dataset_spec
from benchmark.validation.corpus import verify_frozen_pipeline
from benchmark.validation.references import ValidationReferenceStrategy


class ValidationScoringError(ValueError):
    """Raised when trusted scoring inputs violate the declared contract."""


@dataclass(frozen=True, slots=True)
class PredictionRecord:
    """One materialized label artifact supplied by a frozen pipeline."""

    source_set_id: str
    channel: str
    relative_path: Path


@dataclass(frozen=True, slots=True)
class InstanceSegmentationMetrics:
    """Object-level metrics for one predicted/reference label pair."""

    source_set_id: str
    channel: str
    reference_count: int
    predicted_count: int
    true_positive_count: int
    false_positive_count: int
    false_negative_count: int
    precision: float
    recall: float
    f1: float
    mean_matched_iou: float
    panoptic_quality: float
    aggregated_jaccard_index: float
    split_reference_count: int
    merged_prediction_count: int
    count_error: int
    relative_count_error: float


@dataclass(frozen=True, slots=True)
class BoundarySegmentationMetrics:
    """Published BBBC007 boundary score plus symmetric boundary diagnostics."""

    source_set_id: str
    channel: str
    relevant_predicted_boundary_pixels: int
    relevant_boundary_within_two_pixels: float
    boundary_precision_within_two_pixels: float
    boundary_recall_within_two_pixels: float
    boundary_f1_within_two_pixels: float


@dataclass(frozen=True, slots=True)
class AssayQualityMetrics:
    """Plate-level assay statistics for one BBBC013 treatment block."""

    treatment: str
    negative_control_count: int
    positive_control_count: int
    z_prime: float
    replicate_sd_v_factor: float
    dose_response_means: tuple[tuple[float, float], ...]


@dataclass(frozen=True, slots=True)
class AssayMeasurementRecord:
    """One pipeline measurement joined to declaration-derived plate metadata."""

    well: str
    assay_block: str
    treatment: str
    concentration: float
    assay_role: ValidationAssayRole
    value: float


@dataclass(frozen=True, slots=True)
class ValidationScoreReport:
    """Typed result of scoring one hash-frozen pipeline execution."""

    dataset_id: str
    pipeline_sha256: str
    metric_profile: ValidationMetricProfile
    instance_metrics: tuple[InstanceSegmentationMetrics, ...] = ()
    boundary_metrics: tuple[BoundarySegmentationMetrics, ...] = ()
    assay_metrics: tuple[AssayQualityMetrics, ...] = ()
    published_assay_references: tuple[PublishedAssayReference, ...] = ()


class ValidationScoringStrategy(ABC, metaclass=AutoRegisterMeta):
    """Score one declaration-owned metric profile after pipeline freeze."""

    __registry_key__ = "metric_profile"
    __skip_if_no_key__ = True
    metric_profile: ClassVar[ValidationMetricProfile | None] = None

    @classmethod
    def for_profile(cls, profile: ValidationMetricProfile) -> ValidationScoringStrategy:
        try:
            strategy_type = cls.__registry__[profile]
        except KeyError as exc:
            raise ValidationScoringError(
                f"No validation scorer is registered for {profile.value!r}."
            ) from exc
        return strategy_type()

    @abstractmethod
    def score(
        self,
        dataset_id: str,
        *,
        scoring_root: Path,
        result_path: Path,
        pipeline_sha256: str,
    ) -> ValidationScoreReport:
        """Score a frozen result against a trusted reference surface."""


class InstanceSegmentationScorer(ValidationScoringStrategy):
    """Score BBBC039 decoded instance masks."""

    metric_profile = ValidationMetricProfile.INSTANCE_SEGMENTATION

    def score(
        self,
        dataset_id: str,
        *,
        scoring_root: Path,
        result_path: Path,
        pipeline_sha256: str,
    ) -> ValidationScoreReport:
        predictions = _read_prediction_manifest(result_path)
        references = _read_reference_manifest(scoring_root)
        _require_same_keys(predictions, references)
        metrics = tuple(
            instance_segmentation_metrics(
                _load_label_array(
                    _resolved_result_artifact(result_path, prediction.relative_path)
                ),
                ValidationReferenceStrategy.for_evidence(
                    ValidationEvidenceKind.INSTANCE_MASKS
                ).load(scoring_root / reference.relative_path),
                source_set_id=source_set_id,
                channel=channel,
            )
            for (source_set_id, channel), prediction in sorted(predictions.items())
            for reference in (references[(source_set_id, channel)],)
        )
        return ValidationScoreReport(
            dataset_id=dataset_id,
            pipeline_sha256=pipeline_sha256,
            metric_profile=self.metric_profile,
            instance_metrics=metrics,
        )


class BoundaryAndInstanceScorer(ValidationScoringStrategy):
    """Score BBBC007 full manual outlines at boundary and object levels."""

    metric_profile = ValidationMetricProfile.BOUNDARY_AND_INSTANCE

    def score(
        self,
        dataset_id: str,
        *,
        scoring_root: Path,
        result_path: Path,
        pipeline_sha256: str,
    ) -> ValidationScoreReport:
        predictions = _read_prediction_manifest(result_path)
        references = _read_reference_manifest(scoring_root)
        _require_same_keys(predictions, references)
        instance_results: list[InstanceSegmentationMetrics] = []
        boundary_results: list[BoundarySegmentationMetrics] = []
        for key, prediction in sorted(predictions.items()):
            source_set_id, channel = key
            predicted_labels = _load_label_array(
                _resolved_result_artifact(result_path, prediction.relative_path)
            )
            reference_labels = ValidationReferenceStrategy.for_evidence(
                ValidationEvidenceKind.MANUAL_OUTLINES
            ).load(scoring_root / references[key].relative_path)
            instance_results.append(
                instance_segmentation_metrics(
                    predicted_labels,
                    reference_labels,
                    source_set_id=source_set_id,
                    channel=channel,
                )
            )
            boundary_results.append(
                boundary_segmentation_metrics(
                    predicted_labels,
                    reference_labels,
                    source_set_id=source_set_id,
                    channel=channel,
                )
            )
        return ValidationScoreReport(
            dataset_id=dataset_id,
            pipeline_sha256=pipeline_sha256,
            metric_profile=self.metric_profile,
            instance_metrics=tuple(instance_results),
            boundary_metrics=tuple(boundary_results),
        )


class TranslocationAssayScorer(ValidationScoringStrategy):
    """Score BBBC013 biological plate behavior without claiming pixel ground truth."""

    metric_profile = ValidationMetricProfile.TRANSLOCATION_ASSAY

    def score(
        self,
        dataset_id: str,
        *,
        scoring_root: Path,
        result_path: Path,
        pipeline_sha256: str,
    ) -> ValidationScoreReport:
        rows = _read_assay_results(
            result_path,
            source_manifest_path=scoring_root / "source_manifest.csv",
        )
        metrics = tuple(
            assay_quality_metrics(rows, treatment=treatment)
            for treatment in ("Wortmannin", "LY294002")
        )
        return ValidationScoreReport(
            dataset_id=dataset_id,
            pipeline_sha256=pipeline_sha256,
            metric_profile=self.metric_profile,
            assay_metrics=metrics,
        )


def score_validation_corpus(
    dataset_id: str,
    *,
    corpus_root: Path,
    result_path: Path,
    report_path: Path | None = None,
) -> ValidationScoreReport:
    """Verify pipeline immutability, then score through the declared metric owner."""

    receipt = verify_frozen_pipeline(dataset_id, corpus_root=corpus_root)
    spec = get_dataset_spec(dataset_id)
    validation = spec.independent_validation
    if validation is None:
        raise ValidationScoringError(
            f"Dataset {dataset_id!r} has no independent-validation declaration."
        )
    scoring_root = Path(corpus_root).resolve() / dataset_id / "trusted_scoring"
    report = ValidationScoringStrategy.for_profile(validation.metric_profile).score(
        dataset_id,
        scoring_root=scoring_root,
        result_path=Path(result_path).resolve(),
        pipeline_sha256=receipt.pipeline_sha256,
    )
    report = replace(
        report,
        published_assay_references=validation.published_assay_references,
    )
    if report_path is not None:
        report_path = Path(report_path).resolve()
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(_jsonable(asdict(report)), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    return report


def instance_segmentation_metrics(
    predicted_labels: np.ndarray,
    reference_labels: np.ndarray,
    *,
    source_set_id: str,
    channel: str,
    match_iou: float = 0.5,
) -> InstanceSegmentationMetrics:
    """Compute one-to-one IoU, AJI+, PQ, split/merge, and count metrics."""

    predicted = _canonical_labels(predicted_labels)
    reference = _canonical_labels(reference_labels)
    if predicted.shape != reference.shape:
        raise ValidationScoringError(
            f"Prediction/reference shapes differ: {predicted.shape} != {reference.shape}."
        )
    intersections, pred_areas, ref_areas = _contingency(predicted, reference)
    unions = pred_areas[:, None] + ref_areas[None, :] - intersections
    iou = np.divide(
        intersections,
        unions,
        out=np.zeros_like(intersections, dtype=float),
        where=unions > 0,
    )
    if iou.size:
        pred_indexes, ref_indexes = linear_sum_assignment(-iou)
        positive = intersections[pred_indexes, ref_indexes] > 0
        pred_indexes = pred_indexes[positive]
        ref_indexes = ref_indexes[positive]
    else:
        pred_indexes = np.empty(0, dtype=int)
        ref_indexes = np.empty(0, dtype=int)
    assigned_iou = iou[pred_indexes, ref_indexes]
    accepted = assigned_iou >= match_iou
    true_positives = int(np.count_nonzero(accepted))
    predicted_count = int(pred_areas.size)
    reference_count = int(ref_areas.size)
    false_positives = predicted_count - true_positives
    false_negatives = reference_count - true_positives
    precision = _safe_ratio(true_positives, true_positives + false_positives)
    recall = _safe_ratio(true_positives, true_positives + false_negatives)
    f1 = _safe_ratio(2 * precision * recall, precision + recall)
    accepted_ious = assigned_iou[accepted]
    pq = _safe_ratio(
        float(accepted_ious.sum()),
        true_positives + 0.5 * false_positives + 0.5 * false_negatives,
    )
    matched_intersection = float(intersections[pred_indexes, ref_indexes].sum())
    matched_union = float(unions[pred_indexes, ref_indexes].sum())
    unmatched_pred = np.delete(pred_areas, pred_indexes).sum()
    unmatched_ref = np.delete(ref_areas, ref_indexes).sum()
    aji = _safe_ratio(
        matched_intersection,
        matched_union + float(unmatched_pred) + float(unmatched_ref),
    )
    overlap = intersections > 0
    split_count = int(np.count_nonzero(overlap.sum(axis=0) > 1))
    merge_count = int(np.count_nonzero(overlap.sum(axis=1) > 1))
    count_error = predicted_count - reference_count
    return InstanceSegmentationMetrics(
        source_set_id=source_set_id,
        channel=channel,
        reference_count=reference_count,
        predicted_count=predicted_count,
        true_positive_count=true_positives,
        false_positive_count=false_positives,
        false_negative_count=false_negatives,
        precision=precision,
        recall=recall,
        f1=f1,
        mean_matched_iou=float(accepted_ious.mean()) if accepted_ious.size else 0.0,
        panoptic_quality=pq,
        aggregated_jaccard_index=aji,
        split_reference_count=split_count,
        merged_prediction_count=merge_count,
        count_error=count_error,
        relative_count_error=_safe_ratio(abs(count_error), reference_count),
    )


def boundary_segmentation_metrics(
    predicted_labels: np.ndarray,
    reference_labels: np.ndarray,
    *,
    source_set_id: str,
    channel: str,
) -> BoundarySegmentationMetrics:
    """Compute BBBC007's directed <=2 px score and symmetric diagnostics."""

    predicted = _canonical_labels(predicted_labels)
    reference = _canonical_labels(reference_labels)
    if predicted.shape != reference.shape:
        raise ValidationScoringError(
            f"Prediction/reference shapes differ: {predicted.shape} != {reference.shape}."
        )
    predicted_boundary = find_boundaries(predicted, mode="inner")
    reference_boundary = find_boundaries(reference, mode="inner")
    adjacent_to_background = binary_dilation(predicted == 0, structure=np.ones((3, 3)))
    relevant = predicted_boundary & ~adjacent_to_background
    distance_to_reference = distance_transform_edt(~reference_boundary)
    distance_to_prediction = distance_transform_edt(~predicted_boundary)
    relevant_score = _masked_fraction(distance_to_reference <= 2.0, relevant)
    precision = _masked_fraction(distance_to_reference <= 2.0, predicted_boundary)
    recall = _masked_fraction(distance_to_prediction <= 2.0, reference_boundary)
    return BoundarySegmentationMetrics(
        source_set_id=source_set_id,
        channel=channel,
        relevant_predicted_boundary_pixels=int(relevant.sum()),
        relevant_boundary_within_two_pixels=relevant_score,
        boundary_precision_within_two_pixels=precision,
        boundary_recall_within_two_pixels=recall,
        boundary_f1_within_two_pixels=_safe_ratio(
            2 * precision * recall, precision + recall
        ),
    )


def assay_quality_metrics(
    rows: tuple[AssayMeasurementRecord, ...],
    *,
    treatment: str,
) -> AssayQualityMetrics:
    """Compute Z-prime, replicate-SD V-factor, and dose means for one drug block."""

    selected = tuple(row for row in rows if row.assay_block == treatment)
    negatives = np.asarray(
        [
            row.value
            for row in selected
            if row.assay_role is ValidationAssayRole.NEGATIVE_CONTROL
        ]
    )
    positives = np.asarray(
        [
            row.value
            for row in selected
            if row.assay_role is ValidationAssayRole.POSITIVE_CONTROL
        ]
    )
    if len(negatives) < 2 or len(positives) < 2:
        raise ValidationScoringError(
            f"{treatment} requires at least two positive and negative controls."
        )
    dynamic_range = abs(float(positives.mean() - negatives.mean()))
    z_prime = (
        1.0
        - 3.0
        * (float(positives.std(ddof=1)) + float(negatives.std(ddof=1)))
        / dynamic_range
    )
    doses: dict[float, list[float]] = {}
    for row in selected:
        if row.assay_role is ValidationAssayRole.DOSE:
            doses.setdefault(row.concentration, []).append(row.value)
    dose_means = tuple(
        (dose, float(np.mean(values))) for dose, values in sorted(doses.items())
    )
    response_groups: dict[tuple[ValidationAssayRole, float], list[float]] = {}
    for row in selected:
        if row.assay_role is not ValidationAssayRole.EMPTY:
            response_groups.setdefault((row.assay_role, row.concentration), []).append(
                row.value
            )
    replicate_sds = tuple(
        float(np.std(values, ddof=1))
        for values in response_groups.values()
        if len(values) > 1
    )
    if not replicate_sds:
        raise ValidationScoringError(f"{treatment} has no replicated dose groups.")
    return AssayQualityMetrics(
        treatment=treatment,
        negative_control_count=len(negatives),
        positive_control_count=len(positives),
        z_prime=z_prime,
        replicate_sd_v_factor=1.0 - 6.0 * float(np.mean(replicate_sds)) / dynamic_range,
        dose_response_means=dose_means,
    )


@dataclass(frozen=True, slots=True)
class _ReferenceManifestRecord:
    source_set_id: str
    channel: str
    relative_path: Path


def _read_prediction_manifest(path: Path) -> dict[tuple[str, str], PredictionRecord]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        records = tuple(
            PredictionRecord(
                source_set_id=row["source_set_id"],
                channel=row["channel"],
                relative_path=Path(row["relative_path"]),
            )
            for row in csv.DictReader(handle)
        )
    return _unique_records(records)


def _read_reference_manifest(
    scoring_root: Path,
) -> dict[tuple[str, str], _ReferenceManifestRecord]:
    with (scoring_root / "reference_manifest.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        records = tuple(
            _ReferenceManifestRecord(
                source_set_id=row["source_set_id"],
                channel=row["channel"],
                relative_path=Path(row["relative_path"]),
            )
            for row in csv.DictReader(handle)
        )
    return _unique_records(records)


def _unique_records(records):
    result = {}
    for record in records:
        key = (record.source_set_id, record.channel)
        if key in result:
            raise ValidationScoringError(f"Duplicate scoring identity {key!r}.")
        result[key] = record
    return result


def _require_same_keys(predictions, references) -> None:
    if predictions.keys() != references.keys():
        missing = tuple(sorted(references.keys() - predictions.keys()))
        unexpected = tuple(sorted(predictions.keys() - references.keys()))
        raise ValidationScoringError(
            f"Prediction manifest mismatch; missing={missing!r}, unexpected={unexpected!r}."
        )


def _read_assay_results(
    path: Path,
    *,
    source_manifest_path: Path,
) -> tuple[AssayMeasurementRecord, ...]:
    required = {"well", "value"}
    with Path(path).open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or not required.issubset(reader.fieldnames):
            raise ValidationScoringError(
                f"Assay result CSV requires columns {tuple(sorted(required))!r}."
            )
        result_rows = tuple(dict(row) for row in reader)
    wells = tuple(row["well"] for row in result_rows)
    if len(wells) != len(set(wells)):
        raise ValidationScoringError("Assay result CSV contains duplicate wells.")
    metadata_by_well: dict[str, dict[str, str]] = {}
    with source_manifest_path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            well = row["well"]
            metadata = {
                key: row[key]
                for key in (
                    "treatment",
                    "assay_block",
                    "concentration",
                    "assay_role",
                )
            }
            previous = metadata_by_well.setdefault(well, metadata)
            if previous != metadata:
                raise ValidationScoringError(
                    f"Source manifest has inconsistent metadata for well {well!r}."
                )
    missing = tuple(sorted(set(wells) - metadata_by_well.keys()))
    if missing:
        raise ValidationScoringError(
            f"Assay result contains wells absent from the prepared source manifest: {missing!r}."
        )
    return tuple(
        AssayMeasurementRecord(
            well=row["well"],
            assay_block=metadata_by_well[row["well"]]["assay_block"],
            treatment=metadata_by_well[row["well"]]["treatment"],
            concentration=float(metadata_by_well[row["well"]]["concentration"]),
            assay_role=ValidationAssayRole(metadata_by_well[row["well"]]["assay_role"]),
            value=float(row["value"]),
        )
        for row in result_rows
    )


def _load_label_array(path: Path) -> np.ndarray:
    if not path.is_file():
        raise FileNotFoundError(f"Declared prediction is missing: {path}")
    if path.suffix.lower() == ".npy":
        return np.asarray(np.load(path, allow_pickle=False))
    return np.asarray(iio.imread(path))


def _resolved_result_artifact(manifest_path: Path, relative_path: Path) -> Path:
    root = manifest_path.parent.resolve()
    if relative_path.is_absolute():
        raise ValidationScoringError(
            f"Prediction paths must be relative to the result manifest: {relative_path}."
        )
    resolved = (root / relative_path).resolve()
    if resolved != root and root not in resolved.parents:
        raise ValidationScoringError(
            f"Prediction path escapes the result directory: {relative_path}."
        )
    return resolved


def _canonical_labels(values: np.ndarray) -> np.ndarray:
    labels = np.asarray(values)
    if labels.ndim != 2:
        raise ValidationScoringError(
            f"Expected a 2-D label image, got {labels.shape!r}."
        )
    if not np.issubdtype(labels.dtype, np.integer) and labels.dtype != np.bool_:
        raise ValidationScoringError(
            f"Label image dtype must be integral, got {labels.dtype}."
        )
    if np.any(labels < 0):
        raise ValidationScoringError("Label images cannot contain negative object IDs.")
    return relabel_sequential(labels.astype(np.int64, copy=False))[0]


def _contingency(
    predicted: np.ndarray,
    reference: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    predicted_count = int(predicted.max())
    reference_count = int(reference.max())
    encoded = predicted.ravel() * (reference_count + 1) + reference.ravel()
    matrix = np.bincount(
        encoded,
        minlength=(predicted_count + 1) * (reference_count + 1),
    ).reshape(predicted_count + 1, reference_count + 1)
    intersections = matrix[1:, 1:].astype(np.int64, copy=False)
    pred_areas = matrix[1:, :].sum(axis=1)
    ref_areas = matrix[:, 1:].sum(axis=0)
    return intersections, pred_areas, ref_areas


def _safe_ratio(numerator: float, denominator: float) -> float:
    return float(numerator / denominator) if denominator else 0.0


def _masked_fraction(condition: np.ndarray, mask: np.ndarray) -> float:
    return _safe_ratio(float(np.count_nonzero(condition & mask)), float(mask.sum()))


def _jsonable(value):
    if isinstance(value, ValidationMetricProfile):
        return value.value
    if isinstance(value, dict):
        return {key: _jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_jsonable(item) for item in value]
    return value
