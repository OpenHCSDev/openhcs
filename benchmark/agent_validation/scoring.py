"""Diagnostic, lifecycle, and image-comparison scoring."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from scipy import ndimage

from benchmark.agent_validation.contracts import (
    ArchitectureViolation,
    AttemptPhase,
    AttemptRecord,
    DiagnosticCheck,
    ViewKind,
)
from benchmark.agent_validation.declarations import ValidationTaskDeclaration


@dataclass(frozen=True, slots=True)
class AttemptJournalScore:
    """Independent scores for QA practice and OpenHCS mental-model fluency."""

    diagnostic_fraction: float
    dsl_fraction: float
    architecture_violations: tuple[ArchitectureViolation, ...]
    lifecycle_passed: bool


@dataclass(frozen=True, slots=True)
class MaskDiagnosticMetrics:
    """Reference-aware mask diagnostics used by perturbation challenges."""

    missed_signal_fraction: float
    unsupported_mask_fraction: float
    candidate_object_count: int
    candidate_area_quantiles: tuple[float, float, float]
    reference_splits: int
    reference_merges: int
    disconnected_labels: int
    quadrant_foreground_fractions: tuple[float, float, float, float]

    @classmethod
    def measure(
        cls,
        signal_support: np.ndarray,
        candidate: np.ndarray,
        reference: np.ndarray,
    ) -> "MaskDiagnosticMetrics":
        """Measure common visual failure classes without display heuristics."""

        support = np.asarray(signal_support, dtype=bool)
        candidate_labels = _as_labels(candidate)
        reference_labels = _as_labels(reference)
        candidate_mask = candidate_labels > 0
        missed = _safe_fraction(support & ~candidate_mask, support)
        unsupported = _safe_fraction(candidate_mask & ~support, candidate_mask)
        candidate_ids, candidate_areas = np.unique(
            candidate_labels[candidate_mask], return_counts=True
        )
        areas = (
            tuple(
                float(value)
                for value in np.quantile(candidate_areas, (0.25, 0.5, 0.75))
            )
            if candidate_areas.size
            else (0.0, 0.0, 0.0)
        )
        splits, merges = _split_merge_counts(reference_labels, candidate_labels)
        disconnected = sum(
            ndimage.label(candidate_labels == label_id)[1] > 1
            for label_id in candidate_ids
        )
        return cls(
            missed_signal_fraction=missed,
            unsupported_mask_fraction=unsupported,
            candidate_object_count=int(candidate_ids.size),
            candidate_area_quantiles=areas,
            reference_splits=splits,
            reference_merges=merges,
            disconnected_labels=int(disconnected),
            quadrant_foreground_fractions=_quadrant_fractions(candidate_mask),
        )


class AttemptJournalScorer:
    """Score the observable diagnose-edit-rerun-verify protocol."""

    @classmethod
    def score(
        cls,
        task: type[ValidationTaskDeclaration],
        attempts: tuple[AttemptRecord, ...],
    ) -> AttemptJournalScore:
        if not attempts:
            return AttemptJournalScore(0.0, 0.0, (), False)
        if any(attempt.task_id != task.task_id for attempt in attempts):
            raise ValueError("Attempt journal contains a different task id.")
        unique_ids = len({attempt.attempt_id for attempt in attempts}) == len(attempts)
        one_change_per_revision = all(
            attempt.change is not None for attempt in attempts[1:]
        )
        hashes_follow_changes = all(
            current.pipeline_sha256 != previous.pipeline_sha256
            for previous, current in zip(attempts, attempts[1:])
        )
        final = attempts[-1]
        visual_passed = cls._visual_evidence_passed(task, final)
        runtime_passed = (
            final.runtime is not None
            and final.runtime.elapsed_seconds >= 0
            and final.runtime.peak_rss_bytes >= 0
        )
        outputs_exist = bool(final.output_paths) and all(
            path.is_file() for path in final.output_paths
        )
        lifecycle_passed = all(
            (
                unique_ids,
                one_change_per_revision,
                hashes_follow_changes,
                final.phase is AttemptPhase.FROZEN,
                visual_passed,
                runtime_passed,
                outputs_exist,
            )
        )
        observed_diagnostics = frozenset().union(
            *(attempt.diagnostic_checks for attempt in attempts)
        )
        observed_dsl = frozenset(
            evidence.requirement
            for attempt in attempts
            for evidence in attempt.dsl_evidence
            if evidence.artifact_path.is_file() and evidence.explanation.strip()
        )
        violations = tuple(
            sorted(
                frozenset().union(
                    *(attempt.architecture_violations for attempt in attempts)
                ),
                key=lambda violation: violation.value,
            )
        )
        dsl_fraction = _coverage_fraction(frozenset(task.required_dsl), observed_dsl)
        if any(violation.disqualifying for violation in violations):
            dsl_fraction = 0.0
        else:
            dsl_fraction = max(
                0.0,
                dsl_fraction - sum(violation.penalty for violation in violations),
            )
        return AttemptJournalScore(
            diagnostic_fraction=_coverage_fraction(
                frozenset(task.required_diagnostics), observed_diagnostics
            ),
            dsl_fraction=dsl_fraction,
            architecture_violations=violations,
            lifecycle_passed=lifecycle_passed,
        )

    @staticmethod
    def _visual_evidence_passed(
        task: type[ValidationTaskDeclaration], attempt: AttemptRecord
    ) -> bool:
        if not attempt.views:
            return False
        if any(not view.artifact_path.is_file() for view in attempt.views):
            return False
        raw_views = tuple(view for view in attempt.views if view.kind is ViewKind.RAW)
        observed_view_kinds = {view.kind for view in attempt.views}
        if not raw_views or not set(task.required_views()).issubset(
            observed_view_kinds
        ):
            return False
        coordinates = {(view.coordinate, view.crop_shape) for view in attempt.views}
        percentile_windows = {
            (view.display_window.percentile_low, view.display_window.percentile_high)
            for view in raw_views
            if view.display_window is not None
        }
        return len(coordinates) == 1 and len(percentile_windows) >= 3


def _coverage_fraction(required: frozenset, observed: frozenset) -> float:
    if not required:
        return 1.0
    return len(required & observed) / len(required)


def _as_labels(image: np.ndarray) -> np.ndarray:
    array = np.asarray(image)
    if array.dtype == bool or np.array_equal(array, array.astype(bool)):
        return ndimage.label(array > 0)[0]
    return array.astype(np.int64, copy=False)


def _safe_fraction(numerator_mask: np.ndarray, denominator_mask: np.ndarray) -> float:
    denominator = int(np.count_nonzero(denominator_mask))
    if denominator == 0:
        return 0.0
    return float(np.count_nonzero(numerator_mask) / denominator)


def _split_merge_counts(
    reference_labels: np.ndarray,
    candidate_labels: np.ndarray,
) -> tuple[int, int]:
    pairs = np.stack((reference_labels.ravel(), candidate_labels.ravel()), axis=1)
    pairs = pairs[(pairs[:, 0] > 0) & (pairs[:, 1] > 0)]
    if pairs.size == 0:
        return 0, 0
    reference_to_candidate: dict[int, set[int]] = {}
    candidate_to_reference: dict[int, set[int]] = {}
    for reference_id, candidate_id in np.unique(pairs, axis=0):
        reference_to_candidate.setdefault(int(reference_id), set()).add(
            int(candidate_id)
        )
        candidate_to_reference.setdefault(int(candidate_id), set()).add(
            int(reference_id)
        )
    splits = sum(
        len(candidate_ids) > 1 for candidate_ids in reference_to_candidate.values()
    )
    merges = sum(
        len(reference_ids) > 1 for reference_ids in candidate_to_reference.values()
    )
    return int(splits), int(merges)


def _quadrant_fractions(mask: np.ndarray) -> tuple[float, float, float, float]:
    height, width = mask.shape[-2:]
    middle_y, middle_x = height // 2, width // 2
    quadrants = (
        mask[..., :middle_y, :middle_x],
        mask[..., :middle_y, middle_x:],
        mask[..., middle_y:, :middle_x],
        mask[..., middle_y:, middle_x:],
    )
    return tuple(
        float(np.mean(quadrant)) if quadrant.size else 0.0 for quadrant in quadrants
    )
