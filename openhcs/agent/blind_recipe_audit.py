"""Read-only, metadata-only gate for promoting a blinded analysis recipe.

This audits claimed evidence; it neither opens images nor controls data access.
The caller must establish that referenced receipts and witnesses are authentic.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from math import isfinite


class ReviewDecision(str, Enum):
    ACCEPT = "accept"
    REJECT = "reject"
    AMBIGUOUS = "ambiguous"


class DataSplit(str, Enum):
    DEVELOPMENT = "development"
    HELD_OUT = "held_out"


@dataclass(frozen=True)
class Capture:
    """Identity of a retained view, not its pixels or an instruction to load it."""

    capture_id: str
    result_artifact_id: str | None
    source_id: str
    field_id: str
    xy: tuple[int, int]
    z: int
    time: int
    channel: str
    display_limits: tuple[float, float]

    @property
    def coordinate(self) -> tuple[str, tuple[int, int], int, int]:
        return (self.field_id, self.xy, self.z, self.time)


@dataclass(frozen=True)
class VisualReview:
    """A same-coordinate raw/overlay pair and explicit biological judgement."""

    raw: Capture
    overlay: Capture
    decision: ReviewDecision
    reviewer: str
    rationale: str
    criteria_id: str


@dataclass(frozen=True)
class TrialEvidence:
    """Minimal run and parameter provenance for one immutable candidate."""

    split: DataSplit
    source_id: str
    source_manifest_sha256: str
    pipeline_sha256: str
    parameters_sha256: str
    compile_receipt_id: str
    execution_receipt_id: str
    result_artifact_id: str
    review: VisualReview
    authorised_freeze_receipt_id: str | None = None


@dataclass(frozen=True)
class RecipePromotionEvidence:
    """Development acceptance, freeze, and independent validation evidence."""

    development: TrialEvidence
    frozen_pipeline_sha256: str
    frozen_parameters_sha256: str
    freeze_receipt_id: str
    validation: TrialEvidence


def _sha256(value: str) -> bool:
    return len(value) == 64 and all(char in "0123456789abcdef" for char in value)


def _audit_trial(trial: TrialEvidence, name: str) -> list[str]:
    issues: list[str] = []
    for key in (
        "source_id",
        "compile_receipt_id",
        "execution_receipt_id",
        "result_artifact_id",
    ):
        if not getattr(trial, key).strip():
            issues.append(f"{name}: missing {key}")
    for key in ("source_manifest_sha256", "pipeline_sha256", "parameters_sha256"):
        if not _sha256(getattr(trial, key)):
            issues.append(f"{name}: invalid {key}")

    review = trial.review
    for label, capture in (("raw", review.raw), ("overlay", review.overlay)):
        if not all(
            (
                capture.capture_id.strip(),
                capture.source_id.strip(),
                capture.field_id.strip(),
                capture.channel.strip(),
            )
        ):
            issues.append(f"{name}: incomplete {label} capture identity")
        low, high = capture.display_limits
        if not (isfinite(low) and isfinite(high) and low < high):
            issues.append(f"{name}: invalid {label} display limits")
    if (
        review.raw.source_id != trial.source_id
        or review.overlay.source_id != trial.source_id
    ):
        issues.append(f"{name}: capture source does not match run source")
    if review.raw.coordinate != review.overlay.coordinate:
        issues.append(f"{name}: raw and overlay coordinates differ")
    if review.raw.channel != review.overlay.channel:
        issues.append(f"{name}: raw and overlay biological channels differ")
    if review.raw.display_limits != review.overlay.display_limits:
        issues.append(f"{name}: raw and overlay display limits differ")
    if review.raw.capture_id == review.overlay.capture_id:
        issues.append(f"{name}: raw and overlay captures are not distinct")
    if review.raw.result_artifact_id is not None:
        issues.append(f"{name}: raw witness must be independent of result")
    if review.overlay.result_artifact_id != trial.result_artifact_id:
        issues.append(f"{name}: overlay does not identify the run result")
    if (
        not review.reviewer.strip()
        or not review.rationale.strip()
        or not review.criteria_id.strip()
    ):
        issues.append(f"{name}: missing reviewer, rationale, or acceptance criteria")
    if review.decision is not ReviewDecision.ACCEPT:
        issues.append(f"{name}: biological review is not accepted")
    return issues


def audit_recipe_promotion(evidence: RecipePromotionEvidence) -> tuple[str, ...]:
    """Return unmet gates; an empty tuple means only that the receipts are coherent.

    A successful audit does not itself validate biology, prove receipt authenticity,
    or authorise opening held-out images. The domain reviewer owns those decisions.
    """

    issues = _audit_trial(evidence.development, "development")
    issues.extend(_audit_trial(evidence.validation, "validation"))
    if evidence.development.split is not DataSplit.DEVELOPMENT:
        issues.append("development: expected development split")
    if evidence.validation.split is not DataSplit.HELD_OUT:
        issues.append("validation: expected held-out split")
    if evidence.development.authorised_freeze_receipt_id is not None:
        issues.append("development: must not claim held-out release")
    if evidence.validation.authorised_freeze_receipt_id != evidence.freeze_receipt_id:
        issues.append("validation: run is not linked to the freeze receipt")
    if evidence.development.source_id == evidence.validation.source_id:
        issues.append("validation: source is not independent of development")
    if not evidence.freeze_receipt_id.strip():
        issues.append("freeze: missing freeze receipt")
    for key in ("pipeline_sha256", "parameters_sha256"):
        frozen = getattr(evidence, f"frozen_{key}")
        if not _sha256(frozen):
            issues.append(f"freeze: invalid frozen_{key}")
        if frozen != getattr(evidence.development, key):
            issues.append(f"freeze: {key} differs from accepted development trial")
        if frozen != getattr(evidence.validation, key):
            issues.append(f"validation: {key} differs from frozen recipe")
    if (
        evidence.development.review.criteria_id
        != evidence.validation.review.criteria_id
    ):
        issues.append("validation: acceptance criteria changed after freeze")
    return tuple(issues)
