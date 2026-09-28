"""Synthetic metadata only: these tests never load biological images."""

from dataclasses import replace

from openhcs.agent.blind_recipe_audit import (
    Capture,
    DataSplit,
    RecipePromotionEvidence,
    ReviewDecision,
    TrialEvidence,
    VisualReview,
    audit_recipe_promotion,
)


def _trial(split: DataSplit, source: str, freeze: str | None = None) -> TrialEvidence:
    raw = Capture(
        "raw-capture", None, source, "field-a", (20, 30), 0, 0, "target", (1.0, 100.0)
    )
    overlay = replace(raw, capture_id="overlay-capture", result_artifact_id="labels")
    return TrialEvidence(
        split=split,
        source_id=source,
        source_manifest_sha256="c" * 64,
        pipeline_sha256="a" * 64,
        parameters_sha256="b" * 64,
        compile_receipt_id="compile-1",
        execution_receipt_id="run-1",
        result_artifact_id="labels",
        review=VisualReview(
            raw,
            overlay,
            ReviewDecision.ACCEPT,
            "reviewer",
            "objects match raw signal",
            "criteria-v1",
        ),
        authorised_freeze_receipt_id=freeze,
    )


def _evidence() -> RecipePromotionEvidence:
    return RecipePromotionEvidence(
        development=_trial(DataSplit.DEVELOPMENT, "dev"),
        frozen_pipeline_sha256="a" * 64,
        frozen_parameters_sha256="b" * 64,
        freeze_receipt_id="freeze-1",
        validation=_trial(DataSplit.HELD_OUT, "reserve", "freeze-1"),
    )


def test_complete_metadata_is_coherent_not_a_biological_proof() -> None:
    assert audit_recipe_promotion(_evidence()) == ()


def test_missing_execution_and_rejected_review_block_promotion() -> None:
    evidence = _evidence()
    development = replace(
        evidence.development,
        execution_receipt_id="",
        review=replace(evidence.development.review, decision=ReviewDecision.REJECT),
    )
    issues = audit_recipe_promotion(replace(evidence, development=development))
    assert "development: missing execution_receipt_id" in issues
    assert "development: biological review is not accepted" in issues


def test_mismatched_raw_overlay_and_result_lineage_block_promotion() -> None:
    evidence = _evidence()
    bad_overlay = replace(
        evidence.development.review.overlay,
        xy=(21, 30),
        display_limits=(2.0, 100.0),
        result_artifact_id="other-run",
    )
    development = replace(
        evidence.development,
        review=replace(evidence.development.review, overlay=bad_overlay),
    )
    issues = audit_recipe_promotion(replace(evidence, development=development))
    assert "development: raw and overlay coordinates differ" in issues
    assert "development: raw and overlay display limits differ" in issues
    assert "development: overlay does not identify the run result" in issues


def test_held_out_requires_freeze_link_same_recipe_and_independent_source() -> None:
    evidence = _evidence()
    validation = replace(
        evidence.validation,
        source_id="dev",
        parameters_sha256="d" * 64,
        authorised_freeze_receipt_id=None,
    )
    issues = audit_recipe_promotion(replace(evidence, validation=validation))
    assert "validation: source is not independent of development" in issues
    assert "validation: run is not linked to the freeze receipt" in issues
    assert "validation: parameters_sha256 differs from frozen recipe" in issues


def test_incomplete_witness_and_changed_criteria_block_promotion() -> None:
    evidence = _evidence()
    validation = replace(
        evidence.validation,
        review=replace(
            evidence.validation.review,
            criteria_id="criteria-v2",
            raw=replace(evidence.validation.review.raw, display_limits=(2.0, 2.0)),
        ),
    )
    issues = audit_recipe_promotion(replace(evidence, validation=validation))
    assert "validation: invalid raw display limits" in issues
    assert "validation: acceptance criteria changed after freeze" in issues
