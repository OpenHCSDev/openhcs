from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import numpy as np
import pandas as pd
import pytest
from scipy import ndimage
from skimage import filters, measure, morphology, segmentation

from benchmark.agent_validation.contracts import (
    ArchitectureViolation,
    AttemptPhase,
    AttemptRecord,
    DslEvidenceArtifact,
    PercentileWindow,
    RootedContinuityObservation,
    RuntimeObservation,
    SemanticChange,
    ValidationView,
    ViewKind,
)
from benchmark.agent_validation.corpus import AgentValidationCorpus, FrozenPipeline
from benchmark.agent_validation.declarations import ValidationTaskDeclaration
from benchmark.agent_validation.journal import AttemptJournal
from benchmark.agent_validation.perturbations import DiagnosticPerturbationDeclaration
from benchmark.agent_validation.scoring import (
    AttemptJournalScorer,
    MaskDiagnosticMetrics,
    RootedContinuityMetrics,
)


def test_corpus_exposes_eight_declaration_owned_tasks() -> None:
    declarations = AgentValidationCorpus.task_declarations()
    assert len(declarations) == 8
    assert len({declaration.task_id for declaration in declarations}) == 8
    assert tuple(declaration.task_id for declaration in declarations) == tuple(
        sorted(declaration.task_id for declaration in declarations)
    )


def test_blind_bundle_contains_inputs_and_provenance_but_no_answers(
    tmp_path: Path,
) -> None:
    root = tmp_path / "blind"
    specs = AgentValidationCorpus.build_authoring_bundle(root)
    assert len(specs) == 8
    all_text = "\n".join(path.read_text() for path in root.rglob("*.json"))
    assert '"answer_material_included": false' in all_text
    assert '"expected"' not in all_text
    assert "f6edaa15545e84951f5428d07e16db04155f2266" in all_text
    projection_root = root / "human_eval_bia.maximum_intensity_projection" / "inputs"
    assert len(tuple(projection_root.glob("*.tif"))) == 6


def test_diagnostic_bundle_hides_failure_labels_and_preserves_opaque_probes(
    tmp_path: Path,
) -> None:
    root = tmp_path / "diagnostics"
    probe_ids = AgentValidationCorpus.build_diagnostic_bundle(root)
    assert probe_ids == (
        "probe-001",
        "probe-002",
        "probe-003",
        "probe-004",
        "probe-005",
    )
    public_text = "\n".join(path.read_text() for path in root.rglob("*.json"))
    assert '"failure_labels_included": false' in public_text
    assert "disconnected_trace" not in public_text
    assert '"expected_failure_hidden": true' in public_text
    assert all((root / probe_id / "candidate.npy").is_file() for probe_id in probe_ids)
    complete_pipeline = root / "probe-005" / "pipeline.py"
    assert complete_pipeline.is_file()
    assert "radius': 0" in complete_pipeline.read_text()


@pytest.mark.parametrize("task", AgentValidationCorpus.task_declarations())
def test_transcribed_upstream_assertions_accept_reference_implementation(task) -> None:
    for case in task.scoring_cases():
        actual = _reference_result(task.task_id, case)
        assertions = task.assert_case(case, actual)
        assert assertions
        assert all(assertion.passed for assertion in assertions), assertions


def test_mask_diagnostics_identify_split_merge_and_disconnection() -> None:
    reference = np.asarray(
        [[1, 1, 0, 2, 2], [1, 1, 0, 2, 2], [0, 0, 0, 0, 0], [3, 3, 3, 0, 0]]
    )
    candidate = np.asarray(
        [[1, 1, 0, 3, 3], [2, 2, 0, 3, 3], [0, 0, 0, 0, 0], [3, 0, 3, 0, 0]]
    )
    metrics = MaskDiagnosticMetrics.measure(reference > 0, candidate, reference)
    assert metrics.reference_splits == 1
    assert metrics.reference_merges == 1
    assert metrics.disconnected_labels == 1
    assert metrics.missed_signal_fraction > 0


def test_rooted_continuity_separates_admission_from_path_and_ownership() -> None:
    labels = np.zeros((9, 12), dtype=np.uint16)
    labels[4, 1] = 1
    labels[4, 10] = 2
    trace = np.zeros_like(labels, dtype=bool)
    trace[4, 1:11] = True
    trace[1, 4:7] = True
    metrics = RootedContinuityMetrics.measure(labels, trace)
    assert metrics.object_count == 2
    assert metrics.accepted_body_pixels == 2
    assert metrics.rooted_trace_pixels == 10
    assert metrics.unrooted_trace_pixels == 3
    assert metrics.ownership_crossover_components == 1


def test_declared_perturbations_induce_their_reference_visible_failures() -> None:
    probes = DiagnosticPerturbationDeclaration.__registry__
    split_probe = probes["probe-003"]
    split_case = split_probe.task_type().scoring_cases()[0]
    split_metrics = MaskDiagnosticMetrics.measure(
        np.asarray(split_case.expected) > 0,
        split_probe.perturb(split_case),
        np.asarray(split_case.expected),
    )
    assert split_metrics.reference_splits == 1

    merge_probe = probes["probe-004"]
    merge_case = merge_probe.task_type().scoring_cases()[0]
    merge_metrics = MaskDiagnosticMetrics.measure(
        np.asarray(merge_case.expected) > 0,
        merge_probe.perturb(merge_case),
        np.asarray(merge_case.expected),
    )
    assert merge_metrics.reference_merges == 1

    gap_probe = probes["probe-002"]
    gap_case = gap_probe.task_type().scoring_cases()[0]
    gap_metrics = MaskDiagnosticMetrics.measure(
        np.asarray(gap_case.expected) > 0,
        gap_probe.perturb(gap_case),
        np.asarray(gap_case.expected),
    )
    assert gap_metrics.missed_signal_fraction > 0
    assert gap_metrics.candidate_object_count > 1


def test_attempt_journal_scores_visual_and_dsl_axes_separately(tmp_path: Path) -> None:
    task = ValidationTaskDeclaration.get("human_eval_bia.binary_skeleton")
    for path in (
        tmp_path / "raw-100.png",
        tmp_path / "raw-99.png",
        tmp_path / "raw-95.png",
        tmp_path / "normalized.png",
        tmp_path / "overlay.png",
        tmp_path / "a1.npy",
        tmp_path / "a2.npy",
    ):
        path.touch()
    dsl_paths = {}
    for requirement in task.required_dsl:
        path = tmp_path / f"dsl-{requirement.value}.json"
        path.touch()
        dsl_paths[requirement] = path
    views = tuple(
        ValidationView(
            kind=ViewKind.RAW,
            artifact_path=tmp_path / f"raw-{high}.png",
            coordinate=(0, 0),
            crop_shape=(64, 64),
            display_window=PercentileWindow(0, high, 0, high),
        )
        for high in (100, 99, 95)
    ) + (
        ValidationView(
            kind=ViewKind.NORMALIZED,
            artifact_path=tmp_path / "normalized.png",
            coordinate=(0, 0),
            crop_shape=(64, 64),
        ),
        ValidationView(
            kind=ViewKind.OVERLAY,
            artifact_path=tmp_path / "overlay.png",
            coordinate=(0, 0),
            crop_shape=(64, 64),
        ),
    )
    first = AttemptRecord(
        attempt_id="a1",
        task_id=task.task_id,
        phase=AttemptPhase.REVIEWED,
        pipeline_sha256="1" * 64,
        output_paths=(tmp_path / "a1.npy",),
        views=views,
        diagnostic_checks=frozenset(task.required_diagnostics[:-1]),
        dsl_evidence=tuple(
            DslEvidenceArtifact(requirement, dsl_paths[requirement], "observed")
            for requirement in task.required_dsl[:-1]
        ),
        architecture_violations=frozenset(),
        runtime=RuntimeObservation(1.0, 1024),
    )
    second = AttemptRecord(
        attempt_id="a2",
        task_id=task.task_id,
        phase=AttemptPhase.FROZEN,
        pipeline_sha256="2" * 64,
        output_paths=(tmp_path / "a2.npy",),
        views=views,
        diagnostic_checks=frozenset({task.required_diagnostics[-1]}),
        dsl_evidence=(
            DslEvidenceArtifact(
                task.required_dsl[-1],
                dsl_paths[task.required_dsl[-1]],
                "observed",
            ),
        ),
        architecture_violations=frozenset(),
        runtime=RuntimeObservation(0.8, 2048),
        change=SemanticChange(
            "FunctionStep", "func[0].threshold", "0.5", "0.4", "recover dim foreground"
        ),
    )
    score = AttemptJournalScorer.score(task, (first, second))
    assert score.diagnostic_fraction == 1.0
    assert score.dsl_fraction == 1.0
    assert score.lifecycle_passed
    assert AgentValidationCorpus.score_probe_diagnosis("probe-002", first) == 1.0

    pipeline = tmp_path / "frozen_pipeline.py"
    pipeline.write_text("pipeline_steps = []\n")
    result_root = tmp_path / "results"
    result_root.mkdir()
    np.save(result_root / "case-1.npy", task.scoring_cases()[0].expected)
    task_score = AgentValidationCorpus.score(
        task.task_id,
        FrozenPipeline.capture(task.task_id, pipeline),
        (first, second),
        result_root,
    )
    assert task_score.result_parity_passed
    assert task_score.dsl_fraction == 1.0
    assert task_score.architecture_violations == ()

    indirect = AttemptJournalScorer.score(
        task,
        (
            replace(
                first,
                architecture_violations=frozenset(
                    {ArchitectureViolation.DIRECT_VIEWER_AUTOMATION}
                ),
            ),
            second,
        ),
    )
    assert indirect.dsl_fraction == 0.75

    bypassed = AttemptJournalScorer.score(
        task,
        (
            replace(
                first,
                architecture_violations=frozenset(
                    {ArchitectureViolation.EXTERNAL_PREPROCESSING}
                ),
            ),
            second,
        ),
    )
    assert bypassed.dsl_fraction == 0.0

    unrooted_growth = AttemptJournalScorer.score(
        task,
        (
            replace(
                first,
                continuity=RootedContinuityObservation(1, 10, 20, 15, 5, 0),
            ),
            replace(
                second,
                continuity=RootedContinuityObservation(1, 10, 30, 15, 15, 0),
            ),
        ),
    )
    assert not unrooted_growth.lifecycle_passed

    journal = AttemptJournal(tmp_path / "attempts")
    receipt = journal.preserve(first)
    assert receipt.is_file()
    with pytest.raises(FileExistsError):
        journal.preserve(first)


def test_frozen_pipeline_rejects_post_freeze_edits(tmp_path: Path) -> None:
    pipeline = tmp_path / "pipeline.py"
    pipeline.write_text("pipeline_steps = []\n")
    frozen = FrozenPipeline.capture("task", pipeline)
    frozen.verify()
    pipeline.write_text("pipeline_steps = [1]\n")
    with pytest.raises(ValueError, match="Frozen pipeline changed"):
        frozen.verify()


def _reference_result(task_id: str, case) -> object:
    inputs = {item.name: np.asarray(item.array) for item in case.inputs}
    parameters = dict(case.parameters)
    if task_id.endswith("otsu_positive_pixel_count"):
        image = inputs["image"]
        if np.ptp(image) == 0:
            return np.asarray(0)
        return np.asarray(np.sum(image > filters.threshold_otsu(image)))
    if task_id.endswith("binary_closing"):
        radius = parameters["radius"]
        return morphology.binary_closing(
            inputs["binary_image"], footprint=np.ones((radius * 2 + 1,) * 2)
        )
    if task_id.endswith("binary_skeleton"):
        return morphology.skeletonize(inputs["binary_image"])
    if task_id.endswith("detect_edges"):
        return ndimage.sobel(inputs["image"])
    if task_id.endswith("expand_labels_without_overlap"):
        return segmentation.expand_labels(
            inputs["label_image"], distance=parameters["radius"]
        )
    if task_id.endswith("maximum_intensity_projection"):
        return inputs["image"].max(axis=0)
    if task_id.endswith("measure_properties_of_regions"):
        return pd.DataFrame(
            measure.regionprops_table(
                inputs["label_image"],
                inputs["intensity_image"],
                properties=("area", "perimeter", "mean_intensity"),
            )
        )
    image = inputs["image"]
    return np.asarray(measure.label(image > image.mean()).max())
