from openhcs.agent.image_analysis_qa import (
    CandidateRejectionReason,
    ImageAnalysisQaPolicy,
    ImageQaEvidenceRule,
    ImageQaMissStage,
    ImageQaPrecondition,
    ReferenceEvidenceRule,
    RejectedCandidateObservation,
    ResidualStructureDisposition,
    ResidualStructureObservation,
    RootedContinuityObservation,
    SemanticGate,
    SignalTransformConstraint,
    ThinStructureContinuationConstraint,
)


def test_repair_guidance_is_derived_from_every_typed_gate_and_measure() -> None:
    guidance = ImageAnalysisQaPolicy.repair_guidance()
    for gate in SemanticGate:
        assert gate.value in guidance
        assert gate.description in guidance
        for measure in gate.measures:
            assert measure.value in guidance
    for reason in CandidateRejectionReason:
        assert reason.value in guidance
    for disposition in ResidualStructureDisposition:
        assert disposition.value in guidance
    for precondition in ImageQaPrecondition:
        assert precondition.value in guidance
    for rule in ImageQaEvidenceRule:
        assert rule.value in guidance
    for rule in ReferenceEvidenceRule:
        assert rule.value in guidance
    for stage in ImageQaMissStage:
        assert stage.name.lower() in guidance
        assert stage.value in guidance
    for constraint in ThinStructureContinuationConstraint:
        assert constraint.value in guidance
    for constraint in SignalTransformConstraint:
        assert constraint.value in guidance
    assert "nuclei without a nearby accepted soma" in guidance
    assert "source admission and target-body response as separate attempts" in guidance
    assert "splitting an already admitted source" in guidance
    assert "stricter threshold can split a merged object" in guidance
    assert "fixed-coordinate four-panel view" in guidance
    assert "candidate-only residual" in guidance
    assert "real routed payload values" in guidance
    assert "excluding sparse display padding" in guidance
    assert "not proof that the same objects were detected" in guidance
    assert "never to establish spatial identity" in guidance
    assert "for example DAPI" in guidance
    assert "accepted-label overlay" in guidance
    assert "rejected parameter changes" in guidance
    assert "higher-sensitivity diagnostic attempt" in guidance
    assert "subtract the accepted candidate mask" in guidance
    assert "diagnostic evidence rather than an automatic replacement" in guidance
    assert "owner cardinality per connected component" in guidance
    assert "shared crossing-core trace pixels" in guidance
    assert "dropped graph-path pixels rejected as unrooted" in guidance
    assert "physically soma-rooted dropped path pixels" in guidance
    assert "physically soma-detached dropped path pixels" in guidance
    assert "dropped trace pixels absent from final path graph" in guidance
    assert "owned trace pixels dropped by final topology" in guidance
    assert "final-topology added shared-core pixels" in guidance
    assert "lowering the detection threshold cannot repair it" in guidance
    assert "declare the permissive value only on the dataset or preset" in guidance
    assert "distance, ownership, and response alone are insufficient" in guidance
    assert "monotone, ridge, or contrast preprocessing" in guidance
    assert "Aggregate length or object-count agreement alone" in guidance
    assert "derive color-channel semantics from the physical container" in guidance
    assert "never infer a biological plane axis from array rank" in guidance
    assert "every held-out layout class to be represented in development" in guidance
    assert "without opening hidden labels or scoring references" in guidance
    assert "NamedSourceBinding(load_as_monochrome=True)" in guidance
    assert "do not apply unconditional color_to_gray downstream" in guidance
    assert "inventory every selected source" in guidance
    assert "registered image-file header semantics" in guidance
    assert "rather than sampling files or inferring layout from array rank" in guidance
    assert "label-ID sets to be identical" in guidance
    assert (
        "equal object counts alone do not prove seed identity conservation" in guidance
    )
    assert "primary-seed pixel lies inside the secondary mask" in guidance
    assert "applied numeric limits" in guidance
    assert "route-local semantic coordinate" in guidance
    assert "black, empty, stale, or mismatched capture" in guidance
    assert "verify every claimed durable label or measurement path exists" in guidance
    assert "same-identity containment" in guidance
    assert "shared crossing-core mask" in guidance
    assert "net pixel-count change is not evidence of pruning" in guidance
    assert (
        "require multiple independently supported nuclear intensity centres" in guidance
    )
    assert "outline shape alone does not prove multiple nuclei" in guidance
    assert "round_object_prefilter" in guidance
    assert "round_object_adjacent_satellite_candidates" in guidance
    assert "source_component_output_count" in guidance
    assert "separate threshold-stage component from a watershed split" in guidance
    assert "Never globally reject weak-core objects" in guidance
    assert "preserving isolated faint objects and multi-centre controls" in guidance


def test_trace_growth_requires_more_root_connected_continuity() -> None:
    baseline = RootedContinuityObservation(1, 20, 100, 80, 20, 0)
    unsupported_growth = RootedContinuityObservation(1, 20, 120, 80, 40, 0)
    rooted_growth = RootedContinuityObservation(1, 20, 120, 95, 25, 0)
    assert not unsupported_growth.accepts_growth_from(baseline)
    assert rooted_growth.accepts_growth_from(baseline)


def test_rejected_candidates_are_ranked_by_local_signal_support() -> None:
    candidates = (
        RejectedCandidateObservation(
            source_id=2,
            coordinate=(20, 30),
            nearby_signal_support=0.25,
            reason=CandidateRejectionReason.RESPONSE,
        ),
        RejectedCandidateObservation(
            source_id=1,
            coordinate=(10, 15),
            nearby_signal_support=0.8,
            reason=CandidateRejectionReason.CONNECTIVITY,
        ),
    )
    ranked = RejectedCandidateObservation.rank_by_signal_support(candidates)
    assert tuple(candidate.source_id for candidate in ranked) == (1, 2)


def test_residual_structures_are_ranked_before_threshold_changes() -> None:
    structures = (
        ResidualStructureObservation(
            structure_id=4,
            coordinate=(5, 6),
            local_signal_support=0.4,
            disposition=ResidualStructureDisposition.UNROOTED,
            topology_plausible=True,
        ),
        ResidualStructureObservation(
            structure_id=7,
            coordinate=(8, 9),
            local_signal_support=0.9,
            disposition=ResidualStructureDisposition.UNOWNED,
            topology_plausible=True,
        ),
    )
    ranked = ResidualStructureObservation.rank_by_signal_support(structures)
    assert tuple(structure.structure_id for structure in ranked) == (7, 4)
