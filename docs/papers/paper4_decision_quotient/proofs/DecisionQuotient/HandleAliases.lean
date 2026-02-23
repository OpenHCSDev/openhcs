/-
  Compact Lean-handle aliases used in paper prose/tables.
  Implemented as namespace-level exports to preserve exact theorem constants.
-/

import DecisionQuotient.Basic
import DecisionQuotient.ClaimClosure
import DecisionQuotient.IntegrityCompetence
import DecisionQuotient.HardnessDistribution
import DecisionQuotient.Hardness.Sigma2PHardness
import DecisionQuotient.PhysicalBudgetCrossover
import DecisionQuotient.Hardness.ConfigReduction
import DecisionQuotient.InteriorVerification
import DecisionQuotient.DecisionGeometry
import DecisionQuotient.UniverseObjective
import DecisionQuotient.Physics.Instantiation
import DecisionQuotient.Physics.AccessRegime
import DecisionQuotient.Physics.PhysicalHardness
import DecisionQuotient.Physics.DecisionTime
import DecisionQuotient.Physics.PhysicalIncompleteness
import DecisionQuotient.Physics.ClaimTransport

namespace DecisionQuotient

namespace CC
export DecisionQuotient.ClaimClosure (
  RegimeSimulation
  adq_ordering
  agent_transfer_licensed_iff_snapshot
  anchor_sigma2p_complete_conditional
  anchor_sigma2p_reduction_core
  boundaryCharacterized_iff_exists_sufficient_subset
  bounded_actions_detectable
  bridge_boundary_represented_family
  bridge_failure_witness_non_one_step
  bridge_transfer_iff_one_step_class
  certified_total_bits_split_core
  cost_asymmetry_eth_conditional
  declaredBudgetSlice
  declaredRegimeFamily_complete
  declared_physics_no_universal_exact_certifier_core
  dichotomy_conditional
  epsilon_admissible_iff_raw_lt_certified_total_core
  exact_admissible_iff_raw_lt_certified_total_core
  exact_certainty_inflation_under_hardness_core
  exact_raw_eq_certified_iff_certainty_inflation_core
  exact_raw_only_of_no_exact_admissible_core
  explicit_assumptions_required_of_not_excused_core
  explicit_state_upper_core
  hard_family_all_coords_core
  horizonTwoWitness_immediate_empty_sufficient
  horizon_gt_one_bridge_can_fail_on_sufficiency
  information_barrier_opt_oracle_core
  information_barrier_state_batch_core
  information_barrier_value_entry_core
  integrity_resource_bound_for_sufficiency
  integrity_universal_applicability_core
  meta_coordinate_irrelevant_of_invariance_on_declared_slice
  meta_coordinate_not_relevant_on_declared_slice
  minsuff_collapse_core
  minsuff_collapse_to_conp_conditional
  minsuff_conp_complete_conditional
  no_auto_minimize_of_p_neq_conp
  no_exact_claim_admissible_under_hardness_core
  no_exact_claim_under_declared_assumptions_unless_excused_core
  no_exact_identifier_implies_not_boundary_characterized
  no_uncertified_exact_claim_core
  one_step_bridge
  oracle_lattice_transfer_as_regime_simulation
  physical_crossover_above_cap_core
  physical_crossover_core
  physical_crossover_hardness_core
  physical_crossover_policy_core
  process_bridge_failure_witness
  query_obstruction_boolean_corollary
  query_obstruction_finite_state_core
  regime_core_claim_proved
  regime_simulation_transfers_hardness
  reusable_heuristic_of_detectable
  selectorSufficient_not_implies_setSufficient
  separable_detectable
  snapshot_vs_process_typed_boundary
  standard_assumption_ledger_unpack
  stochastic_objective_bridge_can_fail_on_sufficiency
  subproblem_hardness_lifts_to_full
  subproblem_transfer_as_regime_simulation
  sufficiency_conp_complete_conditional
  sufficiency_conp_reduction_core
  sufficiency_iff_dq_ratio
  sufficiency_iff_projectedOptCover_eq_opt
  thermo_conservation_additive_core
  thermo_energy_carbon_lift_core
  thermo_eventual_lift_core
  thermo_hardness_bundle_core
  thermo_mandatory_cost_core
  tractable_bounded_core
  tractable_separable_core
  tractable_subcases_conditional
  tractable_tree_core
  transition_coupled_bridge_can_fail_on_sufficiency
  tree_structure_detectable
  typed_claim_admissibility_core
  typed_static_class_completeness
  universal_solver_framing_core
)
end CC

namespace IC
export DecisionQuotient.IntegrityCompetence (
  CertaintyInflation
  CompletionFractionDefined
  EvidenceForReport
  ExactCertaintyInflation
  Percent
  RLFFWeights
  ReportSignal
  ReportBitModel
  SignalConsistent
  admissible_irrational_strictly_more_than_rational
  admissible_matrix_counts
  abstain_signal_exists_with_guess_self
  certaintyInflation_iff_not_admissible
  certificationOverheadBits
  certificationOverheadBits_of_evidence
  certificationOverheadBits_of_no_evidence
  certifiedTotalBits
  certifiedTotalBits_ge_raw
  certifiedTotalBits_gt_raw_of_evidence
  certifiedTotalBits_of_evidence
  certifiedTotalBits_of_no_evidence
  claim_admissible_of_evidence
  competence_implies_integrity
  completion_fraction_defined_of_declared_bound
  epsilon_competence_implies_integrity
  evidence_nonempty_iff_claim_admissible
  evidence_of_claim_admissible
  exact_claim_admissible_iff_exact_evidence_nonempty
  exact_claim_requires_evidence
  exactCertaintyInflation_iff_no_exact_competence
  exact_raw_only_of_no_exact_admissible
  integrity_forces_abstention
  integrity_not_competent_of_nonempty_scope
  integrity_resource_bound
  no_completion_fraction_without_declared_bound
  overModelVerdict_rational_iff
  percentZero
  rlffBaseReward
  rlffReward
  rlff_abstain_strictly_prefers_no_certificates
  rlff_maximizer_has_evidence
  rlff_maximizer_is_admissible
  self_reflected_confidence_not_certification
  signal_certified_positive_implies_admissible
  signal_consistent_of_claim_admissible
  signal_no_evidence_forces_zero_certified
  signal_exact_no_competence_forces_zero_certified
  steps_run_scalar_always_defined
  steps_run_scalar_falsifiable
  zero_epsilon_competence_iff_exact
)
end IC

namespace HD
export DecisionQuotient.HardnessDistribution (
  centralization_dominance_bundle
  centralization_step_saves_n_minus_one
  centralized_higher_leverage
  complete_model_dominates_after_threshold
  gap_conservation_card
  generalizedTotal_with_saturation_eventually_constant
  generalized_dominance_can_fail_without_right_boundedness
  generalized_dominance_can_fail_without_wrong_growth
  generalized_right_dominates_wrong_of_bounded_vs_identity_lower
  generalized_right_eventually_dominates_wrong
  hardnessEfficiency_eq_central_share
  isRightHardness
  isWrongHardness
  linear_lt_exponential_plus_constant_eventually
  native_dominates_manual
  no_positive_slope_linear_represents_saturating
  requiredWork
  requiredWork_eq_affine_in_sites
  right_dominates_wrong
  saturatingSiteCost_eventually_constant
  simplicityTax_grows
  hardnessLowerBound
  hardness_is_irreducible_required_work
  totalDOF_eventually_constant_iff_zero_distributed
  totalDOF_ge_intrinsic
  totalExternalWork_eq_n_mul_gapCard
  workGrowthDegree
  workGrowthDegree_zero_iff_eventually_constant
)
end HD

namespace DP
export DecisionQuotient.DecisionProblem (
  minimalSufficient_iff_relevant
  relevantSet_is_minimal
  sufficient_implies_selectorSufficient
)
export DecisionQuotient.ClaimClosure.DecisionProblem (
  epsOpt_zero_eq_opt
  sufficient_iff_zeroEpsilonSufficient
)
end DP

namespace S2P
export DecisionQuotient.Sigma2PHardness (
  exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset
  min_representationGap_zero_iff_relevant_card
  min_sufficient_set_iff_relevant_card
  representationGap
  representationGap_eq_waste_plus_missing
  representationGap_eq_zero_iff
  representationGap_missing_eq_gapCard
  representationGap_zero_iff_minimalSufficient
  sufficient_iff_relevant_subset
)
end S2P

namespace PBC
export DecisionQuotient.PhysicalBudgetCrossover (
  CrossoverAt
  explicit_infeasible_succinct_feasible_of_crossover
  has_crossover_of_bounded_succinct_unbounded_explicit
)
end PBC

namespace CR
export DecisionQuotient.ConfigReduction (
  config_sufficiency_iff_behavior_preserving
)
end CR

namespace IV
export DecisionQuotient.InteriorVerification (
  GoalClass
  GoalClass.classMonotoneOn
  GoalClass.isNonNegativelyTautologicalCoord
  GoalClass.isTautologicalCoord
  GoalClass.tautologicalSet
  InteriorDominanceVerifiable
  TautologicalSetIdentifiable
  agreeOnSet
  interiorParetoDominates
  interior_certificate_implies_non_rejection
  interior_dominance_implies_universal_non_rejection
  interior_dominance_not_full_sufficiency
  interior_verification_tractable_certificate
  not_sufficientOnSet_of_counterexample
  singleton_coordinate_interior_certificate
)
end IV

namespace DG
export DecisionQuotient (
  Outside
  anchoredSlice
  anchoredSliceEquivOutside
  card_outside_eq_sub
  card_anchoredSlice
  card_anchoredSlice_eq_pow_sub
  card_anchoredSlice_eq_uniform
  anchoredSlice_mul_fixed_eq_full
  constantBoolDP
  firstCoordDP
  constantBoolDP_opt
  firstCoordDP_opt
  constantBoolDP_empty_sufficient
  firstCoordDP_empty_not_sufficient
  boolHypercube_node_count
  node_count_does_not_determine_edge_geometry
)
export DecisionQuotient.DecisionProblem (
  edgeOnComplement
  edgeOnComplement_iff_not_sufficient
)
end DG

namespace DT
export DecisionQuotient.Physics.DecisionTime (
  TimedState
  DecisionProcess
  tick
  DecisionEvent
  TimeUnitStep
  time_is_discrete
  time_coordinate_falsifiable
  tick_increments_time
  tick_decision_witness
  tick_is_decision_event
  decision_event_implies_time_unit
  decision_taking_place_is_unit_of_time
  decision_event_iff_eq_tick
  run
  run_time_exact
  run_elapsed_time_eq_ticks
  decisionTrace
  decisionTrace_length_eq_ticks
  decision_count_equals_elapsed_time
  SubstrateKind
  SubstrateModel
  substrate_step_realizes_decision_event
  substrate_step_is_time_unit
  time_unit_law_substrate_invariant
)
end DT

namespace PI
export DecisionQuotient.Physics.PhysicalIncompleteness (
  UniverseModel
  PhysicallyInstantiated
  no_surjective_instantiation_of_card_gap
  physical_incompleteness_of_card_gap
  physical_incompleteness_of_bounds
)
end PI

namespace CT
export DecisionQuotient.Physics.ClaimTransport (
  PhysicalEncoding
  physical_claim_lifts_from_core
  physical_claim_lifts_from_core_conditional
  physical_counterexample_yields_core_counterexample
  physical_counterexample_invalidates_core_rule
  no_physical_counterexample_of_core_theorem
  LawGapInstance
  lawGapEncoding
  lawGapPhysicalClaim
  law_gap_physical_claim_holds
  no_law_gap_counterexample
  physical_bridge_bundle
)
end CT

namespace IN
export DecisionQuotient.Physics.Instantiation (
  Geometry
  Dynamics
  Circuit
  geometry_plus_dynamics_is_circuit
  DecisionInterpretation
  DecisionCircuit
  Molecule
  Reaction
  ReactionOutcome
  MoleculeGeometry
  MoleculeDynamics
  MoleculeCircuit
  MoleculeAsCircuit
  MoleculeAsDecisionCircuit
  molecule_decision_preserves_geometry
  molecule_decision_preserves_dynamics
  asDecisionCircuit
  asDecisionCircuit_preserves_circuit
  Configuration
  EnergyLandscape
  k_Boltzmann
  LandauerBound
  law_objective_schema
  law_opt_eq_feasible_of_gap
  law_opt_singleton_of_deterministic
)
end IN

namespace ARG
export PhysicalComplexity.AccessRegime (
  PhysicalDevice
  AccessRegime
  RegimeEval
  RegimeSample
  RegimeProof
  RegimeWithCertificate
  RegimeEvalOn
  RegimeSampleOn
  RegimeProofOn
  RegimeWithCertificateOn
  HardUnderEval
  AuditableWithCertificate
  certificate_upgrades_regime
  certificate_upgrades_regime_on
  physical_succinct_certification_hard
  certificate_amortizes_hardness
  regime_upgrade_with_certificate
  regime_upgrade_with_certificate_on
  AccessChannelLaw
  FiveWayMeet
)
end ARG

namespace PH
export PhysicalComplexity (
  k_Boltzmann
  PhysicalComputer
  bit_energy_cost
  Landauer_bound
  InstanceSize
  ComputationalRequirement
  coNP_requirement
  coNP_physically_impossible
  coNP_not_in_P_physically
  sufficiency_physically_impossible
)
end PH

namespace UO
export DecisionQuotient (
  UniverseDynamics
  feasibleActions
  lawDecisionProblem
  lawUtility
  logicallyDeterministic
  universe_sets_objective_schema
  lawUtility_eq_of_allowed_iff
  opt_eq_feasible_of_gap
  infeasible_not_optimal_of_gap
  opt_singleton_of_logicallyDeterministic
  opt_eq_of_allowed_iff
)
end UO

namespace DQ
export DecisionQuotient.CC (
  anchor_sigma2p_complete_conditional
  cost_asymmetry_eth_conditional
  dichotomy_conditional
  minsuff_collapse_to_conp_conditional
  minsuff_conp_complete_conditional
  sufficiency_conp_complete_conditional
  tractable_subcases_conditional
)
end DQ

end DecisionQuotient
