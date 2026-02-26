/-
  Compact Lean-handle aliases used in paper prose/tables.
  Implemented as namespace-level exports to preserve exact theorem constants.

  ## Triviality Level
  TRIVIAL: This is purely a re-export file. No proofs whatsoever.

  ## Dependencies
  - Chain: Depends on all main modules but exports them under simpler names
  - The nontrivial work is in the imported modules (ClaimClosure, Sigma2PHardness, etc.)
-/

import DecisionQuotient.Basic
import DecisionQuotient.ClaimClosure
import DecisionQuotient.IntegrityCompetence
import DecisionQuotient.HardnessDistribution
import DecisionQuotient.ToolCollapse
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
import DecisionQuotient.Physics.Conversation
import DecisionQuotient.Physics.ConstraintForcing
import DecisionQuotient.Physics.ObserverRelativeState
import DecisionQuotient.Physics.PhysicalIncompleteness
import DecisionQuotient.Physics.ClaimTransport
import DecisionQuotient.Physics.Uncertainty
import DecisionQuotient.Physics.HeisenbergStrong
import DecisionQuotient.GraphNontriviality
import DecisionQuotient.WitnessCheckingDuality
import DecisionQuotient.Summary
import DecisionQuotient.Dichotomy
import DecisionQuotient.Tractability.StructuralRank
import DecisionQuotient.StochasticSequential.ClaimClosure
import DecisionQuotient.StochasticSequential.Basic
import DecisionQuotient.StochasticSequential.Quotient
import DecisionQuotient.StochasticSequential.Hardness
import DecisionQuotient.StochasticSequential.Hierarchy
import DecisionQuotient.StochasticSequential.PolynomialReduction
import DecisionQuotient.StochasticSequential.ThermodynamicLift
import DecisionQuotient.BayesianBridge
import DecisionQuotient.BayesFromDQ
import DecisionQuotient.BayesFoundations
import DecisionQuotient.BayesOptimalityProof

namespace DecisionQuotient

namespace CC
export DecisionQuotient.ClaimClosure (
  RegimeSimulation
  adq_ordering
  agent_transfer_licensed_iff_snapshot
  anchor_sigma2p_complete_conditional
  anchor_sigma2p_reduction_core
  anchor_query_relation_false_iff
  anchor_query_relation_true_iff
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
  poseAnchorQuery
  pose_returns_anchor_query_object
  posed_anchor_checked_true_implies_truth
  posed_anchor_exact_claim_admissible_iff_competent
  posed_anchor_exact_claim_requires_evidence
  posed_anchor_no_competence_no_exact_claim
  posed_anchor_query_truth_iff_exists_anchor
  posed_anchor_query_truth_iff_exists_forall
  posed_anchor_signal_positive_certified_implies_admissible
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
  SuccinctInfeasible
  SuccinctUnbounded
  explicit_infeasible_succinct_feasible_of_crossover
  exists_least_crossover_point
  has_crossover_of_bounded_succinct_unbounded_explicit
  explicit_eventual_infeasibility_of_monotone_and_witness
  crossover_eventually_of_eventual_split
  payoff_threshold_explicit_vs_succinct
  no_universal_survivor_without_succinct_bound
  policy_closure_at_divergence
  policy_closure_beyond_divergence
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

namespace CV
export DecisionQuotient.Physics.Conversation (
  RecurrentCircuit
  CoupledConversation
  JointState
  tick
  tick_uses_shared_node
  tick_shared_is_merged_emissions
  BoundedChannel
  channelObserver
  channel_projection_eq_iff_quantized_eq
  clampBit
  clampChannel
  clamp_output_is_discrete
  clamp_projection_eq_iff_same_clamped_bit
  clampDecisionEvent
  clampDecisionBitOps
  clampDecisionBitOps_pos_of_event
  clampDecisionEvent_iff_bitOps_pos
  clamp_event_implies_positive_energy
  BinaryAnswer
  ConversationReport
  explanationGap
  explanationGap_add_explanationBits
  toClaimReport
  abstain_iff_no_answer
  yes_no_iff_exact_claim
  toClaimReport_ne_epsilon
  toReportSignal
  toReportSignal_declares_bound
  toReportSignal_completion_defined_of_budget
  toReportSignal_signal_consistent_zero_certified
  abstain_report_can_carry_explanation
)
end CV

namespace PI
export DecisionQuotient.Physics.PhysicalIncompleteness (
  UniverseModel
  PhysicallyInstantiated
  no_surjective_instantiation_of_card_gap
  physical_incompleteness_of_card_gap
  physical_incompleteness_of_bounds
  under_resolution_implies_collision
  under_resolution_implies_decision_collision
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
  PhysicalCollapseAtRequirement
  no_physical_collapse_at_requirement
  canonical_physical_collapse_impossible
  p_eq_np_physically_impossible_of_collapse_map
  p_eq_np_physically_impossible_canonical
  CoherentDQRejectionAtRequirement
  coherent_dq_rejection_impossible_at_requirement
  coherent_dq_rejection_impossible_canonical
)
end PH

namespace TC
export DecisionQuotient.ToolCollapse (
  WorkProfile
  WorkModel
  ToolModel
  EventualStrictImprovement
  EffectiveCollapse
  tool_never_worse
  strict_improvement_has_witness
  effective_collapse_of_eventual_strict
  expBaseline
  linearTool
  linear_tool_eventual_strict
  linear_tool_effective_collapse
)
end TC

namespace UQ
export DecisionQuotient.Physics.Uncertainty (
  binaryIdentityProblem
  binaryIdentityProblem_opt_true
  binaryIdentityProblem_opt_false
  exists_decision_problem_with_nontrivial_opt
  PhysicalNontrivialOptAssumption
  exists_decision_problem_with_nontrivial_opt_of_physical
)
end UQ

namespace HS
export DecisionQuotient.Physics.HeisenbergStrong (
  NoisyPhysicalEncoding
  HeisenbergStrongBinding
  strong_binding_implies_core_nontrivial
  strong_binding_yields_core_encoding_witness
  strong_binding_implies_physical_nontrivial_opt_assumption
  strong_binding_implies_nontrivial_opt_via_uncertainty
)
end HS

namespace WD
export DecisionQuotient (
  witnessBudgetEmpty
  checkingBudgetPairs
  checking_witnessing_duality_budget
  no_sound_checker_below_witness_budget
  checking_time_ge_witness_budget
)
end WD

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

-- NOTE: Do NOT use "DQ" as a namespace - it conflicts with auto-generated DQ### IDs.
namespace CCC
export DecisionQuotient.CC (
  anchor_sigma2p_complete_conditional
  cost_asymmetry_eth_conditional
  dichotomy_conditional
  minsuff_collapse_to_conp_conditional
  minsuff_conp_complete_conditional
  sufficiency_conp_complete_conditional
  tractable_subcases_conditional
)
end CCC

/-! ## Stochastic/Sequential Hierarchy (DC prefix) -/

-- DC: Dichotomy/Complexity claims from StochasticSequential
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation
abbrev DC2 := StochasticSequential.stochastic_sequential_strict_separation
abbrev DC3 := StochasticSequential.complexity_dichotomy_hierarchy
abbrev DC4 := StochasticSequential.regime_hierarchy
abbrev DC5 := StochasticSequential.coNP_subset_PP
abbrev DC6 := StochasticSequential.PP_subset_PSPACE
abbrev DC7 := StochasticSequential.coNP_subset_PSPACE
abbrev DC8 := StochasticSequential.static_to_coNP
abbrev DC9 := StochasticSequential.stochastic_to_PP
abbrev DC10 := StochasticSequential.sequential_to_PSPACE
abbrev DC11 := StochasticSequential.ClaimClosure.claim_six_subcases
abbrev DC12 := StochasticSequential.ClaimClosure.claim_hierarchy
abbrev DC13 := StochasticSequential.ClaimClosure.claim_tractable_subcases_to_P
abbrev DC14 := StochasticSequential.stochastic_dichotomy
abbrev DC15 := StochasticSequential.above_threshold_hard
abbrev DC16 := @StochasticSequential.StochasticAnchorSufficient
abbrev DC17 := @StochasticSequential.StochasticAnchorSufficiencyCheck
abbrev DC18 := @StochasticSequential.stochastic_anchor_check_iff
abbrev DC19 := @StochasticSequential.stochastic_anchor_sufficient_of_stochastic_sufficient
abbrev DC20 := @StochasticSequential.SequentialAnchorSufficient
abbrev DC21 := @StochasticSequential.SequentialAnchorSufficiencyCheck
abbrev DC22 := @StochasticSequential.sequential_anchor_check_iff
abbrev DC23 := @StochasticSequential.sequential_anchor_sufficient_of_sequential_sufficient
abbrev DC24 := @StochasticSequential.StochasticAnchorCheckInstance
abbrev DC25 := @StochasticSequential.reduceMAJSAT_correct_anchor_strict
abbrev DC26 := @StochasticSequential.reduceMAJSAT_to_stochastic_anchor_reduction
abbrev DC27 := @StochasticSequential.SequentialAnchorCheckInstance
abbrev DC28 := @StochasticSequential.reduceTQBF_correct_anchor
abbrev DC29 := @StochasticSequential.reduceTQBF_to_sequential_anchor_reduction
abbrev DC30 := @StochasticSequential.StatePotential
abbrev DC31 := @StochasticSequential.utilityFromPotentialDrop_le_iff_nextPotential_ge
abbrev DC32 := @StochasticSequential.utility_from_action_state_potential
abbrev DC33 := @StochasticSequential.stochasticExpectedUtility_eq_neg_expectedActionPotential
abbrev DC34 := @StochasticSequential.stochasticExpectedUtility_le_iff_expectedActionPotential_ge
abbrev DC35 := @StochasticSequential.landauerEnergyFloor_nonneg
abbrev DC36 := @StochasticSequential.landauerEnergyFloor_mono_bits
abbrev DC37 := @StochasticSequential.thermodynamicCost_eq_landauerEnergyFloorRoom_states

-- SS: Stochastic/Sequential completeness theorems (polymorphic - instantiated in ClaimClosure)
-- SS1-SS5 are polymorphic theorems, referenced via DC handles for paper mapping

/-! ## Conversation Physics (CV) handles -/

abbrev CV1 := @Physics.Conversation.RecurrentCircuit
abbrev CV2 := @Physics.Conversation.CoupledConversation
abbrev CV3 := @Physics.Conversation.JointState
abbrev CV4 := @Physics.Conversation.tick_uses_shared_node
abbrev CV5 := @Physics.Conversation.tick_shared_is_merged_emissions
abbrev CV6 := @Physics.Conversation.channel_projection_eq_iff_quantized_eq
abbrev CV7 := @Physics.Conversation.clamp_projection_eq_iff_same_clamped_bit
abbrev CV8 := @Physics.Conversation.clampDecisionEvent_iff_bitOps_pos
abbrev CV9 := @Physics.Conversation.clamp_event_implies_positive_energy
abbrev CV10 := @Physics.Conversation.explanationGap_add_explanationBits
abbrev CV11 := @Physics.Conversation.toClaimReport
abbrev CV12 := @Physics.Conversation.abstain_iff_no_answer
abbrev CV13 := @Physics.Conversation.yes_no_iff_exact_claim
abbrev CV14 := @Physics.Conversation.toReportSignal_completion_defined_of_budget
abbrev CV15 := @Physics.Conversation.toReportSignal_signal_consistent_zero_certified
abbrev CV16 := @Physics.Conversation.abstain_report_can_carry_explanation

/-! ## Physics Claims Handle Abbreviations -/

-- Decision Equivalence (DE) handles
abbrev DE1 := ClaimClosure.DE1
abbrev DE2 := ClaimClosure.DE2
abbrev DE3 := ClaimClosure.DE3
abbrev DE4 := ClaimClosure.DE4

-- Molecular Integrity (MI) handles
abbrev MI1 := ClaimClosure.MI1
abbrev MI2 := ClaimClosure.MI2
abbrev MI3 := ClaimClosure.MI3
abbrev MI4 := ClaimClosure.MI4
abbrev MI5 := ClaimClosure.MI5

-- Self-Reference (SR) handles
abbrev SR1 := ClaimClosure.SR1
abbrev SR2 := ClaimClosure.SR2
abbrev SR3 := ClaimClosure.SR3
abbrev SR4 := ClaimClosure.SR4
abbrev SR5 := ClaimClosure.SR5

-- Information Access (IA) handles
abbrev IA1 := ClaimClosure.IA1
abbrev IA2 := ClaimClosure.IA2
abbrev IA3 := ClaimClosure.IA3
abbrev IA4 := ClaimClosure.IA4
abbrev IA5 := ClaimClosure.IA5
abbrev IA6 := ClaimClosure.IA6

-- Gap Energy (GE) handles
abbrev GE1 := ClaimClosure.GE1
abbrev GE2 := ClaimClosure.GE2
abbrev GE3 := ClaimClosure.GE3
abbrev GE4 := ClaimClosure.GE4
abbrev GE5 := ClaimClosure.GE5
abbrev GE6 := ClaimClosure.GE6
abbrev GE7 := ClaimClosure.GE7
abbrev GE8 := ClaimClosure.GE8
abbrev GE9 := ClaimClosure.GE9

-- Integrity Equilibrium (IE) handles
abbrev IE1 := ClaimClosure.IE1
abbrev IE2 := ClaimClosure.IE2
abbrev IE3 := ClaimClosure.IE3
abbrev IE4 := ClaimClosure.IE4
abbrev IE5 := ClaimClosure.IE5
abbrev IE6 := ClaimClosure.IE6
abbrev IE7 := ClaimClosure.IE7
abbrev IE8 := ClaimClosure.IE8
abbrev IE9 := ClaimClosure.IE9
abbrev IE10 := ClaimClosure.IE10
abbrev IE11 := ClaimClosure.IE11
abbrev IE12 := ClaimClosure.IE12
abbrev IE13 := ClaimClosure.IE13
abbrev IE14 := ClaimClosure.IE14
abbrev IE15 := ClaimClosure.IE15
abbrev IE16 := ClaimClosure.IE16
abbrev IE17 := ClaimClosure.IE17

-- Substrate Energy (SE) handles
abbrev SE1 := ClaimClosure.SE1
abbrev SE2 := ClaimClosure.SE2
abbrev SE3 := ClaimClosure.SE3
abbrev SE4 := ClaimClosure.SE4
abbrev SE5 := ClaimClosure.SE5
abbrev SE6 := ClaimClosure.SE6

-- Channel (CH) handles
abbrev CH1 := ClaimClosure.CH1
abbrev CH2 := ClaimClosure.CH2
abbrev CH3 := ClaimClosure.CH3
abbrev CH5 := ClaimClosure.CH5
abbrev CH6 := ClaimClosure.CH6

-- Atomic/Orbital (AC) handles
abbrev AC1 := ClaimClosure.AtomicCircuitExports.AC1
abbrev AC3 := ClaimClosure.AtomicCircuitExports.AC3
abbrev AC4 := ClaimClosure.AtomicCircuitExports.AC4
abbrev AC5 := ClaimClosure.AtomicCircuitExports.AC5
abbrev AC6 := ClaimClosure.AtomicCircuitExports.AC6
abbrev AC8 := ClaimClosure.AtomicCircuitExports.AC8
abbrev AC9 := ClaimClosure.AtomicCircuitExports.AC9
abbrev AC11 := ClaimClosure.AtomicCircuitExports.AC11

-- Discrete State (DS) handles
abbrev DS1 := ClaimClosure.DS1
abbrev DS2 := ClaimClosure.DS2
abbrev DS3 := ClaimClosure.DS3
abbrev DS4 := ClaimClosure.DS4
abbrev DS5 := ClaimClosure.DS5
abbrev DS6 := ClaimClosure.DS6

-- Decision Quotient (DQ) handles from IntegrityEquilibrium
abbrev DQ1 := ClaimClosure.DQ1  -- Mutual information
abbrev DQ2 := ClaimClosure.DQ2  -- DecisionQuotient structure
abbrev DQ3 := ClaimClosure.DQ3  -- DQ from gap
abbrev DQ4 := ClaimClosure.DQ4  -- Zero gap = DQ 1
abbrev DQ5 := ClaimClosure.DQ5  -- Max gap = DQ 0
abbrev DQ6 := ClaimClosure.DQ6  -- DQ + Gap = Total
abbrev DQ7 := ClaimClosure.DQ7  -- DQ monotonic
abbrev DQ8 := ClaimClosure.DQ8  -- DQ thermodynamic interpretation

-- Decision Problem (DP) additional handles
abbrev DP6 := ClaimClosure.DP6  -- Empty-set sufficiency iff constant
abbrev DP7 := ClaimClosure.DP7  -- Non-sufficiency iff counterexample
abbrev DP8 := ClaimClosure.DP8  -- Empty-set non-sufficiency iff distinct opt

-- Query Complexity (QC) handles - polymorphic theorems referenced via CC handles for paper mapping
-- QC1-QC7 are polymorphic theorems, paper uses CC49, CC50 for query obstruction

-- Bayesian Bridge (BB) handles - connecting Bayes to Decision Quotient
abbrev BB1 := BayesianDQ
abbrev BB2 := BayesianDQ.certaintyGain
abbrev BB3 := dq_is_bayesian_certainty_fraction
abbrev BB4 := bayesian_dq_matches_physics_dq
abbrev BB5 := dq_derived_from_bayes

-- Physical no-go extension (PH) handles - P=NP transfer schema
abbrev PH11 := @PhysicalComplexity.PhysicalCollapseAtRequirement
abbrev PH12 := @PhysicalComplexity.no_physical_collapse_at_requirement
abbrev PH13 := @PhysicalComplexity.canonical_physical_collapse_impossible
abbrev PH14 := @PhysicalComplexity.p_eq_np_physically_impossible_of_collapse_map
abbrev PH15 := @PhysicalComplexity.p_eq_np_physically_impossible_canonical
abbrev PH16 := @PhysicalComplexity.P_eq_NP_via_SAT
abbrev PH17 := @PhysicalComplexity.SAT3ReductionBridge
abbrev PH18 := @PhysicalComplexity.sat_reduction_transfers_energy_lower_bound
abbrev PH19 := @PhysicalComplexity.physical_collapse_of_polytime_sat_realization
abbrev PH20 := @PhysicalComplexity.p_eq_np_physically_impossible_via_sat_bridge
abbrev PH21 := @PhysicalComplexity.SAT3HardFamily
abbrev PH22 := @PhysicalComplexity.p_eq_np_physically_impossible_via_sat_hard_family
abbrev PH23 := @PhysicalComplexity.collapse_possible_without_positive_bit_cost
abbrev PH24 := @PhysicalComplexity.collapse_possible_without_exponential_lower_bound
abbrev PH25 := @PhysicalComplexity.no_go_transfer_requires_collapse_map
abbrev PH26 := @PhysicalComplexity.no_collapse_of_bounded_budget_pos_cost_exp_lb
abbrev PH27 := @PhysicalComplexity.collapse_implies_assumption_failure_disjunction
abbrev PH28 := @PhysicalComplexity.deterministic_no_physical_collapse
abbrev PH29 := @PhysicalComplexity.probabilistic_no_physical_collapse
abbrev PH30 := @PhysicalComplexity.sequential_no_physical_collapse
abbrev PH31 := @PhysicalComplexity.collapse_possible_with_unbounded_budget_profile
abbrev PH32 := @PhysicalComplexity.exp_budget_profile_unbounded
abbrev PH33 := @PhysicalComplexity.finite_budget_assumption_is_necessary
abbrev PH34 := @PhysicalComplexity.CoherentDQRejectionAtRequirement
abbrev PH35 := @PhysicalComplexity.coherent_dq_rejection_impossible_at_requirement
abbrev PH36 := @PhysicalComplexity.coherent_dq_rejection_impossible_canonical

-- Bayes-from-DQ (BF) handles - belief forcing before Bayes uniqueness
abbrev BF1 := @certainty_of_not_nondegenerateBelief
abbrev BF2 := @nondegenerateBelief_of_uncertaintyForced
abbrev BF3 := @forced_action_under_uncertainty
abbrev BF4 := @bayes_update_exists_of_nondegenerateBelief

-- Constraint-forcing (CF) handles - logic/time scaffold -> law/decision/thermo forcing
abbrev CF1 := @Physics.ConstraintForcing.laws_not_determined_of_parameter_separation
abbrev CF2 := @Physics.ConstraintForcing.logic_time_not_sufficient_for_unique_law
abbrev CF3 := @Physics.ConstraintForcing.laws_determined_implies_objective_determined
abbrev CF4 := @Physics.ConstraintForcing.objective_not_determined_of_parameter_separation
abbrev CF5 := @Physics.ConstraintForcing.forcedDecisionBits_pos_of_deadline
abbrev CF6 := @Physics.ConstraintForcing.actionForced_of_deadline
abbrev CF7 := @Physics.ConstraintForcing.nondegenerateBelief_of_deadline_and_uncertainty
abbrev CF8 := @Physics.ConstraintForcing.forced_decision_implies_positive_landauer_cost
abbrev CF9 := @Physics.ConstraintForcing.forced_decision_implies_positive_nv_work

-- Physical-state universality (PS) handles - generic physical-state semantics
abbrev PS1 := @Physics.ClaimTransport.PhysicalStateSemantics
abbrev PS2 := @Physics.ClaimTransport.physical_state_has_witness
abbrev PS3 := @Physics.ClaimTransport.physical_state_claim_of_instance_claim
abbrev PS4 := @Physics.ClaimTransport.physical_state_claim_of_universal_core

-- Observer-relative physical state-space (OR) handles
abbrev OR1 := @Physics.ObserverRelativeState.ObserverClass
abbrev OR2 := @Physics.ObserverRelativeState.obsEquiv
abbrev OR3 := @Physics.ObserverRelativeState.EffectiveStateSpace
abbrev OR4 := @Physics.ObserverRelativeState.project_eq_iff
abbrev OR5 := @Physics.ObserverRelativeState.observer_relative_equivalence_witness
abbrev OR6 := @Physics.ObserverRelativeState.PhysicalObserverClass
abbrev OR7 := @Physics.ObserverRelativeState.PhysicalStateSpace
abbrev OR8 := @Physics.ObserverRelativeState.physical_state_space_has_instance_witness
abbrev OR9 := @Physics.ObserverRelativeState.physical_observer_relative_effective_space

-- Graph nontriviality (GN) handles - cycles, observer surprisal, Bayes/DQ/physics bridge
abbrev GN1 := @LogicGraph.isCycle
abbrev GN2 := @LogicGraph.cycleWitnessBits_pos
abbrev GN3 := @LogicGraph.pathProb_nonneg
abbrev GN4 := @LogicGraph.pathSurprisal_nonneg_of_positive_mass
abbrev GN5 := @LogicGraph.nontrivialityScore_unknown
abbrev GN6 := @LogicGraph.observerEntropy_nonneg
abbrev GN7 := @LogicGraph.dqFromEntropy_in_unit_interval
abbrev GN8 := @LogicGraph.path_belief_forced_under_uncertainty
abbrev GN9 := @LogicGraph.bayes_update_exists_for_observer_paths
abbrev GN10 := @LogicGraph.cycle_witness_implies_positive_landauer
abbrev GN11 := @LogicGraph.cycle_witness_implies_positive_nv_work
abbrev GN12 := @LogicGraph.dna_erasure_implies_positive_landauer
abbrev GN13 := @LogicGraph.dna_room_temp_environmental_stability

-- Foundations (FN) handles - machine-checked Bayes optimality chain
-- (BayesOptimalityProof: zero axioms, zero sorry)
abbrev FN7 := @BayesOptimalityProof.KL_nonneg
abbrev FN8 := @BayesOptimalityProof.entropy_le_crossEntropy
abbrev FN12 := @BayesOptimalityProof.crossEntropy_eq_entropy_add_KL
abbrev FN14 := @BayesOptimalityProof.bayes_is_optimal
abbrev FN15 := @BayesOptimalityProof.KL_eq_sum_klFun
abbrev FN16 := @BayesOptimalityProof.KL_eq_zero_iff_eq

-- Thermodynamic-lift (TL) handles - Landauer calibration -> positive per-bit conversion
noncomputable abbrev TL1 := @ThermodynamicLift.landauerJoulesPerBit
abbrev TL2 := @ThermodynamicLift.landauerJoulesPerBit_pos
abbrev TL3 := @ThermodynamicLift.joulesPerBit_pos_of_landauer_calibration
abbrev TL4 := @ThermodynamicLift.energy_lower_mandatory_of_landauer_calibration

-- Tool-collapse (TC) handles - model-relative leverage collapse
abbrev TC1 := @ToolCollapse.WorkProfile
abbrev TC2 := @ToolCollapse.WorkModel
abbrev TC3 := @ToolCollapse.ToolModel
abbrev TC4 := @ToolCollapse.EventualStrictImprovement
abbrev TC5 := @ToolCollapse.EffectiveCollapse
abbrev TC6 := @ToolCollapse.tool_never_worse
abbrev TC7 := @ToolCollapse.strict_improvement_has_witness
abbrev TC8 := @ToolCollapse.effective_collapse_of_eventual_strict
abbrev TC9 := @ToolCollapse.expBaseline
abbrev TC10 := @ToolCollapse.linearTool
abbrev TC11 := @ToolCollapse.linear_tool_eventual_strict
abbrev TC12 := @ToolCollapse.linear_tool_effective_collapse

-- Anchor-query node (AQ) handles
abbrev AQ1 := @ClaimClosure.AQ1
abbrev AQ2 := @ClaimClosure.AQ2
abbrev AQ3 := @ClaimClosure.AQ3
abbrev AQ4 := @ClaimClosure.AQ4
abbrev AQ5 := @ClaimClosure.AQ5
abbrev AQ6 := @ClaimClosure.AQ6
abbrev AQ7 := @ClaimClosure.AQ7
abbrev AQ8 := @ClaimClosure.AQ8

end DecisionQuotient
