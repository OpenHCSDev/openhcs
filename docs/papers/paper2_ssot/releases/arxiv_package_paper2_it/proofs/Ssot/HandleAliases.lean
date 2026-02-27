/-!
Stable, semantic Lean-handle IDs for Paper 2 (IT).

The build system parses `abbrev CODE := target` and uses these IDs in
`lean_handle_ids_auto.tex`, which then powers `\LH{CODE}` links in the PDF.
-/

import Ssot.Basic
import Ssot.Bounds
import Ssot.ClaimClosure
import Ssot.Coherence
import Ssot.Completeness
import Ssot.Entropy
import Ssot.Foundations
import Ssot.Inconsistency
import Ssot.LangPython
import Ssot.Requirements

abbrev ENT1 := Entropy.ClassicalEntropyAssumptions
abbrev CIA1 := ClaimClosure.ClassicalInfoAssumptions
abbrev CIA2 := ClaimClosure.side_information_requirement_conditional
abbrev CIA3 := ClaimClosure.fano_converse_conditional
abbrev CIA4 := ClaimClosure.info_dof_conditional

abbrev ORA1 := oracle_arbitrary
abbrev COH1 := dof_one_implies_coherent
abbrev COH2 := dof_gt_one_incoherence_possible
abbrev COH3 := determinate_truth_forces_ssot

abbrev BAS1 := correctness_forcing
abbrev BAS2 := dof_inconsistency_potential
abbrev BAS3 := dof_gt_one_inconsistent

abbrev INS1 := Inconsistency.ssot_is_unique_optimum
abbrev INS2 := Inconsistency.ssot_required
abbrev INS3 := Inconsistency.ssot_unique_satisfier
abbrev INS4 := Inconsistency.resolution_requires_external_choice

abbrev CAP1 := ClaimClosure.cap_encoding_conditional
abbrev CAP2 := ssot_guarantees_coherence
abbrev CAP3 := non_ssot_permits_incoherence
abbrev FLP1 := ClaimClosure.static_flp_core
abbrev RED1 := ClaimClosure.redundancy_incoherence_equiv
abbrev RAT1 := ClaimClosure.rate_incoherence_step
abbrev DES1 := ClaimClosure.design_necessity
abbrev SID1 := ClaimClosure.dof1_zero_side_information
abbrev SID2 := ClaimClosure.side_information_scales_with_redundancy

abbrev DER1 := all_derived_from_source
abbrev DER2 := ClaimClosure.derivation_preserves_coherence_core
abbrev AXM1 := complete_mono
abbrev AXM2 := completeD_mono
abbrev AXM3 := minimal_no_redundant_axes
abbrev AXM4 := semantically_minimal_implies_independent
abbrev CPL1 := cost_ratio_eq_dof
abbrev REQ1 := structural_facts_fixed_at_definition
abbrev REQ2 := definition_hooks_necessary
abbrev REQ3 := introspection_necessary_for_verification
abbrev IND1 := both_requirements_independent
abbrev IND2 := both_requirements_independent'
abbrev SOT1 := ssot_iff
abbrev GEN1 := generated_file_is_second_encoding
abbrev LNG1 := ClaimClosure.language_realizability_criterion

abbrev BND1 := ssot_upper_bound
abbrev BND2 := non_ssot_lower_bound
abbrev BND3 := ssot_advantage_unbounded
abbrev BND4 := ClaimClosure.arbitrary_reduction_factor
abbrev REG1 := ClaimClosure.operating_regimes_partition
abbrev REG2 := ClaimClosure.pareto_optimality_p1
abbrev REG3 := ClaimClosure.no_tradeoff_at_p1
abbrev REG4 := ClaimClosure.amortized_complexity_core

abbrev PYH1 := Python.python_has_hooks
abbrev PYI1 := Python.python_has_introspection
