import Ssot.Basic
import Ssot.Bounds
import Ssot.ClaimClosure
import Ssot.Coherence
import Ssot.Completeness
import Ssot.CrossPaperDependencies  -- Bridge theorems linking Paper 2 → Paper 1
import Ssot.Entropy
import Ssot.GraphEntropy
import Ssot.Foundations
import Ssot.Inconsistency
import Ssot.LangPython
import Ssot.Requirements
import axis_framework

open Ssot

/-- Stable, semantic Lean-handle IDs for Paper 2 (IT).

    The build system parses `abbrev CODE := target` and uses these IDs in
    `lean_handle_ids_auto.tex`, which then powers `\LH{CODE}` links in the PDF. -/

abbrev ENT1 := Entropy.ClassicalEntropyAssumptions
abbrev GPH2 := @GraphEntropy.clique_card_le_colors
abbrev GPH3 := @GraphEntropy.complete_graph_needs_all_colors
abbrev CIA1 := ClaimClosure.ClassicalInfoAssumptions
-- CIA2-CIA4 require ClassicalInfoAssumptions instance; define as functions taking instance explicitly
abbrev CIA2 := fun (inst : ClaimClosure.ClassicalInfoAssumptions) =>
  @ClaimClosure.side_information_requirement_conditional inst
abbrev CIA3 := fun (inst : ClaimClosure.ClassicalInfoAssumptions) =>
  @ClaimClosure.fano_converse_conditional inst
abbrev CIA4 := fun (inst : ClaimClosure.ClassicalInfoAssumptions) =>
  @ClaimClosure.info_dof_conditional inst

abbrev ORA1 := oracle_arbitrary
abbrev COH1 := dof_one_implies_coherent
abbrev COH2 := dof_gt_one_incoherence_possible
abbrev COH3 := determinate_truth_forces_ssot

abbrev BAS1 := Ssot.correctness_forcing
abbrev BAS2 := Ssot.dof_inconsistency_potential
abbrev BAS3 := Ssot.dof_gt_one_inconsistent

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

-- DER1: all_derived_from_source requires Location, DerivationSystem, source, and all_locations parameters
-- Use: `all_derived_from_source D source locations` where D : DerivationSystem Location
abbrev DER1 := @all_derived_from_source
abbrev DER2 := ClaimClosure.derivation_preserves_coherence_core
abbrev AXM1 := @complete_mono
abbrev AXM2 := @completeD_mono
abbrev AXM3 := @minimal_no_redundant_axes
abbrev AXM4 := @semantically_minimal_implies_independent
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

/-! ## FIRST PRINCIPLES FORCING CHAIN
    These theorems establish that SSOT is FORCED by first principles.
    The chain: Derivation → Causality → Trichotomy → Only source_hooks works → SSOT unique

    If you accept "derivation" as a coherent concept, you MUST accept trichotomy.
    If you accept trichotomy, only source_hooks achieves SSOT.
    Therefore, SSOT is forced by first principles - cannot be honestly rejected.
-/

-- Trichotomy theorems (TRI*): Timing trichotomy and its necessity
abbrev TRI1 := timing_trichotomy_exhaustive      -- Trichotomy is exhaustive
abbrev TRI2 := trichotomy_necessary_for_causality -- Causality requires trichotomy
abbrev TRI3 := trichotomy_necessary_for_mechanism -- Mechanisms require trichotomy
abbrev TRI4 := no_mechanism_outside_trichotomy   -- No mechanism outside trichotomy

-- Model completeness theorems (MDL*): Mechanism enumeration and capability
abbrev MDL1 := mechanisms_cover_all_timings      -- Mechanisms cover all timing categories
abbrev MDL2 := mechanism_exhaustiveness          -- Every mechanism has valid timing
abbrev MDL3 := only_at_definition_works          -- Only at_definition timing works
abbrev MDL4 := mechanism_structural_capability   -- Source_hooks is uniquely capable
abbrev MDL5 := model_completeness                -- achieves_ssot ↔ source_hooks

-- Uniqueness theorems (UNQ*): SSOT mechanism is unique
abbrev UNQ1 := uniqueness                        -- Combined existence + uniqueness
abbrev UNQ2 := uniqueness_exists                 -- ∃ mechanism achieving SSOT
abbrev UNQ3 := uniqueness_unique                 -- All SSOT mechanisms are source_hooks

-- Adversary/impossibility theorems (ADV*): Why alternatives fail
abbrev ADV1 := adversary_construction            -- m ≠ source_hooks → fails
abbrev ADV2 := derivation_impossibility          -- No alternative works
abbrev ADV3 := compile_macros_insufficient       -- Compile macros fail
abbrev ADV4 := build_codegen_insufficient        -- Build codegen fails
abbrev ADV5 := runtime_reflection_too_late       -- Runtime reflection fails

-- Independence theorems (IND*): External tools don't count
abbrev IND3 := external_tools_not_derivation     -- External tools can be bypassed
abbrev IND4 := language_semantics_is_derivation  -- Language semantics is derivation
abbrev IND5 := ide_refactoring_not_derivation    -- IDE refactoring not derivation
