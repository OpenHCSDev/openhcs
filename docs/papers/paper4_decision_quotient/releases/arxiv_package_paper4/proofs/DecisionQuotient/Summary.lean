/-
  Paper 4: Decision-Relevant Uncertainty

  Summary.lean - mechanically backed summary aliases

  This module exposes compact theorem names that alias concrete results proved
  in the underlying modules. It does not introduce placeholder statements.
-/

import DecisionQuotient.Hardness
import DecisionQuotient.Tractability.BoundedActions
import DecisionQuotient.Tractability.SeparableUtility
import DecisionQuotient.Tractability.TreeStructure
import DecisionQuotient.Tractability.Tightness
import DecisionQuotient.Tractability.FPT
import DecisionQuotient.Dichotomy
import DecisionQuotient.ComplexityMain

namespace DecisionQuotient.Summary

/-- coNP-hardness reduction core for SUFFICIENCY-CHECK. -/
theorem conp_completeness {n : ℕ} (φ : Formula n) :
    (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology :=
  (DecisionQuotient.tautology_iff_sufficient φ).symm

/-- Bounded-actions tractability alias. -/
theorem bounded_actions_tractable
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (k : ℕ) (cdp : ComputableDecisionProblem A S)
    (hcard : Fintype.card A ≤ k) :
    ∃ (decide : Finset (Fin n) → Bool),
      ∀ I, decide I = true ↔ cdp.toAbstract.isSufficient I :=
  DecisionQuotient.sufficiency_poly_bounded_actions (k := k) (cdp := cdp) hcard

/-- Separable-utility tractability alias. -/
theorem separable_utility_tractable
    {A S : Type*} [DecidableEq A] [DecidableEq S] {n : ℕ} [CoordinateSpace S n]
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ dp.isSufficient I :=
  DecisionQuotient.sufficiency_poly_separable (dp := dp) hsep

/-- Tree-structured tractability alias. -/
theorem tree_structure_tractable
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S)
    (deps : Fin n → Finset (Fin n)) (htree : TreeStructured deps) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I :=
  DecisionQuotient.sufficiency_poly_tree_structured (cdp := cdp) deps htree

/-- Tightness alias. -/
theorem tractability_tightness :
    (∀ (n : ℕ) (φ : Formula n),
      (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology) ∧
    (∀ (n : ℕ) (φ : Formula n), (∃ a, φ.eval a = false) →
      ¬∃ (av : ReductionAction → ℝ) (sv : ReductionState n → ℝ),
        ∀ a s, reductionUtility φ a s = av a + sv s) ∧
    (∀ {A S : Type*} [Unique A] (dp : DecisionProblem A S)
      {n : ℕ} [CoordinateSpace S n] (I : Finset (Fin n)), dp.isSufficient I) :=
  DecisionQuotient.tractability_conditions_tight

/-- Parameterized-results alias. -/
theorem parameterized_results :
    (∀ {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
        {n : ℕ} [CoordinateSpace S n]
        [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
        (cdp : ComputableDecisionProblem A S),
        ∃ f : ℕ → ℕ, ∃ algo : Finset (Fin n) → Bool,
          (∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I) ∧
          (∀ k, 1 ≤ f k)) ∧
    (∀ {n : ℕ} (φ : Formula n),
      (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology) :=
  DecisionQuotient.parameterized_complexity_summary

/-- Dichotomy alias in terms of minimal-sufficient-set size relative to state
cardinality. -/
theorem complexity_dichotomy
    {A S : Type*} {n : ℕ}
    [DecidableEq (Set A)] [DecidableEq (Fin n)]
    [ProductSpace S n] [Fintype S] [Nonempty S]
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) :
    (I.card ≤ Nat.log 2 (Fintype.card S)) ∨
    (I.card > Nat.log 2 (Fintype.card S)) :=
  DecisionQuotient.dichotomy_by_relevant_size dp I hmin

end DecisionQuotient.Summary
