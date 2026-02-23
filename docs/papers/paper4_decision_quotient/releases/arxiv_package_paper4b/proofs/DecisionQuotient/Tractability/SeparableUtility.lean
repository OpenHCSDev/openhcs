/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/SeparableUtility.lean - Separable utilities admit efficient checks
-/

import DecisionQuotient.Finite

namespace DecisionQuotient

open Classical

variable {A S : Type*} [DecidableEq A] [DecidableEq S]

/-- A separable utility structure: action and state contributions add. -/
structure SeparableUtility (dp : FiniteDecisionProblem (A := A) (S := S)) where
  actionValue : A → ℤ
  stateValue : S → ℤ
  utility_eq : ∀ a s, dp.utility a s = actionValue a + stateValue s

lemma mem_optimalActions_iff_actionValue
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) (s : S) (a : A) :
    a ∈ dp.optimalActions s ↔
      a ∈ dp.actions ∧ ∀ a' ∈ dp.actions, hsep.actionValue a' ≤ hsep.actionValue a := by
  constructor
  · intro ha
    rcases (FiniteDecisionProblem.mem_optimalActions_iff (dp := dp) (s := s) (a := a)).1 ha with
      ⟨haA, hmax⟩
    refine ⟨haA, ?_⟩
    intro a' ha'
    have hmax' := hmax a' ha'
    have hmax'' :
        hsep.actionValue a' + hsep.stateValue s ≤ hsep.actionValue a + hsep.stateValue s := by
      simpa [hsep.utility_eq] using hmax'
    exact (add_le_add_iff_right (hsep.stateValue s)).1 hmax''
  · intro ha
    rcases ha with ⟨haA, hmax⟩
    refine (FiniteDecisionProblem.mem_optimalActions_iff (dp := dp) (s := s) (a := a)).2 ?_
    refine ⟨haA, ?_⟩
    intro a' ha'
    have hmax' := hmax a' ha'
    have :
        hsep.actionValue a' + hsep.stateValue s ≤ hsep.actionValue a + hsep.stateValue s :=
      (add_le_add_iff_right (hsep.stateValue s)).2 hmax'
    simpa [hsep.utility_eq] using this

lemma optimalActions_eq_of_separable
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) (s s' : S) :
    dp.optimalActions s = dp.optimalActions s' := by
  classical
  ext a
  constructor <;> intro ha
  ·
    have ha' := (mem_optimalActions_iff_actionValue (dp := dp) hsep s a).1 ha
    exact (mem_optimalActions_iff_actionValue (dp := dp) hsep s' a).2 ha'
  ·
    have ha' := (mem_optimalActions_iff_actionValue (dp := dp) hsep s' a).1 ha
    exact (mem_optimalActions_iff_actionValue (dp := dp) hsep s a).2 ha'

lemma separable_isSufficient
    {n : ℕ} [CoordinateSpace S n]
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) (I : Finset (Fin n)) :
    dp.isSufficient I := by
  intro s hs s' hs' _
  exact optimalActions_eq_of_separable (dp := dp) hsep s s'

/-- For separable utilities, we register the existence of a simple decision
    procedure: all coordinate sets are sufficient because optimal actions
    do not depend on the state. -/
theorem sufficiency_poly_separable
    {n : ℕ} [CoordinateSpace S n] (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ dp.isSufficient I := by
  refine ⟨fun _ => true, ?_⟩
  intro I
  constructor
  · intro _; exact separable_isSufficient (dp := dp) hsep I
  · intro _; rfl

end DecisionQuotient
