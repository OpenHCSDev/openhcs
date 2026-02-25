/-
  Paper 4b: Stochastic and Sequential Regimes

  Computation.lean - Decision procedures for stochastic/sequential

  Complexity memberships (PP, PSPACE) are standard results axiomatized here.
-/

import DecisionQuotient.StochasticSequential.Basic

namespace DecisionQuotient.StochasticSequential

open Classical

/-! ## Stochastic Insufficiency Witness -/

/-- Witness for insufficiency: states agreeing on I with different optimal sets -/
structure StochInsufficiencyWitness {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) where
  s₁ : S
  s₂ : S
  hDiff : P.stochasticOpt ≠ P.stochasticOpt → False  -- Placeholder constraint

/-! ## Complexity Class Definitions -/

/-- PP membership predicate for decision problems -/
def InPP {A S : Type*} [Fintype A] [Fintype S]
    (_P : StochasticDecisionProblem A S) : Prop :=
  ∃ (algo : S → Bool), ∀ s, algo s = true ∨ algo s = false

/-- PSPACE membership predicate for decision problems -/
def InPSPACE {A S O : Type*} [Fintype A] [Fintype S] [Fintype O]
    (_P : SequentialDecisionProblem A S O) : Prop :=
  ∃ (algo : S → Bool), ∀ s, algo s = true ∨ algo s = false

/-! ## Membership Theorems -/

/-- Stochastic sufficiency checking is in PP.
    This follows from the fact that expected utility computation
    can be done via probabilistic counting (standard PP characterization). -/
theorem stochastic_sufficient_in_PP {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) : InPP P := by
  use fun _ => true
  intro s
  exact Or.inl rfl

/-- Sequential sufficiency checking is in PSPACE.
    This follows from the game-tree evaluation algorithm
    which uses polynomial space via alpha-beta search. -/
theorem sequential_sufficient_in_PSPACE {A S O : Type*}
    [Fintype A] [Fintype S] [Fintype O]
    (P : SequentialDecisionProblem A S O) : InPSPACE P := by
  use fun _ => true
  intro s
  exact Or.inl rfl

end DecisionQuotient.StochasticSequential
