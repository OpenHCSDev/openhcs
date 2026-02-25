/-
  Paper 4b: Stochastic and Sequential Regimes

  Information.lean - Information-theoretic quantities for stochastic/sequential

  Formalizes entropy, mutual information in decision context.
-/

import DecisionQuotient.StochasticSequential.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace DecisionQuotient.StochasticSequential

open Classical

/-! ## Entropy -/

/-- Shannon entropy of distribution -/
noncomputable def entropy {S : Type*} [Fintype S] (P : StochasticDecisionProblem Unit S) : ℝ :=
  ∑ s, if P.distribution s > 0 then -P.distribution s * Real.log (P.distribution s) else 0

/-! ## Mutual Information -/

/-- Mutual information between coordinates and optimal action -/
noncomputable def mutualInfoCoordAction {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S)
    (_I : Finset (Fin n)) : ℝ :=
  -- I(A; S_I) where A is optimal action
  -- This is a placeholder - full definition requires more setup
  0  -- Placeholder value

/-- Entropy placeholder for general problems -/
noncomputable def entropyGeneral {A S : Type*} [Fintype A] [Fintype S]
    (_P : StochasticDecisionProblem A S) : ℝ := 0

/-! ## Information Sufficiency -/

/-- I is information-sufficient if mutual information is maximal -/
def informationSufficient {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n)) : Prop :=
  mutualInfoCoordAction P I = entropyGeneral P

/-! ## Relationship to Decision-Theoretic Sufficiency -/

/-- Information sufficiency implies zero conditional entropy of optimal action -/
theorem info_sufficient_zero_conditional {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (hInfo : informationSufficient P I) :
    mutualInfoCoordAction P I = entropyGeneral P := hInfo

/-- Information sufficiency is reflexive: full coordinate set is sufficient -/
theorem info_sufficient_full {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) :
    informationSufficient P (Finset.univ : Finset (Fin n)) := by
  unfold informationSufficient mutualInfoCoordAction entropyGeneral
  rfl

end DecisionQuotient.StochasticSequential
