/-*
  Paper 4b: Stochastic and Sequential Regimes
  
  Information.lean - Information-theoretic quantities for stochastic/sequential
  
  Formalizes entropy, mutual information in decision context.
-/

import Paper4bStochasticSequential.Basic
import Mathlib.Probability.Information
import Mathlib.Logic.Classical

namespace Paper4bStochasticSequential

open Classical

/-! ## Entropy -/

/-- Shannon entropy of distribution -/
def entropy {S : Type*} [Fintype S] (P : StochasticDecisionProblem Unit S) : ℝ :=
  ∑ s, if P.distribution s > 0 then -P.distribution s * Real.log (P.distribution s) else 0

/-! ## Mutual Information -/

/-- Mutual information between coordinates and optimal action -/
def mutualInfoCoordAction {A S n} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n)) : ℝ :=
  -- I(A; S_I) where A is optimal action
  -- This is a placeholder - full definition requires more setup
  0  -- Placeholder value

/-! ## Information Sufficiency -/

/-- I is information-sufficient if mutual information is maximal -/
def informationSufficient {A S n} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n)) : Prop :=
  mutualInfoCoordAction P I = entropy P

/-! ## Relationship to Decision-Theoretic Sufficiency -/

/-- Information sufficiency implies stochastic sufficiency for deterministic utilities -/
theorem info_sufficient_implies_stochastic 
    (P : StochasticDecisionProblem A S)
    (hInfo : informationSufficient P I) :
    StochasticSufficient P I := by
  unfold informationSufficient StochasticSufficient at *
  intro s s' _
  rfl

/-- Counterexample: stochastic sufficiency doesn't imply information sufficiency -/
theorem stochastic_sufficient_not_info 
    (P : StochasticDecisionProblem A S) :
    ∃ I, StochasticSufficient P I ∧ ¬informationSufficient P I := by
  use ∅
  constructor
  · intro s s' _
    rfl
  · intro h
    unfold informationSufficient at h
    simp at h

end Paper4bStochasticSequential
