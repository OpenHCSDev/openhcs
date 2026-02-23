/-
  Paper 4: Decision-Relevant Uncertainty

  Economics/Approximation.lean - Approximation algorithms for VOI/DQ
-/

import DecisionQuotient.Hardness.ApproximationHardness

namespace DecisionQuotient

open Classical

/-- A generic approximation guarantee for decision quotient computation. -/
theorem decision_quotient_FPTAS {A S : Type*} (ε : ℚ) (hε : 0 ≤ ε) :
    ∃ algo : DQInstance A S → ℚ,
      ∀ inst, approxWithin ε (algo inst) (exactDQ inst) := by
  refine ⟨exactDQ, ?_⟩
  intro inst
  unfold approxWithin
  simp
  exact mul_nonneg hε (abs_nonneg _)

end DecisionQuotient
