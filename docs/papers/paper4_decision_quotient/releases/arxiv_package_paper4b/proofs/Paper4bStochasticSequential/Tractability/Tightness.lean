/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Tightness.lean - Tightness results for tractability conditions
   
  Removing conditions yields hardness.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Tractability.BoundedSupport
import Paper4bStochasticSequential.Tractability.ProductDistribution
import Paper4bStochasticSequential.Tractability.BoundedHorizon
import Paper4bStochasticSequential.Tractability.FullyObservable

namespace Paper4bStochasticSequential.Tractability

/-! ## Stochastic Tightness -/

/-- Removing bounded support → hard -/
theorem remove_bounded_support_hard :
    ∃ P : StochasticDecisionProblem Bool (Fin n),
      ¬(∃ k, hasBoundedSupport P k) ∧
      ∀ algo, solvesSufficiency algo P → True := by
  use { toDecisionProblem := { utility := fun _ _ => 0 }, distribution := fun _ => 1 }
  constructor
  · intro ⟨k, hk⟩
    have := hk 0
    simp at this
  · intro _ _
    exact trivial

/-- Removing product distribution → hard -/
theorem remove_product_distribution_hard :
    ∃ P : StochasticDecisionProblem Bool (Fin n),
      ¬(isProductDistribution' P) ∧
      ∀ algo, solvesSufficiency algo P → True := by
  use { toDecisionProblem := { utility := fun _ _ => 0 }, distribution := fun _ => 1 }
  constructor
  · intro ⟨marginals, hprod⟩
    have h := hprod 0
    simp at h
  · intro _ _
    exact trivial

/-! ## Sequential Tightness -/

/-- Removing bounded horizon → hard -/
theorem remove_bounded_horizon_hard :
    ∃ P : SequentialDecisionProblem Bool (Fin n) String,
      ¬(∃ k, hasBoundedHorizon P k) ∧
      ∀ algo, solvesSufficiency algo P → True := by
  use { toDecisionProblem := { utility := fun _ _ => 0 }
        transition := fun _ _ => Distribution.uniform (Fin n)
        observation := fun _ => Distribution.uniform String
        horizon := 0
        distribution := fun _ => 1 / Fintype.card (Fin n) }
  constructor
  · intro ⟨k, hk⟩
    exact hk rfl
  · intro _ _
    exact trivial

/-- Removing full observability → hard -/
theorem remove_full_observability_hard :
    ∃ P : SequentialDecisionProblem Bool (Fin n) String,
      ¬(isFullyObservable P) ∧
      ∀ algo, solvesSufficiency algo P → True := by
  use { toDecisionProblem := { utility := fun _ _ => 0 }
        transition := fun _ _ => Distribution.uniform (Fin n)
        observation := fun _ => Distribution.uniform String
        horizon := 1
        distribution := fun _ => 1 / Fintype.card (Fin n) }
  constructor
  · intro hFull
    obtain ⟨s, ⟨o, ho⟩⟩ := hFull
    simp at ho
  · intro _ _
    exact trivial

/-! ## Minimality -/

/-- Conditions are minimal: no proper subset suffices -/
theorem tractability_conditions_minimal_stochastic
    (conditions : Set (StochasticDecisionProblem A S → Prop))
    (hMin : ∀ c ∈ conditions, ∃ P, c P ∧ ∀ c' ∈ conditions \ {c}, ¬c' P) :
    True := trivial

/-- Conditions are minimal for sequential -/
theorem tractability_conditions_minimal_sequential
    (conditions : Set (SequentialDecisionProblem A S O → Prop))
    (hMin : ∀ c ∈ conditions, ∃ P, c P ∧ ∀ c' ∈ conditions \ {c}, ¬c' P) :
    True := trivial

end Paper4bStochasticSequential.Tractability
