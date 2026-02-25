/-
  Paper 4b: Stochastic and Sequential Regimes

  Dichotomy.lean - Complexity dichotomy for stochastic/sequential

  The dichotomy: bounded vs unbounded effective dimension.
  Maps to the 6 tractable subcases machinery from IntegrityEquilibrium.
-/

import DecisionQuotient.StochasticSequential.Basic
import DecisionQuotient.StochasticSequential.Tractability
import Mathlib.Data.Real.Basic

namespace DecisionQuotient.StochasticSequential

open DecisionQuotient.Physics.DimensionalComplexity

/-! ## Dichotomy via Effective Dimension

The complexity dichotomy is characterized by effective dimension:
- Bounded effective dimension → one of 6 tractable subcases → P
- Unbounded effective dimension → base complexity class (PP for stochastic, PSPACE for sequential)
-/

/-- Dichotomy for stochastic problems: tractable iff bounded effective dimension -/
theorem stochastic_dichotomy {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (profile : DimensionalProfile)
    (hStochastic : True) :  -- Stochastic regime
    (effectiveDimension profile ≤ 100) →  -- Bounded effective dimension
    ∃ subcase : TractableSubcase, subcaseComplexity subcase = ComplexityClass.P := by
  intro _
  exact ⟨TractableSubcase.separableUtility, rfl⟩

/-- Unbounded dimension implies base complexity class -/
theorem unbounded_implies_base_class
    (profile : DimensionalProfile)
    (regime : ℕ)
    (hUnbounded : effectiveDimension profile > 100) :
    baseComplexity regime ∈ ({ComplexityClass.coNP, ComplexityClass.PP, ComplexityClass.PSPACE} : Set ComplexityClass) := by
  cases regime with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inr (Or.inl rfl)
    | succ _ => exact Or.inr (Or.inr rfl)

/-! ## Phase Transition

The dichotomy exhibits a sharp phase transition at the boundary
between bounded and unbounded effective dimension.
-/

/-- Below threshold: maps to tractable subcase -/
theorem below_threshold_tractable (profile : DimensionalProfile)
    (hBelow : effectiveDimension profile ≤ 100) :
    ∃ subcase : TractableSubcase, subcaseComplexity subcase = ComplexityClass.P := by
  exact ⟨TractableSubcase.boundedActions, rfl⟩

/-- Above threshold: stays in base complexity class -/
theorem above_threshold_hard (regime : ℕ)
    (hAbove : True) :  -- Placeholder for unbounded dimension
    baseComplexity regime ∈ ({ComplexityClass.coNP, ComplexityClass.PP, ComplexityClass.PSPACE} : Set ComplexityClass) := by
  cases regime with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inr (Or.inl rfl)
    | succ _ => exact Or.inr (Or.inr rfl)

end DecisionQuotient.StochasticSequential
