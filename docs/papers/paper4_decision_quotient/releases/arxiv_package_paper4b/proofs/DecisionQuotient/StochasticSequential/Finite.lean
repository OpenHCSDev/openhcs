/-
  Paper 4b: Stochastic and Sequential Regimes

  Finite.lean - Finite type utilities for stochastic/sequential

  Additional finite state reasoning. Core instances are in Basic.lean.
-/

import DecisionQuotient.StochasticSequential.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card

namespace DecisionQuotient.StochasticSequential

/-! ## State Spaces -/

-- StochState is now an alias for Assignment n = Fin n → Bool (see Basic.lean)

/-- StochState is inhabited (all-false assignment is default) -/
instance instInhabitedStochState (n : ℕ) : Inhabited (StochState n) := ⟨fun _ => false⟩

/-- StochAction is inhabited (accept is default) -/
instance instInhabitedStochAction : Inhabited StochAction := ⟨StochAction.accept⟩

/-- StochState is nonempty -/
instance instNonemptyStochState (n : ℕ) : Nonempty (StochState n) := ⟨fun _ => false⟩

/-- StochAction is nonempty -/
instance instNonemptyStochAction : Nonempty StochAction := ⟨StochAction.accept⟩

/-- Card of StochState is 2^n (number of Boolean assignments) -/
theorem card_stochState (n : ℕ) : Fintype.card (StochState n) = 2^n := by
  -- StochState n = Assignment n = Fin n → Bool
  -- Card = 2^n
  simp only [StochState, Assignment, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]


/-- Card of StochAction is 2 -/
theorem card_stochAction : Fintype.card StochAction = 2 := by
  rfl

/-! ## Distribution Properties -/

/-- Distribution is valid probability mass function -/
def isProbabilityDistribution {S : Type*} [Fintype S] (dist : S → ℝ) : Prop :=
  (∑ s, dist s = 1) ∧ (∀ s, 0 ≤ dist s)

/-! ## Uniform Distribution -/

/-- Uniform distribution function -/
noncomputable def uniformDistribution (S : Type*) [Fintype S] : S → ℝ :=
  fun _ => 1 / (Fintype.card S : ℝ)

/-- Uniform distribution over StochState -/
noncomputable def uniformStochDistribution (n : ℕ) : StochState n → ℝ :=
  uniformDistribution (StochState n)

/-- Uniform distribution sums to 1 -/
theorem uniformStochDistribution_valid (n : ℕ) :
    isProbabilityDistribution (uniformStochDistribution n) := by
  constructor
  · -- Sum of uniform distribution = 1
    unfold uniformStochDistribution uniformDistribution
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [card_stochState]
    have h2n : (2^n : ℝ) ≠ 0 := by positivity
    field_simp [h2n]
  · intro _
    unfold uniformStochDistribution uniformDistribution
    positivity

/-- Generic uniform distribution validity -/
theorem uniform_is_valid {S : Type*} [Fintype S] [Nonempty S] :
    isProbabilityDistribution (uniformDistribution S) := by
  constructor
  · unfold uniformDistribution
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp [hcard]
  · intro _
    unfold uniformDistribution
    positivity

end DecisionQuotient.StochasticSequential
