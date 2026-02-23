/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Finite.lean - Finite type utilities for stochastic/sequential
   
  Fintype instances and finite state reasoning.
-/

import Paper4bStochasticSequential.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card

namespace Paper4bStochasticSequential

/-! ## State Spaces -/

/-- StochState has 2^n + 1 elements (2^n assignments + 1 reference) -/
instance instFintypeStochState (n : ℕ) : Fintype (StochState n) := by
  unfold StochState
  infer_instance

/-- StochAction has 2 elements (accept and reject) -/
instance instFintypeStochAction : Fintype StochAction := by
  unfold StochAction
  infer_instance

/-- StochState is inhabited (reference is default) -/
instance instInhabitedStochState (n : ℕ) : Inhabited (StochState n) := ⟨StochState.reference⟩

/-- StochAction is inhabited (accept is default) -/
instance instInhabitedStochAction : Inhabited StochAction := ⟨StochAction.accept⟩

/-- Card of StochState is 2^n + 1 -/
theorem card_stochState (n : ℕ) : Fintype.card (StochState n) = 2^n + 1 := by
  simp only [StochState, Fintype.card_sum, Fintype.card_pi, Fintype.card_fin, 
             Fintype.card_bool, Fintype.card_unit]
  ring

/-- Card of StochAction is 2 -/
theorem card_stochAction : Fintype.card StochAction = 2 := by
  simp only [StochAction, Fintype.card_sum, Fintype.card_unit]
  ring

/-! ## Distribution Properties -/

/-- Distribution is valid probability mass function -/
def isProbabilityDistribution {S : Type*} [Fintype S] (dist : S → ℝ) : Prop :=
  (∑ s, dist s = 1) ∧ (∀ s, 0 ≤ dist s)

/-- StochState is nonempty -/
instance instNonemptyStochState (n : ℕ) : Nonempty (StochState n) := ⟨StochState.reference⟩

/-- StochAction is nonempty -/
instance instNonemptyStochAction : Nonempty StochAction := ⟨StochAction.accept⟩

/-- Uniform distribution over StochState -/
def uniformStochDistribution (n : ℕ) : StochState n → ℝ :=
  uniformDistribution (StochState n)

/-- Uniform distribution sums to 1 -/
theorem uniformStochDistribution_valid (n : ℕ) :
    isProbabilityDistribution (uniformStochDistribution n) := by
  constructor
  · simp only [uniformStochDistribution, uniformDistribution, Finset.sum_const, 
               Finset.card_univ, Fintype.card, mul_one, nsmul_eq_mul]
    field_simp [card_stochState]
  · intro s
    simp only [uniformStochDistribution, uniformDistribution]
    positivity

/-! ## Uniform Distribution -/

def uniformDistribution {S : Type*} [Fintype S] : S → ℝ :=
  fun _ => 1 / (Fintype.card S : ℝ)

theorem uniform_is_valid {S : Type*} [Fintype S] [Nonempty S] :
    isProbabilityDistribution (uniformDistribution S) := by
  constructor
  · simp only [uniformDistribution, Finset.sum_const, Finset.card_univ, 
               Fintype.card, mul_one, nsmul_eq_mul]
    field_simp [Fintype.card]
  · intro s
    positivity

end Paper4bStochasticSequential
