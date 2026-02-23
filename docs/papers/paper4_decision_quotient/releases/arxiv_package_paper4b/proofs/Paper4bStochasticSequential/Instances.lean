/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Instances.lean - Concrete instantiations of stochastic/sequential problems
   
  Provides example problems for each regime.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Tractability
import Mathlib.Data.Real.Basic

namespace Paper4bStochasticSequential

/-! ## Static Instance -/

/-- Classic umbrella decision -/
def umbrellaStatic : DecisionProblem Bool (Fin 2) :=
  { utility := fun a s =>
    match a, s with
    | true, 0 => 2    -- carry, rain
    | true, 1 => -1   -- carry, no rain
    | false, 0 => -2  -- don't carry, rain
    | false, 1 => 0 }  -- don't carry, no rain

/-! ## Stochastic Instance -/

/-- Umbrella with weather forecast distribution -/
def umbrellaStochastic : StochasticDecisionProblem Bool (Fin 2) :=
  { toDecisionProblem := umbrellaStatic
    distribution := fun s =>
      match s with
      | 0 => 0.3  -- rain probability
      | 1 => 0.7 } -- no rain probability

/-- Expected utility of carrying -/
theorem umbrella_expected_carry :
    stochasticExpectedUtility umbrellaStochastic true = -0.1 := by
  simp [stochasticExpectedUtility, umbrellaStochastic, umbrellaStatic]
  norm_num

/-! ## Sequential Instance -/

/-- Multi-stage gambler problem -/
def gamblerSequential (goal : ℕ) : SequentialDecisionProblem Bool (Fin (goal + 1)) String :=
  { toDecisionProblem :=
    { utility := fun a s =>
        if a ∧ s + 1 = goal then 1 else 0 }
    transition := fun a s => Distribution.uniform (Fin (goal + 1))
    observation := fun s => Distribution.delta (toString s)
    horizon := 10 }

/-! ## Product Distribution Instance -/

/-- Independent coin flips -/
def coinFlips (n : ℕ) : StochasticDecisionProblem Unit (Fin (2^n)) :=
  { toDecisionProblem := 
    { utility := fun _ _ => 1 }
    distribution := fun _ => 1 / (2^n : ℝ) }

/-- Coin flips have product distribution -/
theorem coinFlips_product (n : ℕ) : isProductDistribution (coinFlips n).distribution := by
  unfold isProductDistribution coinFlips
  use fun _ => fun _ => 1 / (2^n : ℝ)
  intro s
  have h : 1 / (2^n : ℝ) = ∏ _i : Fin n, 1 / (2^n : ℝ) := by
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    simp [Finset.prod_const, Finset.card_univ, hcard]
    ring
  exact h.symm

/-! ## Fully Observable MDP Instance -/

/-- Simple inventory MDP -/
def inventoryMDP (capacity : ℕ) : SequentialDecisionProblem (Fin 2) (Fin capacity) Unit :=
  { toDecisionProblem :=
    { utility := fun a s =>
        if a = 0 then -(s : ℝ) else (s : ℝ) }
    transition := fun a s => Distribution.uniform (Fin capacity)
    observation := fun _ => Distribution.delta ()
    horizon := 5 }

/-- Inventory MDP is fully observable -/
theorem inventoryMDP_fully_observable : 
    ∀ s, ∃ o, (inventoryMDP capacity).observation s = Distribution.delta o := by
  intro s
  exact ⟨(), rfl⟩

end Paper4bStochasticSequential
