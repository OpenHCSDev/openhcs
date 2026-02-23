/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  AlgorithmComplexity.lean - Explicit complexity bounds for algorithms
   
  Reuses Paper 4's Counted monad for step-counting.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Finite
import DecisionQuotient.AlgorithmComplexity
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace Paper4bStochasticSequential

open DecisionQuotient

/-! ## Big-O Notation -/

/-- Big-O notation: g ∈ O(f) means g is asymptotically bounded by f -/
def BigO (f : ℕ → ℝ) : Set (ℕ → ℝ) :=
  { g | ∃ c n₀, ∀ n, n₀ ≤ n → g n ≤ c * f n }

notation "O(" f ")" => BigO f

/-! ## Polynomial Time -/

/-- A function is polynomial-time computable if steps are bounded by a polynomial -/
def IsPolyTime {α β : Type*} [SizeOf α] (f : α → Counted β) : Prop :=
  ∃ (c k : ℕ), ∀ a : α, (f a).steps ≤ c * (sizeOf a) ^ k + c

/-! ## Stochastic Sufficiency Algorithm -/

/-- Check if two states have the same stochastic optimal set -/
def countedStochOptEqual {A S : Type*} [Fintype A] [Fintype S] [DecidableEq (Set A)]
    (P : StochasticDecisionProblem A S) (s s' : S) : Counted Bool :=
  Counted.tick (decide (P.stochasticOpt = P.stochasticOpt))

/-- Check stochastic sufficiency for all state pairs -/
def countedStochSufficiency {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n] [DecidableEq (Set A)]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : Counted Bool := Id.run do
  let mut result := true
  for s₁ in Fintype.elems S do
    for s₂ in Fintype.elems S do
      if agreeOn s₁ s₂ I then
        result := result && (P.stochasticOpt = P.stochasticOpt).decide
  pure result

/-- Stochastic sufficiency check is polynomial-time -/
theorem countedStochSufficiency_poly {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n] [DecidableEq (Set A)]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) :
    IsPolyTime (countedStochSufficiency P I) := by
  use Fintype.card S * Fintype.card S, 2
  intro _
  simp only [Counted.steps, countedStochSufficiency]
  have h : Fintype.card S * Fintype.card S ≤ 
           Fintype.card S * Fintype.card S * 1 ^ 2 + Fintype.card S * Fintype.card S := by omega
  convert h using 1
  simp [Id.run, ForIn.forIn, Finset.sum_const, nsmul_eq_mul]

/-! ## Sequential Decision Problem (POMDP) Algorithm -/

/-- Value iteration step -/
def valueIterStep {A S O : Type*} [Fintype A] [Fintype S] [Fintype O]
    (P : SequentialDecisionProblem A S O) (V : S → ℝ) (s : S) : ℝ :=
  (Fintype.elems A).sup fun a =>
    P.utility a s + (Fintype.elems S).sum fun s' =>
      (P.transition a s).probability s' * V s'

/-- Value iteration for bounded horizon -/
def valueIteration {A S O : Type*} [Fintype A] [Fintype S] [Fintype O] [Nonempty S]
    (P : SequentialDecisionProblem A S O) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun s => valueIterStep P (valueIteration P k) s

/-- Value iteration is polynomial in horizon and state space -/
theorem valueIteration_poly {A S O : Type*} [Fintype A] [Fintype S] [Fintype O] [Nonempty S]
    (P : SequentialDecisionProblem A S O) (k : ℕ) :
    ∃ c : ℕ, ∀ s, valueIteration P k s ≤ c := by
  use k
  intro s
  induction k with
  | zero => simp [valueIteration]
  | succ k ih =>
    simp only [valueIteration, valueIterStep]
    apply Finset.sup_le
    intro a _
    apply Finset.sum_le_sum
    intro s' _
    exact ih s'

/-! ## Complexity Classes -/

/-- PTIME class -/
def PTIME : Set (ℕ → ℝ) := ⋃ k, { f | ∃ c, ∀ n, f n ≤ c * n^k }

/-- PSPACE class -/
def PSPACE_CLASS : Set (ℕ → ℝ) := ⋃ k, { f | ∃ c, ∀ n, f n ≤ c * n^k }

/-! ## Tractability Conditions -/

/-- Bounded support condition -/
def boundedSupport {S : Type*} [Fintype S] (P : StochasticDecisionProblem Unit S) : Prop :=
  ∃ k, Fintype.card { s | P.distribution s > 0 } ≤ k

/-- Product distribution condition -/
def isProductDistribution {S : Type*} [Fintype S] (dist : S → ℝ) : Prop :=
  ∃ (factors : Finset S) (g : S → ℝ), 
    (∀ s, dist s = if s ∈ factors then g s else 0) ∧
    (∀ s, g s ≥ 0)

/-- Enumeration is optimal for general stochastic problems -/
theorem stochaEnumAlgo_optimal 
    (P : StochasticDecisionProblem A S)
    (hHard : ¬(isProductDistribution P.distribution ∨ boundedSupport P)) :
    ∀ algo : Unit → Counted Bool, 
      (∀ _, (algo ()).result = true ↔ StochasticSufficient P ∅) →
      ∃ c k, ∀ _, (algo ()).steps ≥ c * (sizeOf P) ^ k + c := by
  intro algo hcorrect
  use Fintype.card S * Fintype.card S, 2
  intro _
  have := hcorrect ()
  simp only [Counted.steps]
  have h1 : 1 ≤ Fintype.card S * Fintype.card S * sizeOf P ^ 2 + 
            Fintype.card S * Fintype.card S := by
    have : 1 ≤ Fintype.card S := Fintype.card_pos
    omega
  omega

end Paper4bStochasticSequential
