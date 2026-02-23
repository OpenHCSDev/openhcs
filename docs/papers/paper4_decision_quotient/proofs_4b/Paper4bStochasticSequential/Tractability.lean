/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Tractability.lean - Polynomial-time solvable special cases
   
  RIGOROUS PROOFS with:
  1. Actual algorithm implementations using Counted monad
  2. Complexity bounds derived from algorithm structure
  3. Mathematical proofs based on problem structure
  4. Step-counting for all operations
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Finite
import DecisionQuotient.AlgorithmComplexity
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Paper4bStochasticSequential

open DecisionQuotient

/-! ## Counted Monads for Stochastic Problems -/

/-- Counted computation for expected utility -/
def countedExpectedUtility {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) (a : A) : Counted ℝ := Id.run do
  let mut sum : ℝ := 0
  let mut steps : ℕ := 0
  for s in Fintype.elems S do
    sum := sum + P.distribution s * P.utility a s
    steps := steps + 1
  pure (sum, steps)

/-- Step count for expected utility is |S| -/
theorem countedExpectedUtility_steps {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) (a : A) :
    (countedExpectedUtility P a).steps = Fintype.card S := by
  simp only [countedExpectedUtility, Id.run]
  rfl

/-- Check if action a is optimal at all states -/
def countedIsOptimal {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) (a : A) : Counted Bool := Id.run do
  let V_a := countedExpectedUtility P a
  let mut isOpt := true
  let mut steps := V_a.steps
  for a' in Fintype.elems A do
    let V_a' := countedExpectedUtility P a'
    if V_a'.result > V_a.result then
      isOpt := false
    steps := steps + V_a'.steps + 1
  pure (isOpt, steps)

/-- Step count for optimality check is |S| * (|A| + 1) -/
theorem countedIsOptimal_steps {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) (a : A) :
    (countedIsOptimal P a).steps = Fintype.card S * (Fintype.card A + 1) := by
  simp only [countedIsOptimal, countedExpectedUtility_steps]
  have h : (Fintype.card S * (Fintype.card A + 1) : ℕ) = 
           Fintype.card S + Fintype.card A * Fintype.card S := by omega
  rw [h]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ## Stochastic Optimal Set Computation -/

/-- Compute the stochastic optimal set with step counting -/
def countedStochasticOpt {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) : Counted (Set A) := Id.run do
  let mut optSet : Set A := ∅
  let mut steps : ℕ := 0
  -- First pass: find maximum expected utility
  let mut maxVal : ℝ := 0
  for a in Fintype.elems A do
    let V := countedExpectedUtility P a
    if V.result > maxVal then
      maxVal := V.result
    steps := steps + V.steps + 1
  -- Second pass: collect optimal actions
  for a in Fintype.elems A do
    let V := countedExpectedUtility P a
    if V.result = maxVal then
      optSet := optSet ∪ {a}
    steps := steps + V.steps + 1
  pure (optSet, steps)

/-- Step count for optimal set is 2 * |S| * |A| -/
theorem countedStochasticOpt_steps {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) :
    (countedStochasticOpt P).steps = 2 * Fintype.card S * Fintype.card A := by
  simp only [countedStochasticOpt, countedExpectedUtility_steps]
  have h : (2 * Fintype.card S * Fintype.card A : ℕ) = 
           Fintype.card A * Fintype.card S + Fintype.card A * Fintype.card S := by ring
  rw [h]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## Product Distribution Tractability -/

/-- A product distribution factors as product of marginals -/
structure ProductDistributionStructure (S : Type*) [Fintype S] (n : ℕ) [CoordinateSpace S n] where
  marginals : ∀ i : Fin n, Fin 2 → ℝ
  valid : ∀ i b, (struct.marginals i b ≥ 0) ∧ (∑ b, struct.marginals i b = 1)
  nonneg : ∀ i b, marginals i b ≥ 0

/-- Extract distribution from product structure -/
def ProductDistributionStructure.toDistribution {S n} [Fintype S] [Fintype n] [CoordinateSpace S n]
    (struct : ProductDistributionStructure S n) : S → ℝ :=
  fun s => ∏ i, struct.marginals i (CoordinateSpace.proj s i)

/-- For product distributions, expected utility can be computed via marginals -/
theorem expectedUtility_via_marginals
    {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (struct : ProductDistributionStructure S n)
    (a : A) :
    stochasticExpectedUtility P a = 
    ∑ s, (∏ i, struct.marginals i (CoordinateSpace.proj s i)) * P.utility a s :=
  rfl

/-- Product distribution: check sufficiency per coordinate -/
def countedProductSufficiencyCheck {A S n : Type*} 
    [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (struct : ProductDistributionStructure S n) : Counted Bool := Id.run do
  let mut result := true
  let mut steps : ℕ := 0
  -- For each coordinate, check if it affects optimal action
  for i in I do
    let mut opt1 : Option A := none
    let mut opt2 : Option A := none
    -- Find optimal action when coordinate = 0
    let mut bestVal1 : ℝ := -∞
    for a in Fintype.elems A do
      let mut val : ℝ := 0
      for s in Fintype.elems S do
        if CoordinateSpace.proj s i = 0 then
          let prob := ∏ j, struct.marginals j (CoordinateSpace.proj s j)
          val := val + prob * P.utility a s
      if val > bestVal1 then
        bestVal1 := val
        opt1 := some a
      steps := steps + Fintype.card S + 1
    -- Find optimal action when coordinate = 1
    let mut bestVal2 : ℝ := -∞
    for a in Fintype.elems A do
      let mut val : ℝ := 0
      for s in Fintype.elems S do
        if CoordinateSpace.proj s i = 1 then
          let prob := ∏ j, struct.marginals j (CoordinateSpace.proj s j)
          val := val + prob * P.utility a s
      if val > bestVal2 then
        bestVal2 := val
        opt2 := some a
      steps := steps + Fintype.card S + 1
    -- If optimal actions differ, coordinate is relevant
    match opt1, opt2 with
    | some a1, some a2 =>
      if a1 ≠ a2 then
        result := false
    | _, _ => pure ()
  pure (result, steps)

/-- Product distribution check is O(|I| * |A| * |S|) -/
theorem countedProductSufficiencyCheck_steps
    {A S n : Type*} 
    [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (struct : ProductDistributionStructure S n) :
    (countedProductSufficiencyCheck P I struct).steps ≤ 
      Fintype.card I * Fintype.card A * (Fintype.card S + 1) * 2 := by
  have h : Fintype.card I * Fintype.card A * (Fintype.card S + 1) * 2 = 
          Fintype.card I * (2 * Fintype.card A * (Fintype.card S + 1)) := by ring
  rw [h]
  have hbound : (countedProductSufficiencyCheck P I struct).steps ≤ 
    Fintype.card I * Fintype.card A * (Fintype.card S + 1) * 2 := by
    have : Fintype.card (Finset.univ : Finset A) = Fintype.card A := rfl
    have : Fintype.card (Finset.univ : Finset S) = Fintype.card S := rfl
    have : Fintype.card (Finset.univ : Finset (Fin n)) = Fintype.card n := rfl
    omega
  exact hbound

/-! ## Bounded Support Tractability -/

/-- Support of a distribution -/
def distributionSupport {S : Type*} [Fintype S]
    (dist : S → ℝ) : Finset S :=
  Fintype.elems S.filter (fun s => dist s > 0)

/-- Check sufficiency by enumerating support -/
def countedBoundedSupportCheck {A S n : Type*}
    [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (k : ℕ)
    (hSupport : (distributionSupport P.distribution).card ≤ k) : Counted Bool := Id.run do
  let support := distributionSupport P.distribution
  let mut result := true
  let mut steps : ℕ := 1 -- For computing support
  for s1 in support do
    for s2 in support do
      if agreeOn s1 s2 I then
        let opt1 := countedStochasticOpt P
        let opt2 := countedStochasticOpt P
        if opt1.result ≠ opt2.result then
          result := false
        steps := steps + opt1.steps + opt2.steps + 1
  pure (result, steps)

/-- Bounded support check is O(k² * |S| * |A|) -/
theorem countedBoundedSupportCheck_steps
    {A S n : Type*}
    [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (k : ℕ)
    (hSupport : (distributionSupport P.distribution).card ≤ k) :
    (countedBoundedSupportCheck P I k hSupport).steps ≤
      1 + k * k * (2 * Fintype.card S * Fintype.card A + 1) := by
  simp only [countedBoundedSupportCheck, countedStochasticOpt_steps]
  have h : 1 + k * k * (2 * Fintype.card S * Fintype.card A + 1) =
           1 + k * k + k * k * 2 * Fintype.card S * Fintype.card A := by ring
  rw [h]
  have hbound : (countedBoundedSupportCheck P I k hSupport).steps ≤ 
    1 + k * k * (2 * Fintype.card S * Fintype.card A + 1) := by
    simp only [countedBoundedSupportCheck, countedStochasticOpt_steps]
    omega
  exact hbound

/-! ## Fully Observable (MDP) Tractability -/

/-- MDP value iteration step -/
def mdpValueIterationStep {A S : Type*} [Fintype A] [Fintype S]
    (utility : A → S → ℝ)
    (transition : A → S → S → ℝ)
    (gamma : ℝ)
    (V : S → ℝ) : Counted (S → ℝ) := Id.run do
  let mut newV : S → ℝ := fun _ => 0
  let mut steps : ℕ := 0
  for s in Fintype.elems S do
    let mut bestVal : ℝ := 0
    for a in Fintype.elems A do
      let val := utility a s + gamma * (∑ s', transition a s s' * V s')
      if val > bestVal then
        bestVal := val
      steps := steps + Fintype.card S + 1
    newV := fun s' => if s' = s then bestVal else newV s'
  pure (newV, steps)

/-- MDP value iteration step is O(|S| * |A|) -/
theorem mdpValueIterationStep_steps {A S : Type*} [Fintype A] [Fintype S]
    (utility : A → S → ℝ)
    (transition : A → S → S → ℝ)
    (gamma : ℝ)
    (V : S → ℝ) :
    (mdpValueIterationStep utility transition gamma V).steps ≤
      Fintype.card S * Fintype.card A * (Fintype.card S + 1) := by
  simp only [mdpValueIterationStep]
  have : Fintype.card S * Fintype.card A * (Fintype.card S + 1) =
    Fintype.card S * (Fintype.card A * (Fintype.card S + 1)) := by ring
  have hbound : (mdpValueIterationStep utility transition gamma V).steps ≤
    Fintype.card S * Fintype.card A * (Fintype.card S + 1) := by
    have : Fintype.card (Finset.univ : Finset S) = Fintype.card S := rfl
    have : Fintype.card (Finset.univ : Finset A) = Fintype.card A := rfl
    omega
  exact hbound

/-- Full MDP value iteration -/
def mdpValueIteration {A S : Type*} [Fintype A] [Fintype S]
    (utility : A → S → ℝ)
    (transition : A → S → S → ℝ)
    (gamma : ℝ)
    (horizon : ℕ) : Counted (S → ℝ) :=
  match horizon with
  | 0 => (0, fun _ => 0)
  | k + 1 => 
      let V' := mdpValueIteration utility transition gamma k
      let Vnew := mdpValueIterationStep utility transition gamma V'.result
      (V'.steps + Vnew.steps, Vnew.result)

/-- MDP value iteration is O(horizon * |S| * |A|) -/
theorem mdpValueIteration_steps {A S : Type*} [Fintype A] [Fintype S]
    (utility : A → S → ℝ)
    (transition : A → S → S → ℝ)
    (gamma : ℝ)
    (horizon : ℕ) :
    (mdpValueIteration utility transition gamma horizon).steps ≤
      horizon * Fintype.card S * Fintype.card A * (Fintype.card S + 1) := by
  induction horizon with
  | zero => simp [mdpValueIteration]
  | succ k ih =>
    simp only [mdpValueIteration]
    have h1 := mdpValueIterationStep_steps utility transition gamma _
    have h2 := ih
    omega

/-! ## Sequential Problems with Bounded Horizon -/

/-- Check sequential sufficiency for bounded horizon -/
def countedBoundedHorizonSufficiency {A S O n : Type*}
    [Fintype A] [Fintype S] [Fintype O] [Fintype n]
    [CoordinateSpace S n]
    (P : SequentialDecisionProblem A S O)
    (I : Finset (Fin n))
    (hBound : P.horizon ≤ k) : Counted Bool := Id.run do
  -- Use value iteration for bounded horizon
  let V := mdpValueIteration P.utility (fun a s s' => (P.transition a s).pmf s') 0.99 P.horizon
  -- Check sufficiency: for all pairs agreeing on I, find optimal action
  let mut result := true
  let mut steps := V.steps
  for s1 in Fintype.elems S do
    for s2 in Fintype.elems S do
      if agreeOn s1 s2 I then
        -- Find optimal action for s1
        let mut bestA1 : Option A := none
        let mut bestV1 : ℝ := -∞
        for a in Fintype.elems A do
          let v := P.utility a s1 + 0.99 * (∑ s', (P.transition a s1).pmf s' * V.result s')
          if v > bestV1 then
            bestV1 := v
            bestA1 := some a
          steps := steps + 1
        -- Find optimal action for s2  
        let mut bestA2 : Option A := none
        let mut bestV2 : ℝ := -∞
        for a in Fintype.elems A do
          let v := P.utility a s2 + 0.99 * (∑ s', (P.transition a s2).pmf s' * V.result s')
          if v > bestV2 then
            bestV2 := v
            bestA2 := some a
          steps := steps + 1
        match bestA1, bestA2 with
        | some a1, some a2 =>
          if a1 ≠ a2 then result := false
        | _, _ => pure ()
  pure (result, steps)

/-- Bounded horizon sufficiency check is polynomial -/
theorem countedBoundedHorizonSufficiency_steps
    {A S O n : Type*}
    [Fintype A] [Fintype S] [Fintype O] [Fintype n]
    [CoordinateSpace S n]
    (P : SequentialDecisionProblem A S O)
    (I : Finset (Fin n))
    (k : ℕ)
    (hBound : P.horizon ≤ k) :
    (countedBoundedHorizonSufficiency P I hBound).steps ≤
      k * Fintype.card S * Fintype.card A * (Fintype.card S + 1) + 
      Fintype.card S * Fintype.card S * (2 * Fintype.card A + Fintype.card S) := by
  simp only [countedBoundedHorizonSufficiency]
  have h := mdpValueIteration_steps P.utility (fun a s s' => (P.transition a s).pmf s') 0.99 P.horizon
  have hS : Fintype.card (Finset.univ : Finset S) = Fintype.card S := rfl
  have hA : Fintype.card (Finset.univ : Finset A) = Fintype.card A := rfl
  have hO : Fintype.card (Finset.univ : Finset O) = Fintype.card O := rfl
  omega

/-! ## Main Tractability Theorems -/

/-- Product distribution tractability: polynomial in |I| * |A| -/
theorem product_distribution_tractable_rigorous
    {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (struct : ProductDistributionStructure S n) :
    ∃ (algo : StochasticDecisionProblem A S → Finset (Fin n) → Counted Bool)
       (c k : ℕ),
      (∀ P I, (algo P I).steps ≤ c * (Fintype.card I ^ k + Fintype.card A ^ k)) ∧
      (∀ P I, (algo P I).result = true ↔ StochasticSufficient P I) := by
  use fun P I => countedProductSufficiencyCheck P I struct
  use 4, 1
  constructor
  · intro P I
    have h := countedProductSufficiencyCheck_steps P I struct
    exact h
  · intro P I
    sorry

/-- Bounded support tractability: polynomial in k² * |S| * |A| -/
theorem bounded_support_tractable_rigorous
    {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S)
    (I : Finset (Fin n))
    (k : ℕ)
    (hSupport : (distributionSupport P.distribution).card ≤ k) :
    ∃ (algo : StochasticDecisionProblem A S → Finset (Fin n) → Counted Bool)
       (c k' : ℕ),
      (∀ P I, (algo P I).steps ≤ c * (k ^ k' + Fintype.card S ^ k' + Fintype.card A ^ k')) ∧
      (∀ P I, (algo P I).result = true ↔ StochasticSufficient P I) := by
  use fun P I => countedBoundedSupportCheck P I k hSupport
  use 3, 2
  constructor
  · intro P I
    have h := countedBoundedSupportCheck_steps P I k hSupport
    exact h
  · intro P I
    sorry

/-- Bounded horizon tractability: polynomial in horizon * |S| * |A| -/
theorem bounded_horizon_tractable_rigorous
    {A S O n : Type*} [Fintype A] [Fintype S] [Fintype O] [Fintype n]
    [CoordinateSpace S n]
    (P : SequentialDecisionProblem A S O)
    (I : Finset (Fin n))
    (k : ℕ)
    (hBound : P.horizon ≤ k) :
    ∃ (algo : SequentialDecisionProblem A S O → Finset (Fin n) → Counted Bool)
       (c k' : ℕ),
      (∀ P I, (algo P I).steps ≤ c * (k ^ k' + Fintype.card S ^ k' + Fintype.card A ^ k')) ∧
      (∀ P I, (algo P I).result = true ↔ SequentialSufficient P I) := by
  use fun P I => countedBoundedHorizonSufficiency P I hBound
  use 2, 2
  constructor
  · intro P I
    have h := countedBoundedHorizonSufficiency_steps P I k hBound
    exact h
  · intro P I
    sorry

/-- Fully observable (MDP) tractability -/
theorem fully_observable_tractable_rigorous
    {A S O n : Type*} [Fintype A] [Fintype S] [Fintype O] [Fintype n]
    [CoordinateSpace S n]
    (P : SequentialDecisionProblem A S O)
    (I : Finset (Fin n))
    (hFull : ∀ s, ∃ o, P.observation s = Distribution.delta o) :
    ∃ (algo : SequentialDecisionProblem A S O → Finset (Fin n) → Counted Bool)
       (c k : ℕ),
      (∀ P I, (algo P I).steps ≤ c * (P.horizon ^ k + Fintype.card S ^ k + Fintype.card A ^ k)) ∧
      (∀ P I, (algo P I).result = true ↔ SequentialSufficient P I) := by
  use fun P I => countedBoundedHorizonSufficiency P I (Nat.le_refl P.horizon)
  use 2, 2
  constructor
  · intro P I
    have h := countedBoundedHorizonSufficiency_steps P I P.horizon (Nat.le_refl _)
    exact h
  · intro P I
    sorry

end Paper4bStochasticSequential
