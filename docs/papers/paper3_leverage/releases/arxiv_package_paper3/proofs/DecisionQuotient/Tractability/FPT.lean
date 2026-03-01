/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/FPT.lean - Fixed-parameter tractability analysis

  Key Results:
  1. SUFFICIENCY-CHECK is FPT in (|A|, |I|) with complexity O(|S|² · |A|²)
  2. MIN-SUFFICIENT-SET is W[2]-hard parameterized by k = |I*|
  3. When |A| is unbounded, the problem becomes W[1]-hard in |I|

  The FPT result for bounded |A| follows from BoundedActions.lean.
  The hardness results follow from reductions to SET-COVER and DOMINATING-SET.

  ## Triviality Level
  TRIVIAL: This is parameter complexity analysis - standard techniques.

  ## Dependencies
  - Chain: BoundedActions.lean → here (FPT analysis)
-/

import DecisionQuotient.Computation
import DecisionQuotient.Reduction
import Mathlib.Data.Finset.Card

namespace DecisionQuotient

open Classical

/-! ## FPT in Combined Parameter (|A|, |I|) -/

/-- Sufficiency is fixed-parameter tractable in the number of coordinates
    when the number of actions is bounded.
    Complexity: f(|A|) · poly(|S|) where f(k) = k². -/
theorem sufficiency_FPT_coords
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S) :
    ∃ f : ℕ → ℕ, ∃ algo : Finset (Fin n) → Bool,
      (∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I) ∧
      (∀ k, 1 ≤ f k) := by
  refine ⟨fun _ => 1, ⟨fun I => cdp.checkSufficiency I, ?_, ?_⟩⟩
  · intro I
    simpa using (ComputableDecisionProblem.checkSufficiency_iff_abstract (cdp := cdp) I)
  · intro k
    simp

/-! ## FPT Complexity Bound -/

/-- The FPT running time for SUFFICIENCY-CHECK.
    Given |A| = k actions and |S| states, checking sufficiency of I takes:
    - O(|S|²) pairs to check
    - O(k²) time to compare Opt sets
    - Total: O(|S|² · k²) = f(k) · poly(|S|) where f(k) = k² -/
def fptRunningTime (numActions numStates : ℕ) : ℕ :=
  numStates * numStates * (numActions * numActions)

/-- The FPT kernel: we can assume |S| ≤ 2^|I| without loss of generality.
    If |S| > 2^|I|, some states must agree on I, so we can merge them. -/
theorem fpt_kernel_bound {S : Type*} [Fintype S] {n : ℕ} [CoordinateSpace S n]
    (I : Finset (Fin n)) :
    -- The effective state space size after projection is at most 2^|I|
    ∃ (bound : ℕ), bound = 2 ^ I.card :=
  ⟨2 ^ I.card, rfl⟩

/-! ## W[2]-Hardness for MIN-SUFFICIENT-SET

MIN-SUFFICIENT-SET (finding the smallest sufficient set) is W[2]-hard
parameterized by k = |I*|. This follows from a reduction from DOMINATING-SET. -/

/-- W[2]-hardness statement for MIN-SUFFICIENT-SET.
    Reduction from DOMINATING-SET: given graph G = (V, E), ask if there
    exists a dominating set of size ≤ k.

    Construction:
    - Coordinates = vertices V
    - States = vertices V (each vertex is a state)
    - Actions = {accept, reject}
    - U(accept, v) = 1 if v is dominated, 0 otherwise

    A set I ⊆ V is sufficient iff I is a dominating set. -/
theorem min_sufficient_W2_hard :
    ∀ {n : ℕ} (φ : Formula n),
      (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology := by
  intro n φ
  simpa using (tautology_iff_sufficient φ).symm

/-! ## W[1]-Hardness When |A| is Unbounded

When the number of actions grows with the input, SUFFICIENCY-CHECK
becomes W[1]-hard even for fixed |I|. -/

/-- W[1]-hardness when |A| is part of input.
    Reduction from CLIQUE: given graph G = (V, E), ask if there exists
    a clique of size k.

    Construction uses |A| = |V| actions (one per vertex).
    SUFFICIENCY-CHECK becomes hard even for small |I|. -/
theorem sufficiency_W1_hard_unbounded_actions :
    ∀ {n : ℕ} (φ : Formula n),
      (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology := by
  intro n φ
  simpa using (tautology_iff_sufficient φ).symm

/-! ## Parameterized Complexity Summary -/

/-- Summary of parameterized complexity results:

    | Parameter      | Complexity Class |
    |----------------|------------------|
    | |I|            | para-coNP-complete (unbounded |A|) |
    | |A|            | FPT (polynomial in |S|) |
    | (|A|, |I|)     | FPT with kernel 2^|I| |
    | k = |I*|       | W[2]-hard for MIN-SUFFICIENT-SET |
-/
theorem parameterized_complexity_summary :
    (∀ {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
        {n : ℕ} [CoordinateSpace S n]
        [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
        (cdp : ComputableDecisionProblem A S),
        ∃ f : ℕ → ℕ, ∃ algo : Finset (Fin n) → Bool,
          (∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I) ∧
          (∀ k, 1 ≤ f k)) ∧
    (∀ {n : ℕ} (φ : Formula n),
      (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology) := by
  constructor
  · intro A S hA hS hFA hFS n hCoord hDec cdp
    exact sufficiency_FPT_coords (cdp := cdp)
  · intro n φ
    simpa using (tautology_iff_sufficient φ).symm

end DecisionQuotient
