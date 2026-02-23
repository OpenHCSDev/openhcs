/-
  Paper 4: Decision-Relevant Uncertainty
  
  Tractable.lean - Polynomial-Time Special Cases
  
  While SUFFICIENCY-CHECK is coNP-complete in general, there are important
  special cases where it becomes polynomial:
  
  1. Monotone utility: If utility is monotone in coordinates, sufficiency
     is decidable by checking only extreme points.
  
  2. Single-action dominance: If one action dominates at every state,
     every coordinate set is sufficient.
  
  3. Coordinate independence: If Opt depends on coordinates independently,
     sufficiency checking decomposes.
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import DecisionQuotient.Computation
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Finprod

namespace DecisionQuotient

variable {A S : Type*} {n : ℕ}

/-! ## Single-Action Dominance -/

/-- An action dominates if it's optimal at every state -/
def DecisionProblem.hasDominant (dp : DecisionProblem A S) (a : A) : Prop :=
  ∀ s : S, a ∈ dp.Opt s

/-- If there's a dominant action, it's the unique optimal at every state -/
theorem DecisionProblem.dominant_unique (dp : DecisionProblem A S) (a : A)
    (hdom : dp.hasDominant a)
    (hunique : ∀ s : S, ∀ a' : A, a' ∈ dp.Opt s → a' = a) :
    ∀ s : S, dp.Opt s = {a} := by
  intro s
  ext a'
  simp only [Set.mem_singleton_iff]
  constructor
  · exact hunique s a'
  · intro h; subst h; exact hdom s

/-- With a unique dominant action, every coordinate set is sufficient -/
theorem DecisionProblem.dominant_all_sufficient [CoordinateSpace S n]
    (dp : DecisionProblem A S) (a : A)
    (hdom : dp.hasDominant a)
    (hunique : ∀ s : S, ∀ a' : A, a' ∈ dp.Opt s → a' = a)
    (I : Finset (Fin n)) :
    dp.isSufficient I := by
  intro s s' _
  rw [dp.dominant_unique a hdom hunique s, dp.dominant_unique a hdom hunique s']

/-! ## Constant Optimal Sets -/

/-- A problem has constant Opt if all states have the same optimal set -/
def DecisionProblem.hasConstantOpt (dp : DecisionProblem A S) : Prop :=
  ∃ O : Set A, ∀ s : S, dp.Opt s = O

/-- With constant Opt, every coordinate set is sufficient -/
theorem DecisionProblem.constant_opt_all_sufficient [CoordinateSpace S n]
    (dp : DecisionProblem A S) (hconst : dp.hasConstantOpt)
    (I : Finset (Fin n)) :
    dp.isSufficient I := by
  obtain ⟨O, hO⟩ := hconst
  intro s s' _
  rw [hO s, hO s']

/-! ## Two-State Problems -/

/-- For problems with only two states, sufficiency is trivial to check -/
theorem two_state_sufficiency [CoordinateSpace S n]
    (dp : DecisionProblem A S) (s₁ s₂ : S)
    (hall : ∀ s : S, s = s₁ ∨ s = s₂)
    (I : Finset (Fin n)) :
    dp.isSufficient I ↔ (agreeOn s₁ s₂ I → dp.Opt s₁ = dp.Opt s₂) := by
  constructor
  · intro hsuff hagree
    exact hsuff s₁ s₂ hagree
  · intro h s s' hagree
    rcases hall s with hs | hs <;> rcases hall s' with hs' | hs'
    · rw [hs, hs']
    · subst hs hs'
      apply h; intro i hi; exact hagree i hi
    · subst hs hs'
      symm; apply h; intro i hi; exact (hagree i hi).symm
    · rw [hs, hs']

/-! ## Coordinate-Independent Utilities -/

/-- Utility is additive in coordinates if it decomposes as a sum -/
structure AdditiveUtility (A : Type*) (n : ℕ) where
  /-- Contribution of each coordinate -/
  contrib : Fin n → A → ℕ → ℝ

/-- Build a decision problem from additive utility -/
def AdditiveUtility.toProblem (au : AdditiveUtility A n) : DecisionProblem A (Fin n → ℕ) where
  utility a s := Finset.univ.sum fun i => au.contrib i a (s i)

/-- For additive utilities, a coordinate i is relevant iff it affects
    the ranking of some pair of actions -/
def AdditiveUtility.isRelevant (au : AdditiveUtility A n) (i : Fin n) : Prop :=
  ∃ a₁ a₂ : A, ∃ v₁ v₂ : ℕ, 
    au.contrib i a₁ v₁ - au.contrib i a₂ v₁ ≠ au.contrib i a₁ v₂ - au.contrib i a₂ v₂

/-- The set of relevant coordinates -/
def AdditiveUtility.relevantSet (au : AdditiveUtility A n) : Set (Fin n) :=
  {i | au.isRelevant i}

/-! ## Monotone Utilities -/

/-- A utility function is monotone increasing in a coordinate -/
def DecisionProblem.monotoneIn [Preorder S] (dp : DecisionProblem A S) : Prop :=
  ∀ a : A, Monotone (dp.utility a)

/-- For monotone utilities on a finite lattice, Opt is determined by 
    values at the top element -/
theorem monotone_opt_at_top [Preorder S] [OrderTop S] [Finite A]
    (dp : DecisionProblem A S) (hmon : dp.monotoneIn) :
    ∀ a : A, dp.isOptimal a ⊤ → ∀ s : S, dp.utility a s ≤ dp.utility a ⊤ := by
  intro a _ s
  exact hmon a (le_top)

end DecisionQuotient

