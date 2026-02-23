/-
  Paper 4: Decision-Relevant Uncertainty

  Computation.lean - Decidable Predicates and Algorithms

  This file provides the computational layer that connects the abstract
  theory to actual algorithms. We show:

  1. With finite types and decidable equality, we CAN compute optimal sets
  2. Decision equivalence becomes decidable
  3. Sufficiency checking is implementable (but expensive - coNP)
  4. The complexity results from Hardness.lean are reflected in algorithm structure
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order

namespace DecisionQuotient

/-! ## Computable Decision Problems -/

/-- A computable decision problem has finite action and state spaces
    with decidable equality and a computable utility function.
    Uses ℚ instead of ℝ for computability. -/
structure ComputableDecisionProblem (A S : Type*)
    [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S] where
  /-- Utility function (computable over rationals) -/
  utility : A → S → ℚ

variable {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]

/-- Convert a computable decision problem to an abstract one -/
def ComputableDecisionProblem.toAbstract (cdp : ComputableDecisionProblem A S) :
    DecisionProblem A S where
  utility := fun a s => cdp.utility a s

/-! ## Decidable Optimality -/

/-- Check if action a is optimal at state s (computable) -/
def ComputableDecisionProblem.isOptimalDec (cdp : ComputableDecisionProblem A S)
    (a : A) (s : S) : Bool :=
  (Finset.univ : Finset A).filter (fun a' => decide (cdp.utility a' s > cdp.utility a s)) = ∅

/-- Compute the optimal set at state s -/
def ComputableDecisionProblem.computeOpt (cdp : ComputableDecisionProblem A S)
    (s : S) : Finset A :=
  Finset.univ.filter fun a => cdp.isOptimalDec a s

/-! ## Decidable Decision Equivalence -/

/-- Check if two states are decision-equivalent (computable) -/
def ComputableDecisionProblem.decisionEquivDec (cdp : ComputableDecisionProblem A S)
    (s s' : S) : Bool :=
  cdp.computeOpt s = cdp.computeOpt s'

/-- Decision equivalence is decidable for computable problems -/
instance ComputableDecisionProblem.decisionEquivDecidable
    (cdp : ComputableDecisionProblem A S) : DecidableRel (fun s s' =>
      cdp.computeOpt s = cdp.computeOpt s') := fun s s' =>
  inferInstanceAs (Decidable (cdp.computeOpt s = cdp.computeOpt s'))

/-! ## Decidable Sufficiency (for finite coordinate spaces) -/

variable {n : ℕ} [CoordinateSpace S n]

/-- Check if coordinate set I is sufficient by exhaustive search.
    This is O(|S|²) - reflects the coNP complexity.
    We check: ∀ s s', agreeOn s s' I → computeOpt s = computeOpt s'

    We find counterexamples: pairs (s, s') that agree on I but have different Opt -/
def ComputableDecisionProblem.insufficiencyWitnesses
    (cdp : ComputableDecisionProblem A S)
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (I : Finset (Fin n)) : Finset (S × S) :=
  (Finset.univ.product Finset.univ).filter fun ⟨s, s'⟩ =>
    decide (agreeOn s s' I) && decide (cdp.computeOpt s ≠ cdp.computeOpt s')

/-- Check if I is sufficient (no counterexample exists) -/
def ComputableDecisionProblem.checkSufficiency
    (cdp : ComputableDecisionProblem A S)
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (I : Finset (Fin n)) : Bool :=
  cdp.insufficiencyWitnesses I = ∅

/-! ## Complexity Witness -/

/-- A witness for insufficiency: two states that agree on I but have different Opt.
    Finding such a witness is in NP (guess and verify in poly time).
    This shows INSUFFICIENCY ∈ NP, hence SUFFICIENCY ∈ coNP. -/
structure InsufficiencyWitness (cdp : ComputableDecisionProblem A S)
    (I : Finset (Fin n)) where
  s : S
  s' : S
  agree : agreeOn s s' I
  differ : cdp.computeOpt s ≠ cdp.computeOpt s'

/-- Verify an insufficiency witness in polynomial time -/
def ComputableDecisionProblem.verifyWitness
    (cdp : ComputableDecisionProblem A S)
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (I : Finset (Fin n)) (s s' : S) : Bool :=
  decide (agreeOn s s' I) && decide (cdp.computeOpt s ≠ cdp.computeOpt s')

/-- An insufficiency witness certifies the set is not sufficient -/
theorem InsufficiencyWitness.certifies_not_sufficient
    (cdp : ComputableDecisionProblem A S) (I : Finset (Fin n))
    (w : InsufficiencyWitness cdp I) :
    ∃ s s' : S, agreeOn s s' I ∧ cdp.computeOpt s ≠ cdp.computeOpt s' :=
  ⟨w.s, w.s', w.agree, w.differ⟩

/-! ## Correctness Characterization

These characterize what the computable layer computes -/

/-- isOptimalDec checks that no action has strictly higher utility -/
theorem ComputableDecisionProblem.isOptimalDec_iff
    (cdp : ComputableDecisionProblem A S) (a : A) (s : S) :
    cdp.isOptimalDec a s ↔ ∀ a' : A, cdp.utility a' s ≤ cdp.utility a s := by
  unfold isOptimalDec
  simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
             not_lt, decide_eq_true_eq]

/-- computeOpt returns exactly the actions with maximal utility -/
theorem ComputableDecisionProblem.mem_computeOpt_iff
    (cdp : ComputableDecisionProblem A S) (a : A) (s : S) :
    a ∈ cdp.computeOpt s ↔ ∀ a' : A, cdp.utility a' s ≤ cdp.utility a s := by
  unfold computeOpt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact cdp.isOptimalDec_iff a s

/-- decisionEquivDec checks equality of optimal sets -/
theorem ComputableDecisionProblem.decisionEquivDec_iff
    (cdp : ComputableDecisionProblem A S) (s s' : S) :
    cdp.decisionEquivDec s s' ↔ cdp.computeOpt s = cdp.computeOpt s' := by
  unfold decisionEquivDec
  simp only [decide_eq_true_eq]

/-! ## Full Correctness: Computable ↔ Abstract

These theorems prove the computable layer correctly implements
the abstract specification. The key is that ℚ ↪ ℝ preserves order. -/

/-- The computable isOptimal matches the abstract isOptimal -/
theorem ComputableDecisionProblem.isOptimalDec_iff_abstract
    (cdp : ComputableDecisionProblem A S) (a : A) (s : S) :
    cdp.isOptimalDec a s ↔ cdp.toAbstract.isOptimal a s := by
  rw [isOptimalDec_iff]
  unfold toAbstract DecisionProblem.isOptimal
  simp only [Rat.cast_le]

/-- The computable Opt matches the abstract Opt -/
theorem ComputableDecisionProblem.computeOpt_eq_abstract
    (cdp : ComputableDecisionProblem A S) (s : S) :
    ↑(cdp.computeOpt s) = cdp.toAbstract.Opt s := by
  ext a
  simp only [Finset.mem_coe]
  rw [mem_computeOpt_iff]
  unfold toAbstract DecisionProblem.Opt DecisionProblem.isOptimal
  simp only [Set.mem_setOf_eq, Rat.cast_le]

/-- The computable decision equivalence matches the abstract -/
theorem ComputableDecisionProblem.decisionEquivDec_iff_abstract
    (cdp : ComputableDecisionProblem A S) (s s' : S) :
    cdp.decisionEquivDec s s' ↔ cdp.toAbstract.DecisionEquiv s s' := by
  rw [decisionEquivDec_iff]
  unfold DecisionProblem.DecisionEquiv
  rw [← computeOpt_eq_abstract, ← computeOpt_eq_abstract]
  constructor
  · intro h; rw [h]
  · intro h; exact Finset.coe_injective h

/-- checkSufficiency correctly decides abstract sufficiency -/
theorem ComputableDecisionProblem.checkSufficiency_iff_abstract
    (cdp : ComputableDecisionProblem A S)
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (I : Finset (Fin n)) :
    cdp.checkSufficiency I ↔ cdp.toAbstract.isSufficient I := by
  unfold checkSufficiency insufficiencyWitnesses DecisionProblem.isSufficient
  simp only [Finset.filter_eq_empty_iff, Finset.mem_product, Finset.mem_univ,
             true_and, Bool.and_eq_true, decide_eq_true_eq, not_and, not_not]
  constructor
  · intro h s s' hagree
    have hmem : (s, s') ∈ (Finset.univ.product Finset.univ : Finset (S × S)) := by simp
    have := h hmem hagree
    rw [← cdp.computeOpt_eq_abstract, ← cdp.computeOpt_eq_abstract, this]
  · intro h p _ hagree
    have := h p.1 p.2 hagree
    rw [← cdp.computeOpt_eq_abstract, ← cdp.computeOpt_eq_abstract] at this
    exact Finset.coe_injective this

/-- An insufficiency witness proves the abstract set is not sufficient -/
theorem InsufficiencyWitness.not_abstract_sufficient
    (cdp : ComputableDecisionProblem A S) (I : Finset (Fin n))
    (w : InsufficiencyWitness cdp I) :
    ¬cdp.toAbstract.isSufficient I := by
  unfold DecisionProblem.isSufficient
  push_neg
  refine ⟨w.s, w.s', w.agree, ?_⟩
  rw [← cdp.computeOpt_eq_abstract, ← cdp.computeOpt_eq_abstract]
  intro h
  exact w.differ (Finset.coe_injective h)

end DecisionQuotient

