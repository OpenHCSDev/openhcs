/-
  Paper 4: Decision-Relevant Uncertainty

  Finite.lean - Finite Decision Problems and the Decision Quotient

  This module follows the foundation laid out in `IMPLEMENTATION_PLAN.md`
  (Part 2). It introduces a concrete, finite representation of decision
  problems using `Finset`s, plus computable notions of optimal actions,
  sufficiency, and the decision quotient metric.
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Init

namespace DecisionQuotient

open Classical

variable {A S : Type*}

/-- A decision problem with explicitly finite actions and states. -/
structure FiniteDecisionProblem where
  /-- Finite set of actions (alternatives). -/
  actions : Finset A
  /-- Finite set of states. -/
  states : Finset S
  /-- Utility function on actions and states (ℤ for convenient arithmetic). -/
  utility : A → S → ℤ

namespace FiniteDecisionProblem

/-- Forget the finiteness witness and view the problem as an abstract one. -/
def toDecisionProblem (dp : FiniteDecisionProblem (A := A) (S := S)) :
    DecisionProblem A S :=
  { utility := fun a s => dp.utility a s }

/-- The set of actions that maximize utility at state `s` within `dp.actions`. -/
def optimalActions (dp : FiniteDecisionProblem (A := A) (S := S)) (s : S) : Finset A :=
  dp.actions.filter (fun a => ∀ a' ∈ dp.actions, dp.utility a' s ≤ dp.utility a s)

/-- Characterization of membership in `optimalActions`. -/
theorem mem_optimalActions_iff (dp : FiniteDecisionProblem (A := A) (S := S))
    [DecidableEq A] [DecidableEq S]
    {s : S} {a : A} :
    a ∈ dp.optimalActions s ↔
      a ∈ dp.actions ∧ ∀ a' ∈ dp.actions, dp.utility a' s ≤ dp.utility a s := by
  unfold optimalActions
  simp

/-- `optimalActions` is always a subset of the available actions. -/
theorem optimalActions_subset_actions (dp : FiniteDecisionProblem (A := A) (S := S))
    [DecidableEq A] [DecidableEq S]
    (s : S) :
    dp.optimalActions s ⊆ dp.actions := by
  intro a ha
  have h := (FiniteDecisionProblem.mem_optimalActions_iff (dp := dp) (s := s) (a := a)).1 ha
  exact h.1

/- Decision quotient: fraction of actions that are optimal for at least one state
    in the provided state set (defaults to `dp.states`). If there are no actions,
    the quotient is defined to be `0` to avoid division by zero. -/
noncomputable def decisionQuotient (dp : FiniteDecisionProblem (A := A) (S := S))
    (states : Finset S := dp.states) : ℚ :=
  let optCover : Finset A := states.biUnion (fun s => dp.optimalActions s)
  if _ : dp.actions.card = 0 then 0
  else (optCover.card : ℚ) / (dp.actions.card : ℚ)

variable {n : ℕ} [CoordinateSpace S n]

/-- A coordinate set `I` is sufficient (finite version): for every pair of states
    that agree on coordinates in `I`, the optimal action set coincides. The check
    is restricted to the finite state set carried by `dp`. -/
def isSufficient (dp : FiniteDecisionProblem (A := A) (S := S)) (I : Finset (Fin n)) : Prop :=
  ∀ s ∈ dp.states, ∀ s' ∈ dp.states, agreeOn s s' I → dp.optimalActions s = dp.optimalActions s'

/-- Sufficiency respects supersets of coordinates (monotonicity). -/
theorem isSufficient_superset (dp : FiniteDecisionProblem (A := A) (S := S))
    [DecidableEq A] [DecidableEq S]
    {I J : Finset (Fin n)} (hI : dp.isSufficient I) (hIJ : I ⊆ J) :
    dp.isSufficient J := by
  intro s hs s' hs' hagree
  apply hI s hs s' hs'
  intro i hi
  exact hagree i (hIJ hi)

end FiniteDecisionProblem

end DecisionQuotient
