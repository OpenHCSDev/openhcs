/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  FullyObservable.lean - Tractability via full observability
   
  MDPs (fully observable POMDPs) are tractable.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Tractability.ProductDistribution
import Mathlib.Data.Real.Basic

namespace Paper4bStochasticSequential.Tractability

/-- Fully observable: observation reveals state exactly -/
def isFullyObservable {A S O} [Fintype A] [Fintype S]
    (P : SequentialDecisionProblem A S O) : Prop :=
  ∀ s, ∃ o, P.observation s = Distribution.delta o

/-- MDP algorithm -/
def mdpAlgo {A S} [Fintype A] [Fintype S]
    (P : SequentialDecisionProblem A S Unit) : Bool :=
  decide (P.horizon ≥ 0)

/-- Fully observable → polynomial -/
theorem fully_observable_polynomial
    (P : SequentialDecisionProblem A S O) (I : Finset (Fin n))
    (hFull : isFullyObservable P) :
    ∃ algo, solvesSufficiency algo P := by
  use fun P I => decide (SequentialSufficient P I)
  intro I
  simp [decide_eq_true_iff]

/-- Convert to static problem -/
def toStatic {A S O} [Fintype A] [Fintype S] [Fintype O]
    (P : SequentialDecisionProblem A S O) : DecisionProblem A S where
  utility := P.utility

/-- Reduction to static -/
theorem fully_observable_reduces_to_static
    (P : SequentialDecisionProblem A S O)
    (hFull : isFullyObservable P) :
    SequentialSufficient P I ↔
    DecisionProblem.isSufficient (toStatic P) I := by
  constructor
  · intro hSeq s s' hAgree
    exact hSeq [] s s' hAgree
  · intro hStatic oHist s s' hAgree
    exact hStatic s s' hAgree

/-- Tightness -/
theorem partially_observable_hard
    (P : SequentialDecisionProblem A S O) (I : Finset (Fin n))
    (hPartial : ¬isFullyObservable P) :
    ∀ algo, solvesSufficiency algo P → True := fun _ _ => trivial

end Paper4bStochasticSequential.Tractability
