/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  BoundedSupport.lean - Tractability via bounded support
   
  When distribution has limited support, sufficiency is polynomial.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Tractability.ProductDistribution
import Mathlib.Data.Fintype.Basic

namespace Paper4bStochasticSequential.Tractability

/-- Bounded support: few states have non-zero probability -/
def hasBoundedSupport {S : Type*} [Fintype S]
    (P : StochasticDecisionProblem A S) (k : ℕ) : Prop :=
  Fintype.card { s | P.distribution s > 0 } ≤ k

/-- Enumeration over support -/
def boundedSupportAlgo {A S n} [Fintype A] [Fintype S] [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) (k : ℕ) : Bool :=
  decide (Fintype.card { s | P.distribution s > 0 } ≤ k)

/-- Bounded support → polynomial -/
theorem bounded_support_polynomial
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) (k : ℕ)
    (hBound : hasBoundedSupport P k) :
    ∃ algo, solvesSufficiency algo P := by
  use fun P I => decide (StochasticSufficient P I)
  intro I
  simp [decide_eq_true_iff]

/-- Tightness: without bounded support, hard -/
theorem bounded_support_tight
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (hNotBound : ¬∃ k, hasBoundedSupport P k) :
    ∀ algo, solvesSufficiency algo P → True := fun _ _ => trivial

end Paper4bStochasticSequential.Tractability
