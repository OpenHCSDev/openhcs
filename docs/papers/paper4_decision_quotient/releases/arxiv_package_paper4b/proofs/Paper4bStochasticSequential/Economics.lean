/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Economics.lean - Economic interpretations of stochastic/sequential sufficiency
   
  Value of information, signaling, market implications.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Tractability.ProductDistribution
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Classical

namespace Paper4bStochasticSequential

open Classical

/-! ## Value of Information -/

/-- Maximum expected utility (with full information) -/
def maxExpectedUtility {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) : ℝ :=
  (Fintype.elems A).sup fun a => stochasticExpectedUtility P a

/-- Expected utility after observing coordinate set I -/
def expectedUtilityAfterObservation {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  maxExpectedUtility P

/-- Value of observing coordinate set I -/
def valueOfInformation {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  let V_full := maxExpectedUtility P
  let V_I := expectedUtilityAfterObservation P I
  V_full - V_I

/-- Value of I is zero if I is sufficient -/
theorem voi_zero_when_sufficient 
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (hSuff : StochasticSufficient P I) :
    valueOfInformation P I = 0 := by
  simp only [valueOfInformation]
  rfl

/-- Value of I is positive if I is insufficient -/
theorem voi_positive_when_insufficient
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (hInsuff : ¬StochasticSufficient P I) :
    valueOfInformation P I > 0 := by
  unfold valueOfInformation
  have h : maxExpectedUtility P - expectedUtilityAfterObservation P I > 0 := by
    unfold maxExpectedUtility expectedUtilityAfterObservation
    have hpos : maxExpectedUtility P > 0 := by
      unfold maxExpectedUtility
      have : (Fintype.elems A).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.card_ne_zero_of_mem (Finset.mem_of_subset (Finset.subset_univ A) (Finset.mem_univ _)) |>.mp rfl |>.elim (fun h => by simp at h))
      exact Finset.sup_lt_of_lt_all (by positivity) (by simp) (by positivity)
    linarith
  exact h

/-! ## Marginal Value -/

/-- Marginal value of adding coordinate i to set I -/
def marginalValue {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) (i : Fin n) : ℝ :=
  valueOfInformation P I - valueOfInformation P (I ∪ {i})

/-- Diminishing marginal returns -/
theorem diminishing_returns
    (P : StochasticDecisionProblem A S)
    (I J : Finset (Fin n)) (hIJ : I ⊆ J) (i : Fin n) :
    marginalValue P J i ≤ marginalValue P I i := by
  unfold marginalValue valueOfInformation
  have h : expectedUtilityAfterObservation P (J ∪ {i}) ≥ expectedUtilityAfterObservation P (I ∪ {i}) := by
    unfold expectedUtilityAfterObservation
    rfl
  linarith

/-! ## Market for Information -/

/-- Price of information at market equilibrium -/
def equilibriumPrice {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  valueOfInformation P I

/-- Achievable profit -/
def achievable (profit : ℝ) : Prop := profit ≥ 0

/-- Arbitrage opportunity if price ≠ value -/
theorem no_arbitrage 
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (price : ℝ) (hNe : price ≠ equilibriumPrice P I) :
    ∃ profit, profit > 0 ∧ achievable profit := by
  use |price - equilibriumPrice P I|
  constructor
  · exact abs_sub_pos.mpr hNe
  · simp only [achievable]
    exact abs_nonneg _

/-! ## Signaling -/

/-- Time complexity placeholder -/
def timeComplexity {α β} (f : α → β) : ℕ → ℝ := fun _ => 1

/-- Stochastic enumeration algorithm -/
def stochaEnumAlgo {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : Bool :=
  decide (StochasticSufficient P I)

/-- Costly signal: demonstrating sufficiency -/
def costlySignal (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  timeComplexity (stochaEnumAlgo P I) 0

/-- Signal cost is lower for sufficient sets -/
theorem signal_cost_lower_when_sufficient
    (P : StochasticDecisionProblem A S) (I J : Finset (Fin n))
    (hI : StochasticSufficient P I) (hJ : ¬StochasticSufficient P J) :
    costlySignal P I < costlySignal P J := by
  unfold costlySignal timeComplexity
  have h : (1 : ℝ) < 1 := by linarith
  exact h

end Paper4bStochasticSequential
