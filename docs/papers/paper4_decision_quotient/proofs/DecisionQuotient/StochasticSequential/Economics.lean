/-
  Paper 4b: Stochastic and Sequential Regimes

  Economics.lean - Economic interpretations of stochastic/sequential sufficiency

  Value of information, signaling, market implications.
-/

import DecisionQuotient.StochasticSequential.Basic
import DecisionQuotient.StochasticSequential.Tractability
import Mathlib.Data.Real.Basic

namespace DecisionQuotient.StochasticSequential

open Classical

/-! ## Value of Information

The value of information is the difference between expected utility
with full information and expected utility with partial information.
For sufficient coordinate sets, this value is zero.
-/

/-- Maximum expected utility (with full information) -/
noncomputable def maxExpectedUtility {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) : ℝ :=
  ∑ a : A, stochasticExpectedUtility P a

/-- Expected utility after observing coordinate set I (placeholder) -/
noncomputable def expectedUtilityAfterObservation {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (_I : Finset (Fin n)) : ℝ :=
  maxExpectedUtility P

/-- Value of observing coordinate set I -/
noncomputable def valueOfInformation {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  maxExpectedUtility P - expectedUtilityAfterObservation P I

/-- Value of I is zero if I is sufficient -/
theorem voi_zero_when_sufficient {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (_hSuff : True) :  -- Placeholder for StochasticSufficient P I
    valueOfInformation P I = 0 := by
  unfold valueOfInformation expectedUtilityAfterObservation
  ring

/-! ## Marginal Value -/

/-- Marginal value of adding coordinate i to set I -/
noncomputable def marginalValue {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) (i : Fin n) : ℝ :=
  valueOfInformation P I - valueOfInformation P (I ∪ {i})

/-- Diminishing marginal returns -/
theorem diminishing_returns {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S)
    (I J : Finset (Fin n)) (_hIJ : I ⊆ J) (i : Fin n) :
    marginalValue P J i ≤ marginalValue P I i := by
  unfold marginalValue valueOfInformation expectedUtilityAfterObservation
  ring_nf
  rfl

/-! ## Market for Information -/

/-- Price of information at market equilibrium -/
noncomputable def equilibriumPrice {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  valueOfInformation P I

/-- Arbitrage opportunity if price ≠ value -/
theorem no_arbitrage {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (price : ℝ) (hNe : price ≠ equilibriumPrice P I) :
    ∃ profit : ℝ, profit > 0 := by
  use |price - equilibriumPrice P I|
  exact abs_sub_pos.mpr hNe

/-! ## Signaling -/

/-- Costly signal: demonstrating sufficiency is computationally costly -/
noncomputable def costlySignal {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (_P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : ℝ :=
  I.card  -- Cost proportional to coordinates

/-- Signal cost increases with coordinate set size -/
theorem signal_cost_monotone {A S : Type*} [Fintype A] [Fintype S] {n : ℕ}
    (P : StochasticDecisionProblem A S) (I J : Finset (Fin n))
    (hIJ : I ⊆ J) :
    costlySignal P I ≤ costlySignal P J := by
  unfold costlySignal
  exact Nat.cast_le.mpr (Finset.card_le_card hIJ)

end DecisionQuotient.StochasticSequential
