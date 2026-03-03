/-
  Paper 4: Decision-Relevant Uncertainty

  Physics/WolpertResidual.lean

  This module promotes the strongest additional part of the residual branch that
  the current machinery can honestly prove without rebuilding full trajectory
  stochastic thermodynamics.

  The key idea is finite and local:

  - Given a discrete Markov process, compare the stationary edge flow `s → s'`
    against the reverse edge flow `s' → s`.
  - If both directions are positive and the two flows differ, then the induced
    two-point forward/reverse flow distributions differ.
  - The existing KL machinery then forces strictly positive divergence.

  This does not claim the full stopping-time / absolute-irreversibility theorem
  of the cited papers. It proves a theorem-level finite-support residual
  asymmetry branch that can be composed with the current Wolpert decomposition.
-/

import DecisionQuotient.Physics.TUR
import DecisionQuotient.Physics.WolpertMismatch
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators
open Finset

namespace DecisionQuotient
namespace Physics
namespace WolpertResidual

open WolpertMismatch

/-- Stationary edge-flow weight on the directed edge `s → s'`. -/
noncomputable def edgeFlow {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S) : ℝ :=
  stationaryProb π s * transitionProb mc s s'

/-- Total two-edge mass used to normalize the local forward/reverse pair. -/
noncomputable def pairFlowMass {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S) : ℝ :=
  edgeFlow mc π s s' + edgeFlow mc π s' s

/-- The normalized two-point forward distribution for the pair `(s,s')`. -/
noncomputable def forwardPairDistribution {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s) :
    StrictFiniteDistribution Bool := by
  refine
    { pmf := fun b =>
        if b then
          edgeFlow mc π s s' / pairFlowMass mc π s s'
        else
          edgeFlow mc π s' s / pairFlowMass mc π s s'
      sum_eq_one := ?_
      pos := ?_ }
  · have hMassNe : pairFlowMass mc π s s' ≠ 0 := by
      unfold pairFlowMass
      linarith
    rw [Fintype.sum_bool]
    simp
    field_simp [hMassNe]
    simp [pairFlowMass]
  · intro b
    by_cases hb : b
    · simp [hb]
      have hMassPos : 0 < pairFlowMass mc π s s' := by
        unfold pairFlowMass
        linarith
      exact div_pos hForward hMassPos
    · simp [hb]
      have hMassPos : 0 < pairFlowMass mc π s s' := by
        unfold pairFlowMass
        linarith
      exact div_pos hReverse hMassPos

/-- The normalized two-point reverse distribution for the pair `(s,s')`. -/
noncomputable def reversePairDistribution {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s) :
    StrictFiniteDistribution Bool := by
  refine
    { pmf := fun b =>
        if b then
          edgeFlow mc π s' s / pairFlowMass mc π s s'
        else
          edgeFlow mc π s s' / pairFlowMass mc π s s'
      sum_eq_one := ?_
      pos := ?_ }
  · have hMassNe : pairFlowMass mc π s s' ≠ 0 := by
      unfold pairFlowMass
      linarith
    rw [Fintype.sum_bool]
    simp
    field_simp [hMassNe]
    simp [pairFlowMass, add_comm]
  · intro b
    by_cases hb : b
    · simp [hb]
      have hMassPos : 0 < pairFlowMass mc π s s' := by
        unfold pairFlowMass
        linarith
      exact div_pos hReverse hMassPos
    · simp [hb]
      have hMassPos : 0 < pairFlowMass mc π s s' := by
        unfold pairFlowMass
        linarith
      exact div_pos hForward hMassPos

/-- Two-point KL divergence comparing the local forward and reverse edge-flow
distributions. This is the theorem-level finite residual asymmetry quantity
available from the current machinery. -/
noncomputable def pairwiseResidualKL {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s) : ℝ :=
  mismatchKL
    (forwardPairDistribution mc π s s' hForward hReverse)
    (reversePairDistribution mc π s s' hForward hReverse)

/-- The local residual asymmetry quantity is always nonnegative. -/
theorem pairwiseResidualKL_nonneg {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s) :
    0 ≤ pairwiseResidualKL mc π s s' hForward hReverse := by
  unfold pairwiseResidualKL
  exact mismatchKL_nonneg
    (forwardPairDistribution mc π s s' hForward hReverse)
    (reversePairDistribution mc π s s' hForward hReverse)

/-- Any explicit asymmetry between the two directed edge flows forces strictly
positive finite-support residual divergence. -/
theorem pairwiseResidualKL_pos_of_asymmetry {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s)
    (hAsym : edgeFlow mc π s s' ≠ edgeFlow mc π s' s) :
    0 < pairwiseResidualKL mc π s s' hForward hReverse := by
  unfold pairwiseResidualKL
  have hMassNe : pairFlowMass mc π s s' ≠ 0 := by
    unfold pairFlowMass
    linarith
  refine mismatchKL_pos_of_exists_ne
    (forwardPairDistribution mc π s s' hForward hReverse)
    (reversePairDistribution mc π s s' hForward hReverse) ?_
  refine ⟨true, ?_⟩
  simp [forwardPairDistribution, reversePairDistribution]
  intro hEq
  field_simp [hMassNe] at hEq
  exact hAsym hEq

/-- Nat-valued residual lower-bound units obtained by conservatively rounding
the finite-support residual asymmetry witness upward. -/
noncomputable def residualNatLowerBound {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s) : ℕ :=
  Nat.ceil (pairwiseResidualKL mc π s s' hForward hReverse)

/-- Any positive finite-support residual asymmetry witness yields a positive
nat-valued lower-bound term after the declared upward rounding. -/
theorem residualNatLowerBound_pos_of_asymmetry {S : Type*} [Fintype S]
    (mc : DiscreteMarkovChain S) (π : StationaryDist mc) (s s' : S)
    (hForward : 0 < edgeFlow mc π s s')
    (hReverse : 0 < edgeFlow mc π s' s)
    (hAsym : edgeFlow mc π s s' ≠ edgeFlow mc π s' s) :
    0 < residualNatLowerBound mc π s s' hForward hReverse := by
  unfold residualNatLowerBound
  exact (Nat.ceil_pos).2 (pairwiseResidualKL_pos_of_asymmetry mc π s s' hForward hReverse hAsym)

end WolpertResidual
end Physics
end DecisionQuotient
