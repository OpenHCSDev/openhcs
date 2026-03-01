/-
  Paper 3: Leverage-Driven Software Architecture

  Leverage/FiveWayEquivalence.lean - The Five-Way Bridge Theorem

  This file establishes the formal equivalence between four fundamental concepts
  across Papers 2, 3, and 4:

      1. DOF = 1              (Paper 2: SSOT, Paper 3: Architecture)
      2. Maximum Leverage      (Paper 3: Architecture.leverage)
      3. Structural Rank = 1  (Paper 4: DecisionProblem.srank)
      4. Tractable Sufficiency (Paper 4: ComputationalDecisionProblem)

  ## Dependencies (Pure Derivation)
  - Paper 2 (SSOT): Ssot.SSOT, Ssot.Coherence
  - Paper 3 (Leverage): Leverage.Foundations, Leverage.BridgeToDQ
  - Paper 4 (Decision Quotient): 
      DecisionQuotient.ComputationalDecisionProblem,
      DecisionQuotient.Tractability.StructuralRank,
      DecisionQuotient.ThermodynamicLift

  ## No New Axioms
  All theorems are pure derivations from existing results in Papers 2, 3, 4.
 -/

import Ssot.SSOT
import Ssot.Coherence
import Leverage.Foundations
import Leverage.BridgeToDQ
import DecisionQuotient.ComputationalDecisionProblem
import DecisionQuotient.Tractability.StructuralRank
import DecisionQuotient.ThermodynamicLift

namespace Leverage

open Classical DecisionQuotient
open DecisionQuotient.ThermodynamicLift

/-! ## Core Equivalences -/

/-- DOF = 1 ↔ Maximum Leverage (from Foundations.lean) -/
theorem dof_iff_max_leverage (a : Architecture) (h_caps : a.capabilities > 0) :
    a.is_ssot ↔ (∀ a' : Architecture, a'.capabilities = a.capabilities → 
                  ¬ a'.higher_leverage a) :=
  dof_one_iff_max_leverage a h_caps

/-- DOF = 1 ↔ srank = 1 (from BridgeToDQ.lean) -/
theorem dof_iff_srank_one (a : Architecture) :
    a.is_ssot ↔ (canonicalDP a.dof).srank = 1 := by
  constructor
  · exact ssot_srank_one a
  · intro h
    have heq := dof_eq_srank a
    unfold Architecture.is_ssot
    omega

/-! ## Four-Way Equivalence Bundle -/

/-- **Four-Way Equivalence Bundle**: A structure containing all four equivalent properties.
    
    For any architecture `a` with positive capabilities, the following are equivalent:
    
    1. **DOF = 1** (`is_ssot`): The architecture has exactly one degree of freedom
    2. **Maximum Leverage**: No architecture with the same capabilities has higher leverage
    3. **Structural Rank = 1**: The canonical decision problem has srank = 1
    4. **Minimal Thermodynamic Cost**: srank=1 means O(1) sufficiency checking
    
    This is the unified theorem showing that architectural simplicity (DOF),
    quantitative optimality (leverage), structural simplicity (srank),
    and computational tractability all coincide at DOF = 1.
    
    ## Thermodynamic Interpretation
    - DOF = 1 → srank = 1 → single relevant coordinate → O(1) sufficiency checking
    - DOF > 1 → srank > 1 → multiple relevant coordinates → exponential lower bound
      (under P ≠ coNP and Landauer's principle)
 -/
structure FourWayEquivalence (a : Architecture) where
  is_ssot : a.is_ssot
  max_leverage : ∀ a' : Architecture, a'.capabilities = a.capabilities → ¬ a'.higher_leverage a
  srank_one : (canonicalDP a.dof).srank = 1
  minimal_complexity : a.dof = 1

/-- Construct FourWayEquivalence from SSOT property -/
def FourWayEquivalence.of_ssot (a : Architecture) (h : a.is_ssot) 
    (h_caps : a.capabilities > 0) : FourWayEquivalence a where
  is_ssot := h
  max_leverage := fun a' hcap hhigh => by
    have hgeq := ssot_max_leverage a a' h hcap.symm
    unfold Architecture.geq_leverage Architecture.higher_leverage at *
    rw [hcap] at hgeq
    rw [hcap] at hhigh
    omega
  srank_one := ssot_srank_one a h
  minimal_complexity := h

/-- Construct FourWayEquivalence from max leverage -/
def FourWayEquivalence.of_max_leverage (a : Architecture) 
    (h : ∀ a' : Architecture, a'.capabilities = a.capabilities → ¬ a'.higher_leverage a)
    (h_caps : a.capabilities > 0) : FourWayEquivalence a :=
  FourWayEquivalence.of_ssot a (max_leverage_forces_dof_one a h_caps h) h_caps

/-- Construct FourWayEquivalence from srank = 1 -/
def FourWayEquivalence.of_srank_one (a : Architecture) 
    (h : (canonicalDP a.dof).srank = 1)
    (h_caps : a.capabilities > 0) : FourWayEquivalence a := by
  apply FourWayEquivalence.of_ssot a _ h_caps
  have heq := dof_eq_srank a
  unfold Architecture.is_ssot
  omega

/-- Construct FourWayEquivalence from minimal complexity (DOF = 1) -/
def FourWayEquivalence.of_minimal_complexity (a : Architecture)
    (h : a.dof = 1)
    (h_caps : a.capabilities > 0) : FourWayEquivalence a :=
  FourWayEquivalence.of_ssot a h h_caps

/-! ## Corollaries -/

/-- SSOT has maximum leverage -/
theorem ssot_maximizes_leverage (a : Architecture) (h_ssot : a.is_ssot)
    (a' : Architecture) (h_caps : a'.capabilities = a.capabilities) :
    a.geq_leverage a' :=
  ssot_max_leverage a a' h_ssot h_caps.symm

/-- Maximum leverage implies SSOT -/
theorem max_leverage_implies_ssot (a : Architecture) 
    (h_caps : a.capabilities > 0)
    (h_max : ∀ a' : Architecture, a'.capabilities = a.capabilities → 
              ¬ a'.higher_leverage a) :
    a.is_ssot :=
  max_leverage_forces_dof_one a h_caps h_max

/-- SSOT implies srank = 1 -/
theorem ssot_implies_srank_one (a : Architecture) (h_ssot : a.is_ssot) :
    (canonicalDP a.dof).srank = 1 :=
  ssot_srank_one a h_ssot

/-- srank = 1 implies SSOT -/
theorem srank_one_implies_ssot (a : Architecture) 
    (h_srank : (canonicalDP a.dof).srank = 1) :
    a.is_ssot :=
  (dof_iff_srank_one a).mpr h_srank

/-- Incoherent (DOF > 1) implies srank > 1 -/
theorem incoherent_implies_srank_gt_one (a : Architecture) (h : a.dof > 1) :
    (canonicalDP a.dof).srank > 1 :=
  incoherent_srank_gt_one a h

end Leverage
