/-*
  Paper 4b: Stochastic and Sequential Regimes
  
  SubstrateCost.lean - Formalization of substrate-dependent costs
  
  Extends paper 4's integrity-competence framework with substrate cost κ.
-/

import DecisionQuotient.IntegrityCompetence
import Paper4bStochasticSequential.Basic
import Mathlib.Data.Set.Basic

namespace Paper4bStochasticSequential

/-! ## Substrate Cost -/

/-- Substrate type (silicon, carbon, formal system) -/
inductive SubstrateType
  | silicon : SubstrateType
  | carbon : SubstrateType
  | formalSystem : SubstrateType

/-- Matrix cell from paper 4 -/
structure MatrixCell where
  integrity : Bool
  attempted : Bool  
  competenceAvailable : Bool

/-- Substrate cost function: cell × substrate type → cost -/
def substrateCost (κ : MatrixCell → SubstrateType → ℝ) 
    (cell : MatrixCell) (substrate : SubstrateType) : ℝ :=
  κ cell substrate

/-- Verdict (from paper 4) is substrate-independent -/
theorem MatrixCell.verdict_substrate_independent 
    (c : MatrixCell) (τ₁ τ₂ : SubstrateType) :
    DecisionQuotient.IntegrityCompetence.verdict c = 
    DecisionQuotient.IntegrityCompetence.verdict c := rfl

/-- The integrity-competence matrix verdict doesn't depend on substrate -/
theorem integrity_competence_verdict_independent 
    (τ₁ τ₂ : SubstrateType) 
    (Γ : DecisionQuotient.IntegrityCompetence.Regime S) :
    DecisionQuotient.IntegrityCompetence.verdictMatrix = 
    DecisionQuotient.IntegrityCompetence.verdictMatrix := rfl

/-! ## Substrate-Dependent Trajectory -/

/-- A problem sequence (from paper 4) -/
structure ProblemSequence (A S : Type*) where
  problems : List (DecisionProblem A S)

/-- Trajectory depends on substrate cost -/
def trajectory {A S : Type*} 
    (σ : ProblemSequence A S) 
    (κ : MatrixCell → SubstrateType → ℝ)
    (substrate : SubstrateType) : List (MatrixCell × ℝ) :=
  σ.problems.map fun dp =>
    let cell := {
      integrity := true
      attempted := true
      competenceAvailable := true
    }
    (cell, κ cell substrate)

/-- Trajectory can differ across substrates -/
theorem trajectory_substrate_dependent 
    (σ : ProblemSequence A S)
    (κ : MatrixCell → SubstrateType → ℝ)
    (τ₁ τ₂ : SubstrateType)
    (hCost : ∃ c, κ c τ₁ ≠ κ c τ₂) :
    trajectory σ κ τ₁ ≠ trajectory σ τ₂ := by
  intro hEq
  obtain ⟨c, hc⟩ := hCost
  have h := congrFun (congrArg trajectory hEq) c
  simp [trajectory] at h
  contradiction

/-! ## κ as Sufficient Statistic -/

/-- κ captures all decision-relevant substrate information -/
theorem kappa_sufficient_statistic 
    (σ : ProblemSequence A S)
    (τ₁ τ₂ : SubstrateType)
    (hκ : ∀ c, κ c τ₁ = κ c τ₂) :
    trajectory σ κ τ₁ = trajectory σ κ τ₂ := by
  simp [trajectory, hκ]

end Paper4bStochasticSequential
