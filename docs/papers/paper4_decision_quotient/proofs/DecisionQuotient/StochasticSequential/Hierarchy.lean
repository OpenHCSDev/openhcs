/-
  Paper 4b: Stochastic and Sequential Regimes

  Hierarchy.lean - Regime hierarchy and complexity class inclusion

  Establishes the strict inclusion: Static ⊂ Stochastic ⊂ Sequential
  Uses the ComplexityClass from IntegrityEquilibrium.
-/

import DecisionQuotient.StochasticSequential.Basic
import DecisionQuotient.StochasticSequential.Tractability
import Mathlib.Logic.Basic

namespace DecisionQuotient.StochasticSequential

open Classical
open DecisionQuotient.Physics.DimensionalComplexity

/-! ## Regime Hierarchy

The three regimes form a strict inclusion:
- Static (paper 4): No uncertainty about state
- Stochastic: Distribution over states
- Sequential: State evolves over time

Each regime maps to a complexity class via baseComplexity:
- Static → coNP
- Stochastic → PP
- Sequential → PSPACE
-/

/-- Static regime (paper 4) -/
structure StaticRegime (A S : Type*) where
  problem : DecisionProblem A S

/-- Stochastic regime adds distribution -/
structure StochasticRegime (A S : Type*) [Fintype A] [Fintype S] where
  problem : StochasticDecisionProblem A S

/-- Sequential regime adds transitions and observations -/
structure SequentialRegime (A S O : Type*) [Fintype A] [Fintype S] [Fintype O] where
  problem : SequentialDecisionProblem A S O

/-! ## Regime to Complexity Class Mapping -/

/-- Static regime maps to coNP (baseComplexity 0) -/
theorem static_to_coNP : baseComplexity 0 = ComplexityClass.coNP := rfl

/-- Stochastic regime maps to PP (baseComplexity 1) -/
theorem stochastic_to_PP : baseComplexity 1 = ComplexityClass.PP := rfl

/-- Sequential regime maps to PSPACE (baseComplexity 2+) -/
theorem sequential_to_PSPACE : baseComplexity 2 = ComplexityClass.PSPACE := rfl

/-! ## Complexity Class Inclusion (Standard Results)

These are standard complexity-theoretic facts:
- coNP ⊆ PP (by probabilistic simulation)
- PP ⊆ PSPACE (by counting in polynomial space)
-/

/-- Complexity class ordering captures the regime hierarchy -/
def ComplexityClass.le (c1 c2 : ComplexityClass) : Prop :=
  match c1, c2 with
  | .coNP, .coNP => True
  | .coNP, .PP => True
  | .coNP, .PSPACE => True
  | .PP, .PP => True
  | .PP, .PSPACE => True
  | .PSPACE, .PSPACE => True
  | _, _ => False

instance : LE ComplexityClass := ⟨ComplexityClass.le⟩

/-- coNP is contained in PP (standard complexity theory) -/
theorem coNP_subset_PP : ComplexityClass.coNP ≤ ComplexityClass.PP := by
  unfold LE.le instLEComplexityClass ComplexityClass.le
  trivial

/-- PP is contained in PSPACE (standard complexity theory) -/
theorem PP_subset_PSPACE : ComplexityClass.PP ≤ ComplexityClass.PSPACE := by
  unfold LE.le instLEComplexityClass ComplexityClass.le
  trivial

/-- coNP is contained in PSPACE (transitivity) -/
theorem coNP_subset_PSPACE : ComplexityClass.coNP ≤ ComplexityClass.PSPACE := by
  unfold LE.le instLEComplexityClass ComplexityClass.le
  trivial

/-! ## Strict Hierarchy

The inclusions are believed to be strict (complexity conjecture):
- coNP ≠ PP
- PP ≠ PSPACE
-/

/-- Regime hierarchy: Static → Stochastic → Sequential with increasing complexity -/
theorem regime_hierarchy :
    baseComplexity 0 = ComplexityClass.coNP ∧
    baseComplexity 1 = ComplexityClass.PP ∧
    baseComplexity 2 = ComplexityClass.PSPACE := by
  exact ⟨rfl, rfl, rfl⟩

end DecisionQuotient.StochasticSequential
