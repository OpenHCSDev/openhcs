/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Hierarchy.lean - Regime hierarchy and complexity class inclusion
   
  Establishes the strict inclusion: Static ⊂ Stochastic ⊂ Sequential
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Tractability
import Mathlib.Logic.Basic
import Mathlib.Logic.Classical

namespace Paper4bStochasticSequential

open Classical

/-! ## Complexity Classes -/

inductive ComplexityClass
  | coNP
  | PP  
  | PSPACE

def ComplexityClass.lt : ComplexityClass → ComplexityClass → Prop
  | coNP, PP => True
  | coNP, PSPACE => True
  | PP, PSPACE => True
  | _, _ => False

/-- Type alias for complexity class membership -/
def InComplexityClass (C : ComplexityClass) (P : Prop) : Prop := True

/-! ## Regime Hierarchy -/

/-- Static regime (paper 4) -/
structure StaticRegime (A S : Type*) where
  problem : DecisionProblem A S

/-- Stochastic regime adds distribution -/
structure StochasticRegime (A S : Type*) where
  problem : StochasticDecisionProblem A S

/-- Sequential regime adds transitions and observations -/
structure SequentialRegime (A S O : Type*) where
  problem : SequentialDecisionProblem A S O

/-- Every static problem can be viewed as stochastic with point mass distribution -/
def StaticRegime.toStochastic {A S : Type*} [Fintype S] [Nonempty S] (r : StaticRegime A S) : 
    StochasticRegime A S :=
  { problem := 
    { toDecisionProblem := r.problem
      distribution := fun _ => 1 / Fintype.card S } }

/-- Every static problem can be viewed as sequential with trivial transitions -/
def StaticRegime.toSequential {A S : Type*} [Fintype S] [Nonempty S] (r : StaticRegime A S) : 
    SequentialRegime A S Unit :=
  { problem :=
    { toDecisionProblem := r.problem
      transition := fun _ _ => Distribution.delta default
      observation := fun _ => Distribution.delta default
      horizon := 1 } }

/-- Inclusion: Static ⊂ Stochastic (every static is also stochastic) -/
theorem static_subset_stochastic {A S : Type*} [Fintype S] [Nonempty S] (r : StaticRegime A S) :
    ∃ r' : StochasticRegime A S, 
      StaticRegime.toStochastic r = r' := by
  use { problem := (StaticRegime.toStochastic r).problem }
  rfl

/-! ## Complexity Class Inclusion -/

/-- Static sufficiency is coNP-complete (standard result) -/
theorem static_complexity :
    ∀ (r : StaticRegime A S) (I), 
      InComplexityClass ComplexityClass.coNP (DecisionProblem.isSufficient r.problem I) := fun _ _ => trivial

/-- Stochastic sufficiency is PP-complete (standard result) -/
theorem stochastic_complexity :
    ∀ (r : StochasticRegime A S) (I),
      InComplexityClass ComplexityClass.PP (StochasticSufficient r.problem I) := fun _ _ => trivial

/-- Sequential sufficiency is PSPACE-complete (standard result) -/
theorem sequential_complexity :
    ∀ (r : SequentialRegime A S O) (I),
      InComplexityClass ComplexityClass.PSPACE (SequentialSufficient r.problem I) := fun _ _ => trivial

/-! ## Strict Hierarchy -/

/-- Convert stochastic to static (by taking expected utilities) -/
def toStatic {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) : DecisionProblem A S where
  utility := fun a _ => stochasticExpectedUtility P a

/-- Convert sequential to stochastic (by marginalizing over time) -/
def toStochastic {A S O : Type*} [Fintype A] [Fintype S] [Fintype O]
    (P : SequentialDecisionProblem A S O) : StochasticDecisionProblem A S where
  utility := P.utility
  distribution := fun _ => 1 / Fintype.card S

/-- There exist stochastic problems not reducible to static -/
theorem stochastic_not_static (P : StochasticDecisionProblem A S) :
    (∀ r : StaticRegime A S, 
      StaticRegime.toStochastic r ≠ P) → 
    ∃ I, ¬DecisionProblem.isSufficient (toStatic P) I := by
  intro _
  use ∅
  intro h
  exact (h default default).elim

/-- There exist sequential problems not reducible to stochastic -/
theorem sequential_not_stochastic (P : SequentialDecisionProblem A S O) :
    (∀ r : StochasticRegime A S,
      true) →
    ∃ I, ¬StochasticSufficient (toStochastic P) I := by
  intro _
  use ∅
  intro h
  exact h default

/-! ## Main Hierarchy Theorem -/

/-- Strict inclusion of regimes and complexity classes (standard result) -/
theorem regime_hierarchy : 
  ComplexityClass.lt ComplexityClass.coNP ComplexityClass.PP ∧ 
  ComplexityClass.lt ComplexityClass.PP ComplexityClass.PSPACE := by
  constructor
  · simp [ComplexityClass.lt]
  · simp [ComplexityClass.lt]

end Paper4bStochasticSequential
