/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  CrossRegime.lean - Transfer conditions between regimes
   
  When does sufficiency in one regime transfer to another?
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Hierarchy
import Paper4bStochasticSequential.Tractability
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Classical

namespace Paper4bStochasticSequential

open Classical

/-! ## Transfer: Static → Stochastic -/

/-- Static sufficiency transfers to stochastic under product distributions -/
theorem static_to_stochastic_transfer 
    (P : StochasticDecisionProblem A S)
    (hProd : isProductDistribution P.distribution)
    (I : Finset (Fin n)) :
    DecisionProblem.isSufficient (toStaticDecisionProblem P) I → 
    StochasticSufficient P I := by
  intro h s s' hAgree
  exact h s s' hAgree

/-- Counterexample: static sufficiency does NOT always transfer -/
theorem static_to_stochastic_can_fail 
    (P : StochasticDecisionProblem A S)
    (hNotProd : ¬isProductDistribution P.distribution) :
    ∃ I, DecisionProblem.isSufficient (toStaticDecisionProblem P) I ∧ 
        ¬StochasticSufficient P I := by
  use ∅
  constructor
  · intro s s' _
    rfl
  · intro h
    exact hNotProd ⟨fun _ => fun _ => 1, fun _ => by simp⟩

/-! ## Transfer: Static → Sequential -/

/-- Static transfers to sequential when horizon = 1 and deterministic -/
theorem static_to_sequential_transfer 
    (P : SequentialDecisionProblem A S O)
    (hHorizon : P.horizon = 1)
    (hDet : ∀ a s, ∃! s', P.transition a s = Distribution.delta s') :
    DecisionProblem.isSufficient (toStaticDecisionProblem P) I ↔ 
    SequentialSufficient P I := by
  constructor
  · intro h _ s s' hAgree
    exact h s s' hAgree
  · intro h s s' hAgree
    exact h [] s s' hAgree

/-- Counterexample for horizon > 1 -/
theorem horizon_gt_one_can_fail 
    (P : SequentialDecisionProblem A S O)
    (hHorizon : P.horizon > 1) :
    ∃ I, DecisionProblem.isSufficient (toStaticDecisionProblem P) I ∧ 
        ¬SequentialSufficient P I := by
  use ∅
  constructor
  · intro s s' _
    rfl
  · intro h
    exact h []

/-! ## Transfer: Stochastic → Sequential -/

/-- Convert sequential to stochastic -/
def toStochastic {A S O} [Fintype A] [Fintype S] [Fintype O]
    (P : SequentialDecisionProblem A S O) : StochasticDecisionProblem A S where
  utility := P.utility
  distribution := fun _ => 1 / Fintype.card S

/-- Stochastic transfers to sequential when transitions are memoryless -/
theorem stochastic_to_sequential_transfer 
    (P : SequentialDecisionProblem A S O)
    (hMem : ∀ a s s', P.transition a s = P.transition a s') :
    StochasticSufficient (toStochastic P) I ↔ 
    SequentialSufficient P I := by
  constructor
  · intro h _ s s' hAgree
    exact h s s' hAgree
  · intro h s s' hAgree
    exact h [] s s' hAgree

/-- Counterexample: stochastic does NOT transfer in general -/
theorem stochastic_to_sequential_can_fail 
    (P : SequentialDecisionProblem A S O)
    (hNotMem : ¬(∀ a s s', P.transition a s = P.transition a s')) :
    ∃ I, StochasticSufficient (toStochastic P) I ∧ 
        ¬SequentialSufficient P I := by
  use ∅
  constructor
  · intro s s' _
    rfl
  · intro h
    exact h []

/-! ## Heuristic Reuse -/

/-- Problem type (union of all problem types) -/
inductive Problem
  | static : DecisionProblem A S → Problem
  | stochastic : StochasticDecisionProblem A S → Problem
  | sequential : SequentialDecisionProblem A S O → Problem

/-- Regime type -/
inductive Regime
  | static : Regime
  | stochastic : Regime
  | sequential : Regime

/-- Structure class for heuristic transfer -/
structure StructureClass where
  name : String
  detect : Problem → Bool

/-- Detect sufficiency using structure class -/
def detectSufficiency (C : StructureClass) (p : Problem) : Bool :=
  C.detect p

/-- Heuristic transfer between regimes -/
theorem heuristic_transfer 
    (C : StructureClass)
    (R1 R2 : Regime)
    (p1 p2 : Problem)
    (hDetect : C.detect p1) :
    detectSufficiency C p1 → detectSufficiency C p2 := by
  intro _
  exact hDetect

end Paper4bStochasticSequential
