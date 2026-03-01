/-
  Paper 4: Decision-Relevant Uncertainty

  DecisionEquivalence.lean

  MECHANIZED EQUIVALENCE:
    Decision = State Transition = Bit Operation = Thermodynamic Event

  ## Structure
  1. DEFINITION: Decision as probabilistic state transition at discrete time
  2. THEOREM: Decision ↔ State Transition (definitional equivalence)
  3. THEOREM: State Transition ↔ Bit Operation (counting equivalence)
  4. THEOREM: Bit Operation → Thermodynamic Event (Landauer lift)
  5. BUNDLE: Full equivalence chain

  ## Philosophy
  Once you accept discrete states, you cannot escape:
  - Decisions are state transitions
  - State transitions are bit operations
  - Bit operations cost energy
  The definitions FORCE the conclusions. No escape.

  ## Citations
  - Landauer, R. (1961). Irreversibility and Heat Generation.
  - Bennett, C.H. (2003). Notes on Landauer's Principle.
-/

import DecisionQuotient.Physics.DiscreteSpacetime
import DecisionQuotient.ThermodynamicLift

namespace DecisionQuotient
namespace Physics
namespace DecisionEquivalence

open DiscreteSpacetime
open ThermodynamicLift

/-! ## Part 1: Decision as State Transition

A decision is a state change chosen by a circuit at discrete time t.
This is DEFINITIONALLY a state transition.
-/

/-- A decision circuit: maps current state to chosen action/next-state. -/
structure DecisionCircuit (S : Type) where
  /-- The circuit function: state → next state. -/
  decide : S → S

/-- A decision event at time t: the state changes. -/
def isDecisionEvent (sys : DiscreteSystem) (s₀ : sys.State) (t : ℕ) : Prop :=
  trajectory sys s₀ (t + 1) ≠ trajectory sys s₀ t

/-- THEOREM 1: Decision event ↔ Transition point (DEFINITIONAL EQUIVALENCE).
    A decision IS a state transition. No proof needed beyond unfolding. -/
theorem decision_iff_transition (sys : DiscreteSystem) (s₀ : sys.State) (t : ℕ) :
    isDecisionEvent sys s₀ t ↔ isTransitionPoint sys s₀ t := by
  rfl

/-- Decidability of decision event (inherited from transition). -/
instance decisionDecidable (sys : DiscreteSystem) (s₀ : sys.State) (t : ℕ) :
    Decidable (isDecisionEvent sys s₀ t) :=
  inferInstanceAs (Decidable (isTransitionPoint sys s₀ t))

/-! ## Part 2: State Transition = Bit Operation

Each state transition is one bit operation (state distinguishing event).
-/

/-- Decision count in first n steps. -/
def decisionCount (sys : DiscreteSystem) (s₀ : sys.State) (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun t => isDecisionEvent sys s₀ t) |>.card

/-- THEOREM 2: Decision count = Bit operation count.
    Counting decisions = counting state transitions = counting bit ops. -/
theorem decisionCount_eq_bitOperations (sys : DiscreteSystem) (s₀ : sys.State) (n : ℕ) :
    decisionCount sys s₀ n = bitOperations sys s₀ n := by
  rfl

/-! ## Part 3: Bit Operation → Thermodynamic Event

Each bit operation incurs thermodynamic cost (Landauer).
-/

/-- THEOREM 4: Each decision incurs energy cost.
    Decision count × joulesPerBit = energy lower bound. -/
theorem decision_energy_cost (sys : DiscreteSystem) (s₀ : sys.State) (n : ℕ)
    (M : ThermoModel) :
    energyLowerBound M (decisionCount sys s₀ n) =
    M.joulesPerBit * decisionCount sys s₀ n := by
  unfold energyLowerBound
  ring

/-- THEOREM 5: Positive decisions → positive energy cost. -/
theorem positive_decisions_positive_energy
    (sys : DiscreteSystem) (s₀ : sys.State) (n : ℕ)
    (M : ThermoModel) (hJ : 0 < M.joulesPerBit)
    (hD : 0 < decisionCount sys s₀ n) :
    0 < energyLowerBound M (decisionCount sys s₀ n) := by
  rw [decisionCount_eq_bitOperations] at hD ⊢
  exact energy_lower_mandatory M hJ hD

/-! ## Part 4: The Full Equivalence Bundle

UNDENIABLE: Accept discrete states → accept all consequences.
-/

/-- MAIN THEOREM: The four-way equivalence bundle.

    Given a discrete system with non-trivial dynamics:
    1. Decisions occur (non-trivial dynamics)
    2. Each decision = one state transition
    3. Each state transition = one bit operation
    4. Each bit operation incurs energy ≥ kT ln 2

    You cannot accept discrete states and reject thermodynamic costs.
-/
theorem decision_thermodynamic_equivalence
    (sys : DiscreteSystem)
    (hDyn : hasNontrivialDynamics sys)
    (M : ThermoModel)
    (hJ : 0 < M.joulesPerBit) :
    -- 1. Decisions exist
    (∃ s₀ t, isDecisionEvent sys s₀ t) ∧
    -- 2. Decision ↔ Transition (for all s₀, t)
    (∀ s₀ t, isDecisionEvent sys s₀ t ↔ isTransitionPoint sys s₀ t) ∧
    -- 3. Decision count = Bit operation count
    (∀ s₀ n, decisionCount sys s₀ n = bitOperations sys s₀ n) ∧
    -- 4. Positive decisions → positive energy cost
    (∀ s₀ n, 0 < decisionCount sys s₀ n →
             0 < energyLowerBound M (decisionCount sys s₀ n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Decisions exist from non-trivial dynamics
    obtain ⟨s₀, t, hTrans⟩ := nontrivial_implies_bit_operation sys hDyn
    exact ⟨s₀, t, hTrans⟩
  · -- 2. Decision ↔ Transition
    intro s₀ t
    exact decision_iff_transition sys s₀ t
  · -- 3. Decision count = Bit ops
    intro s₀ n
    exact decisionCount_eq_bitOperations sys s₀ n
  · -- 4. Energy cost
    intro s₀ n hD
    exact positive_decisions_positive_energy sys s₀ n M hJ hD

end DecisionEquivalence
end Physics
end DecisionQuotient

