import DecisionQuotient.Basic
import Mathlib.Tactic

/-!
  Paper 4: Decision-Relevant Uncertainty

  UniverseObjective.lean

  Law-induced objective machinery:
  - universe transition laws induce feasibility sets over actions,
  - utilities can be defined directly from those laws,
  - with a strict allowed-vs-blocked gap, optimal actions are exactly feasible actions.
-/

namespace DecisionQuotient

universe u v

section UniverseObjective

variable {S : Type u} {A : Type v}

/-- Universe transition-law model at the decision abstraction level:
    whether action `a` is allowed at state `s`. -/
structure UniverseDynamics (S : Type u) (A : Type v) where
  allowed : S → A → Prop

/-- Law-induced utility:
    actions allowed by transition laws receive `uAllowed`, blocked actions receive `uBlocked`. -/
noncomputable def lawUtility (D : UniverseDynamics S A) (uAllowed uBlocked : ℝ) : A → S → ℝ :=
  by
    classical
    exact fun a s => if D.allowed s a then uAllowed else uBlocked

/-- Decision problem induced from universe laws and a two-level law utility. -/
noncomputable def lawDecisionProblem (D : UniverseDynamics S A) (uAllowed uBlocked : ℝ) :
    DecisionProblem A S where
  utility := lawUtility D uAllowed uBlocked

/-- Feasible action set at state `s` under universe laws. -/
def feasibleActions (D : UniverseDynamics S A) (s : S) : Set A :=
  {a : A | D.allowed s a}

/-- Logical determinism at the action layer:
    at most one action is allowed per state. -/
def logicallyDeterministic (D : UniverseDynamics S A) : Prop :=
  ∀ s : S, ∀ a a' : A, D.allowed s a → D.allowed s a' → a = a'

/-- Objective schema: once `D`, `uAllowed`, and `uBlocked` are fixed,
    the utility is exactly determined. -/
theorem universe_sets_objective_schema
    (D : UniverseDynamics S A) (uAllowed uBlocked : ℝ) :
    (lawDecisionProblem D uAllowed uBlocked).utility =
      lawUtility D uAllowed uBlocked := rfl

/-- Law-induced utility depends only on the allowed/blocked transition partition. -/
theorem lawUtility_eq_of_allowed_iff
    {D₁ D₂ : UniverseDynamics S A} {uAllowed uBlocked : ℝ}
    (hEq : ∀ s : S, ∀ a : A, D₁.allowed s a ↔ D₂.allowed s a) :
    lawUtility D₁ uAllowed uBlocked = lawUtility D₂ uAllowed uBlocked := by
  funext a s
  by_cases h1 : D₁.allowed s a
  · have h2 : D₂.allowed s a := (hEq s a).1 h1
    simp [lawUtility, h1, h2]
  · have h2 : ¬ D₂.allowed s a := by
      intro h2
      exact h1 ((hEq s a).2 h2)
    simp [lawUtility, h1, h2]

/-- If blocked actions are strictly lower utility than allowed actions, and at least one
    allowed action exists at `s`, then optimal actions are exactly the feasible actions. -/
theorem opt_eq_feasible_of_gap
    (D : UniverseDynamics S A) {uAllowed uBlocked : ℝ}
    (hGap : uBlocked < uAllowed) {s : S}
    (hExists : ∃ a : A, D.allowed s a) :
    (lawDecisionProblem D uAllowed uBlocked).Opt s = feasibleActions D s := by
  ext a
  constructor
  · intro hOpt
    by_contra hNot
    have hNotAllowed : ¬ D.allowed s a := by
      simpa [feasibleActions] using hNot
    rcases hExists with ⟨a0, ha0⟩
    have hLe :
        (lawDecisionProblem D uAllowed uBlocked).utility a0 s ≤
          (lawDecisionProblem D uAllowed uBlocked).utility a s := hOpt a0
    have hUA0 :
        (lawDecisionProblem D uAllowed uBlocked).utility a0 s = uAllowed := by
      simp [lawDecisionProblem, lawUtility, ha0]
    have hUA :
        (lawDecisionProblem D uAllowed uBlocked).utility a s = uBlocked := by
      simp [lawDecisionProblem, lawUtility, hNotAllowed]
    have : uAllowed ≤ uBlocked := by simpa [hUA0, hUA] using hLe
    exact (not_le_of_gt hGap) this
  · intro hAllowed
    have hAllowedLaw : D.allowed s a := by
      simpa [feasibleActions] using hAllowed
    intro a'
    by_cases hAllowed' : D.allowed s a'
    · simp [lawDecisionProblem, lawUtility, hAllowedLaw, hAllowed']
    · have hLe : uBlocked ≤ uAllowed := le_of_lt hGap
      simpa [lawDecisionProblem, lawUtility, hAllowedLaw, hAllowed'] using hLe

/-- Infeasible actions are non-optimal under strict allowed-vs-blocked gap
    whenever at least one feasible action exists. -/
theorem infeasible_not_optimal_of_gap
    (D : UniverseDynamics S A) {uAllowed uBlocked : ℝ}
    (hGap : uBlocked < uAllowed) {s : S}
    (hExists : ∃ a : A, D.allowed s a)
    {a : A} (hNot : ¬ D.allowed s a) :
    a ∉ (lawDecisionProblem D uAllowed uBlocked).Opt s := by
  have hOptEq :
      (lawDecisionProblem D uAllowed uBlocked).Opt s = feasibleActions D s :=
    opt_eq_feasible_of_gap D hGap hExists
  have hNotFeasible : a ∉ feasibleActions D s := by
    simpa [feasibleActions] using hNot
  simpa [hOptEq] using hNotFeasible

/-- Under logical determinism and strict utility gap, the optimal set is a singleton
    (when a feasible action exists). -/
theorem opt_singleton_of_logicallyDeterministic
    (D : UniverseDynamics S A) (hDet : logicallyDeterministic D)
    {uAllowed uBlocked : ℝ} (hGap : uBlocked < uAllowed) {s : S}
    (hExists : ∃ a : A, D.allowed s a) :
    ∃ a : A, (lawDecisionProblem D uAllowed uBlocked).Opt s = ({a} : Set A) := by
  rcases hExists with ⟨a0, ha0⟩
  use a0
  have hOptEq :
      (lawDecisionProblem D uAllowed uBlocked).Opt s = feasibleActions D s :=
    opt_eq_feasible_of_gap D hGap ⟨a0, ha0⟩
  ext a
  constructor
  · intro hIn
    have hFeasible : D.allowed s a := by
      have : a ∈ feasibleActions D s := by simpa [hOptEq] using hIn
      simpa [feasibleActions] using this
    have hEq : a = a0 := hDet s a a0 hFeasible ha0
    simpa [hEq]
  · intro hIn
    have hEq : a = a0 := by simpa using hIn
    subst a
    have hFeasible : a0 ∈ feasibleActions D s := by
      simpa [feasibleActions] using ha0
    simpa [hOptEq] using hFeasible

/-- If two universes induce the same allowed/blocked partition, then for fixed
    law-utility levels they induce the same optimal set at every state
    (under nonempty-feasible assumptions). -/
theorem opt_eq_of_allowed_iff
    {D₁ D₂ : UniverseDynamics S A} {uAllowed uBlocked : ℝ}
    (hEq : ∀ s : S, ∀ a : A, D₁.allowed s a ↔ D₂.allowed s a)
    (hGap : uBlocked < uAllowed)
    (hExists₁ : ∀ s : S, ∃ a : A, D₁.allowed s a) :
    ∀ s : S,
      (lawDecisionProblem D₁ uAllowed uBlocked).Opt s =
        (lawDecisionProblem D₂ uAllowed uBlocked).Opt s := by
  intro s
  have hExists₂ : ∃ a : A, D₂.allowed s a := by
    rcases hExists₁ s with ⟨a, ha⟩
    exact ⟨a, (hEq s a).1 ha⟩
  calc
    (lawDecisionProblem D₁ uAllowed uBlocked).Opt s
        = feasibleActions D₁ s := opt_eq_feasible_of_gap D₁ hGap (hExists₁ s)
    _ = feasibleActions D₂ s := by
      ext a
      simp [feasibleActions, hEq s a]
    _ = (lawDecisionProblem D₂ uAllowed uBlocked).Opt s := by
      symm
      exact opt_eq_feasible_of_gap D₂ hGap hExists₂

end UniverseObjective

end DecisionQuotient
