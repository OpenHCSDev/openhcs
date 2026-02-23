import DecisionQuotient.Sufficiency
import Mathlib.Data.Real.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Tactic

namespace DecisionQuotient

namespace ConfigReduction

variable {S B : Type*} {n : ℕ} [CoordinateSpace S n]

/-- Actions for the configuration reduction: observed behaviors plus a sentinel. -/
abbrev ConfigAction (B : Type*) := Option B

/-- Behavioral preservation predicate: agreeing on I preserves behavior occurrence truth values. -/
def behaviorPreserving (occurs : B → S → Prop) (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I → ∀ b : B, occurs b s ↔ occurs b s'

/-- Utility with sentinel action:
    - `some b` gets utility 1 iff behavior `b` occurs.
    - `none` gets utility 1 iff no behavior occurs. -/
noncomputable def configUtility (occurs : B → S → Prop) : ConfigAction B → S → ℝ := by
  classical
  intro a s
  cases a with
  | some b => exact if occurs b s then 1 else 0
  | none => exact if ∃ b : B, occurs b s then 0 else 1

/-- Decision problem induced by the behavior-occurrence model. -/
noncomputable def configDecisionProblem (occurs : B → S → Prop) : DecisionProblem (ConfigAction B) S where
  utility := configUtility occurs

lemma configUtility_le_one (occurs : B → S → Prop) (a : ConfigAction B) (s : S) :
    configUtility occurs a s ≤ 1 := by
  classical
  cases a with
  | none =>
      unfold configUtility
      by_cases hAny : ∃ b : B, occurs b s
      · simp [hAny]
      · simp [hAny]
  | some b =>
      unfold configUtility
      by_cases h : occurs b s
      · simp [h]
      · simp [h]

lemma some_mem_Opt_of_occurs (occurs : B → S → Prop) (b : B) (s : S) (hocc : occurs b s) :
    some b ∈ (configDecisionProblem occurs).Opt s := by
  unfold DecisionProblem.Opt DecisionProblem.isOptimal configDecisionProblem
  intro a'
  have hle : configUtility occurs a' s ≤ 1 := configUtility_le_one occurs a' s
  simpa [configUtility, hocc] using hle

lemma some_not_mem_Opt_of_not_occurs (occurs : B → S → Prop) (b : B) (s : S)
    (hnot : ¬ occurs b s) :
    some b ∉ (configDecisionProblem occurs).Opt s := by
  intro hmem
  have hopt : (configDecisionProblem occurs).isOptimal (some b) s := hmem
  by_cases hAny : ∃ b' : B, occurs b' s
  · rcases hAny with ⟨b', hb'⟩
    have hle := hopt (some b')
    have : (1 : ℝ) ≤ 0 := by
      simpa [configDecisionProblem, configUtility, hb', hnot] using hle
    linarith
  · have hle := hopt none
    have : (1 : ℝ) ≤ 0 := by
      simpa [configDecisionProblem, configUtility, hAny, hnot] using hle
    linarith

/-- In the sentinel reduction, `some b` is optimal iff behavior `b` occurs. -/
theorem some_mem_Opt_iff_occurs (occurs : B → S → Prop) (b : B) (s : S) :
    some b ∈ (configDecisionProblem occurs).Opt s ↔ occurs b s := by
  constructor
  · intro hmem
    by_contra hnot
    exact some_not_mem_Opt_of_not_occurs occurs b s hnot hmem
  · exact some_mem_Opt_of_occurs occurs b s

/-- Sentinel action is optimal iff no behavior occurs. -/
theorem none_mem_Opt_iff_no_occurs (occurs : B → S → Prop) (s : S) :
    none ∈ (configDecisionProblem occurs).Opt s ↔ ¬ ∃ b : B, occurs b s := by
  constructor
  · intro hnone
    intro hAny
    rcases hAny with ⟨b, hb⟩
    have hopt : (configDecisionProblem occurs).isOptimal none s := hnone
    have hle := hopt (some b)
    have hAny' : ∃ b : B, occurs b s := ⟨b, hb⟩
    have : (1 : ℝ) ≤ 0 := by
      simpa [configDecisionProblem, configUtility, hAny', hb] using hle
    linarith
  · intro hNo
    unfold DecisionProblem.Opt DecisionProblem.isOptimal configDecisionProblem
    intro a'
    cases a' with
    | none =>
        simp [configUtility, hNo]
    | some b =>
        have hbnot : ¬ occurs b s := by
          intro hb
          exact hNo ⟨b, hb⟩
        have : configUtility occurs (some b) s ≤ 1 := configUtility_le_one occurs (some b) s
        simpa [configUtility, hNo, hbnot] using this

lemma no_occurs_iff_of_behaviorPreserving
    (occurs : B → S → Prop) (I : Finset (Fin n))
    (hpres : behaviorPreserving occurs I)
    (s s' : S) (hagree : agreeOn s s' I) :
    (¬ ∃ b : B, occurs b s) ↔ (¬ ∃ b : B, occurs b s') := by
  constructor
  · intro hnone hsome'
    rcases hsome' with ⟨b, hb'⟩
    exact hnone ⟨b, (hpres s s' hagree b).2 hb'⟩
  · intro hnone hsome
    rcases hsome with ⟨b, hb⟩
    exact hnone ⟨b, (hpres s s' hagree b).1 hb⟩

/-- Configuration reduction theorem:
    preserving behavior occurrence under projection `I` is equivalent to sufficiency
    for the induced decision problem with sentinel action. -/
theorem config_sufficiency_iff_behavior_preserving
    (occurs : B → S → Prop) (I : Finset (Fin n)) :
    (configDecisionProblem occurs).isSufficient I ↔ behaviorPreserving occurs I := by
  constructor
  · intro hsuff
    intro s s' hagree b
    have hEq : (configDecisionProblem occurs).Opt s = (configDecisionProblem occurs).Opt s' :=
      hsuff s s' hagree
    constructor
    · intro hb
      have hmem : some b ∈ (configDecisionProblem occurs).Opt s :=
        (some_mem_Opt_iff_occurs occurs b s).2 hb
      have hmem' : some b ∈ (configDecisionProblem occurs).Opt s' := by
        simpa [hEq] using hmem
      exact (some_mem_Opt_iff_occurs occurs b s').1 hmem'
    · intro hb'
      have hmem' : some b ∈ (configDecisionProblem occurs).Opt s' :=
        (some_mem_Opt_iff_occurs occurs b s').2 hb'
      have hmem : some b ∈ (configDecisionProblem occurs).Opt s := by
        simpa [hEq] using hmem'
      exact (some_mem_Opt_iff_occurs occurs b s).1 hmem
  · intro hpres
    intro s s' hagree
    ext a
    cases a with
    | some b =>
        constructor
        · intro hmem
          have hb : occurs b s := (some_mem_Opt_iff_occurs occurs b s).1 hmem
          have hb' : occurs b s' := (hpres s s' hagree b).1 hb
          exact (some_mem_Opt_iff_occurs occurs b s').2 hb'
        · intro hmem'
          have hb' : occurs b s' := (some_mem_Opt_iff_occurs occurs b s').1 hmem'
          have hb : occurs b s := (hpres s s' hagree b).2 hb'
          exact (some_mem_Opt_iff_occurs occurs b s).2 hb
    | none =>
        have hNoEq : (¬ ∃ b : B, occurs b s) ↔ (¬ ∃ b : B, occurs b s') :=
          no_occurs_iff_of_behaviorPreserving occurs I hpres s s' hagree
        constructor
        · intro hmem
          have hsNo : ¬ ∃ b : B, occurs b s := (none_mem_Opt_iff_no_occurs occurs s).1 hmem
          have hs'No : ¬ ∃ b : B, occurs b s' := hNoEq.1 hsNo
          exact (none_mem_Opt_iff_no_occurs occurs s').2 hs'No
        · intro hmem'
          have hs'No : ¬ ∃ b : B, occurs b s' := (none_mem_Opt_iff_no_occurs occurs s').1 hmem'
          have hsNo : ¬ ∃ b : B, occurs b s := hNoEq.2 hs'No
          exact (none_mem_Opt_iff_no_occurs occurs s).2 hsNo

end ConfigReduction

end DecisionQuotient
