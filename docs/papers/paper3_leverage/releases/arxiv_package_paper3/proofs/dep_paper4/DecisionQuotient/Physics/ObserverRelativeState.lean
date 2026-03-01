import DecisionQuotient.Physics.ClaimTransport
import Mathlib.Data.Set.Basic

/-!
  ObserverRelativeState.lean

  Observer-relative state-space formalization:
  - physical-instance observations induce equivalence relations,
  - each observer class yields an effective quotient state space,
  - physical-state witness semantics are reused from ClaimTransport.
-/

namespace DecisionQuotient
namespace Physics
namespace ObserverRelativeState

open ClaimTransport

universe u v w

/-- An observer class maps physical states/instances into observable states. -/
structure ObserverClass (Sphys : Type u) (Sobs : Type v) where
  observe : Sphys → Sobs

/-- Two physical states are observer-equivalent iff observations coincide. -/
def obsEquiv
    (O : ObserverClass Sphys Sobs) (s s' : Sphys) : Prop :=
  O.observe s = O.observe s'

theorem obsEquiv_refl (O : ObserverClass Sphys Sobs) (s : Sphys) :
    obsEquiv O s s := rfl

theorem obsEquiv_symm (O : ObserverClass Sphys Sobs) {s s' : Sphys}
    (h : obsEquiv O s s') :
    obsEquiv O s' s := h.symm

theorem obsEquiv_trans (O : ObserverClass Sphys Sobs) {s₁ s₂ s₃ : Sphys}
    (h12 : obsEquiv O s₁ s₂) (h23 : obsEquiv O s₂ s₃) :
    obsEquiv O s₁ s₃ := h12.trans h23

/-- Setoid induced by an observer class. -/
def obsSetoid (O : ObserverClass Sphys Sobs) : Setoid Sphys where
  r := obsEquiv O
  iseqv :=
    ⟨obsEquiv_refl O, (fun h => obsEquiv_symm O h), (fun h1 h2 => obsEquiv_trans O h1 h2)⟩

/-- Effective state space for an observer class (quotient by observational equivalence). -/
def EffectiveStateSpace (O : ObserverClass Sphys Sobs) : Type _ :=
  Quotient (obsSetoid O)

/-- Projection of a physical state to observer-effective state. -/
def project (O : ObserverClass Sphys Sobs) : Sphys → EffectiveStateSpace O :=
  fun s => @Quotient.mk Sphys (obsSetoid O) s

/-- Quotient equality is exactly observer-equivalence. -/
theorem project_eq_iff
    (O : ObserverClass Sphys Sobs) (s s' : Sphys) :
    project O s = project O s' ↔ obsEquiv O s s' := by
  constructor
  · intro h
    exact @Quotient.exact Sphys (obsSetoid O) s s' h
  · intro h
    exact @Quotient.sound Sphys (obsSetoid O) s s' h

/-- Witness form: two observer classes can induce different effective equivalences. -/
theorem observer_relative_equivalence_witness
    {Sobs1 : Type v} {Sobs2 : Type w}
    (O1 : ObserverClass Sphys Sobs1) (O2 : ObserverClass Sphys Sobs2)
    (h : ∃ s s', obsEquiv O1 s s' ∧ ¬ obsEquiv O2 s s') :
    ∃ s s',
      project O1 s = project O1 s' ∧
      project O2 s ≠ project O2 s' := by
  rcases h with ⟨s, s', h1, h2⟩
  refine ⟨s, s', @Quotient.sound Sphys (obsSetoid O1) s s' h1, ?_⟩
  intro hEq
  exact h2 (@Quotient.exact Sphys (obsSetoid O2) s s' hEq)

/-- Physical observer class: observer semantics over physical instances. -/
structure PhysicalObserverClass (PInst : Type u) (Sobs : Type v) where
  semantics : PhysicalStateSemantics PInst Sobs

/-- Observer-class physical state space (states marked physical by that class). -/
abbrev PhysicalStateSpace (O : PhysicalObserverClass PInst Sobs) : Type _ :=
  { s : Sobs // O.semantics.isPhysical s }

/-- Every observer-class physical state has a physical-instance witness. -/
theorem physical_state_space_has_instance_witness
    (O : PhysicalObserverClass PInst Sobs) :
    ∀ s : PhysicalStateSpace O, ∃ p : PInst, O.semantics.observe p = s.1 := by
  intro s
  exact O.semantics.realizable s.1 s.2

/-- Physical observer classes can witness distinct effective spaces on the same
physical-instance domain. -/
theorem physical_observer_relative_effective_space
    {Sobs1 : Type v} {Sobs2 : Type w}
    (O1 : PhysicalObserverClass PInst Sobs1)
    (O2 : PhysicalObserverClass PInst Sobs2)
    (h : ∃ p p',
      O1.semantics.observe p = O1.semantics.observe p' ∧
      O2.semantics.observe p ≠ O2.semantics.observe p') :
    ∃ p p',
      project ({ observe := O1.semantics.observe } : ObserverClass PInst Sobs1) p =
        project ({ observe := O1.semantics.observe } : ObserverClass PInst Sobs1) p' ∧
      project ({ observe := O2.semantics.observe } : ObserverClass PInst Sobs2) p ≠
        project ({ observe := O2.semantics.observe } : ObserverClass PInst Sobs2) p' := by
  rcases h with ⟨p, p', h1, h2⟩
  refine ⟨p, p', @Quotient.sound PInst (obsSetoid ({ observe := O1.semantics.observe } : ObserverClass PInst Sobs1)) p p' h1, ?_⟩
  intro hEq
  exact h2 (@Quotient.exact PInst (obsSetoid ({ observe := O2.semantics.observe } : ObserverClass PInst Sobs2)) p p' hEq)

end ObserverRelativeState
end Physics
end DecisionQuotient
