import DecisionQuotient.Physics.ObserverRelativeState
import DecisionQuotient.StochasticSequential.Quotient
import Mathlib.Tactic

/-!
  Paper 4: Decision-Relevant Uncertainty

  Physics/AnchorChecks.lean

  Observer-collapse anchor-check bridge:
  - stochastic anchor-check simplification to singleton-fiber witnesses,
  - observer-collapse forcing of stochastic sufficiency from one seed witness,
  - observer-collapse forcing of sequential sufficiency from observer-invariant optimal sets,
  - physical-observer specializations.

  No new axioms are introduced.
-/

namespace DecisionQuotient
namespace Physics
namespace AnchorChecks

open ObserverRelativeState
open StochasticSequential

universe u v w

/-- If an observer-effective state space is subsingleton, all physical states are
observer-equivalent under that observer class. -/
theorem obsEquiv_all_of_effective_subsingleton
    {Sphys : Type u} {Sobs : Type v}
    (O : ObserverClass Sphys Sobs)
    [Subsingleton (EffectiveStateSpace O)] :
    ∀ s s' : Sphys, obsEquiv O s s' := by
  intro s s'
  have hProj : project O s = project O s' := Subsingleton.elim _ _
  exact (project_eq_iff O s s').1 hProj

/-- Stochastic anchor sufficiency is equivalent to existence of one anchor fiber
with singleton conditional optimum. The closure clause is implied by
`fiberOpt_of_agreeOn`. -/
theorem stochasticAnchorSufficient_iff_exists_anchor_singleton
    {A S : Type*} {n : ℕ}
    [Fintype A] [Fintype S] [DecidableEq A] [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) :
    StochasticAnchorSufficient P I ↔
      ∃ s₀ : S, ∃ a : A, fiberOpt P I s₀ = ({a} : Set A) := by
  constructor
  · intro h
    rcases h with ⟨s₀, a, ha, _⟩
    exact ⟨s₀, a, ha⟩
  · intro h
    rcases h with ⟨s₀, a, ha⟩
    refine ⟨s₀, a, ha, ?_⟩
    intro s hs
    have hEq : fiberOpt P I s = fiberOpt P I s₀ :=
      StochasticSequential.fiberOpt_of_agreeOn P I s s₀ hs
    simpa [ha] using hEq

/-- Decision-predicate form of stochastic anchor check in singleton-fiber witness
form. -/
theorem stochastic_anchor_check_iff_exists_anchor_singleton
    {A S : Type*} {n : ℕ}
    [Fintype A] [Fintype S] [DecidableEq A] [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) :
    StochasticAnchorSufficiencyCheck P I ↔
      ∃ s₀ : S, ∃ a : A, fiberOpt P I s₀ = ({a} : Set A) := by
  rw [stochastic_anchor_check_iff]
  exact stochasticAnchorSufficient_iff_exists_anchor_singleton P I

/-- Observer collapse + one singleton seed fiber forces stochastic sufficiency:
all states inherit the same singleton conditional optimum. -/
theorem stochastic_sufficient_of_observer_collapse_and_seed
    {A : Type*} {S : Type*} {Sobs : Type*} {n : ℕ}
    [Fintype A] [Fintype S] [DecidableEq A] [CoordinateSpace S n]
    (O : ObserverClass S Sobs)
    [Subsingleton (EffectiveStateSpace O)]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (hObsToAgree : ∀ s s' : S, obsEquiv O s s' → agreeOn s s' I)
    (hSeed : ∃ s₀ : S, ∃ a : A, fiberOpt P I s₀ = ({a} : Set A)) :
    StochasticSufficient P I := by
  rcases hSeed with ⟨s₀, a, ha⟩
  intro s
  have hObs : obsEquiv O s s₀ :=
    obsEquiv_all_of_effective_subsingleton O s s₀
  have hAgree : agreeOn s s₀ I := hObsToAgree s s₀ hObs
  have hEq : fiberOpt P I s = fiberOpt P I s₀ :=
    StochasticSequential.fiberOpt_of_agreeOn P I s s₀ hAgree
  refine ⟨a, ?_⟩
  simpa [ha] using hEq

/-- Observer collapse + one singleton seed fiber yields stochastic anchor-check. -/
theorem stochastic_anchor_check_of_observer_collapse_and_seed
    {A : Type*} {S : Type*} {Sobs : Type*} {n : ℕ}
    [Fintype A] [Fintype S] [DecidableEq A] [CoordinateSpace S n] [Nonempty S]
    (O : ObserverClass S Sobs)
    [Subsingleton (EffectiveStateSpace O)]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n))
    (hObsToAgree : ∀ s s' : S, obsEquiv O s s' → agreeOn s s' I)
    (hSeed : ∃ s₀ : S, ∃ a : A, fiberOpt P I s₀ = ({a} : Set A)) :
    StochasticAnchorSufficiencyCheck P I := by
  rw [stochastic_anchor_check_iff]
  exact StochasticSequential.stochastic_anchor_sufficient_of_stochastic_sufficient P I
    (stochastic_sufficient_of_observer_collapse_and_seed O P I hObsToAgree hSeed)

/-- If the observer-effective state space collapses and optimal sets are
observer-invariant, then sequential sufficiency holds at every coordinate set. -/
theorem sequential_sufficient_of_observer_collapse
    {A : Type*} {S : Type*} {ObsTy : Type*} {Sobs : Type*} {n : ℕ}
    [Fintype A] [Fintype S] [Fintype ObsTy] [DecidableEq A] [CoordinateSpace S n]
    (O : ObserverClass S Sobs)
    [Subsingleton (EffectiveStateSpace O)]
    (P : SequentialDecisionProblem A S ObsTy) (I : Finset (Fin n))
    (hObsInvariant :
      ∀ s s' : S, obsEquiv O s s' →
        P.toDecisionProblem.Opt s = P.toDecisionProblem.Opt s') :
    SequentialSufficient P I := by
  intro s s' _
  have hObs : obsEquiv O s s' :=
    obsEquiv_all_of_effective_subsingleton O s s'
  exact hObsInvariant s s' hObs

/-- Observer collapse + observer-invariant optimal sets imply sequential
anchor-check. -/
theorem sequential_anchor_check_of_observer_collapse
    {A : Type*} {S : Type*} {ObsTy : Type*} {Sobs : Type*} {n : ℕ}
    [Fintype A] [Fintype S] [Fintype ObsTy] [DecidableEq A]
    [CoordinateSpace S n] [Nonempty S]
    (O : ObserverClass S Sobs)
    [Subsingleton (EffectiveStateSpace O)]
    (P : SequentialDecisionProblem A S ObsTy) (I : Finset (Fin n))
    (hObsInvariant :
      ∀ s s' : S, obsEquiv O s s' →
        P.toDecisionProblem.Opt s = P.toDecisionProblem.Opt s') :
    SequentialAnchorSufficiencyCheck P I := by
  rw [sequential_anchor_check_iff]
  exact StochasticSequential.sequential_anchor_sufficient_of_sequential_sufficient P I
    (sequential_sufficient_of_observer_collapse O P I hObsInvariant)

/-- Observer class induced by physical observer semantics. -/
def observerOfPhysicalObserverClass
    {PInst : Type u} {Sobs : Type v}
    (O : PhysicalObserverClass PInst Sobs) : ObserverClass PInst Sobs where
  observe := O.semantics.observe

/-- Physical observer specialization:
subsingleton effective space implies global observer-equivalence on instances. -/
theorem physical_observer_collapse_implies_obsEquiv_all
    {PInst : Type u} {Sobs : Type v}
    (O : PhysicalObserverClass PInst Sobs)
    [Subsingleton (EffectiveStateSpace (observerOfPhysicalObserverClass O))] :
    ∀ p p' : PInst,
      obsEquiv (observerOfPhysicalObserverClass O) p p' :=
  obsEquiv_all_of_effective_subsingleton (observerOfPhysicalObserverClass O)

/-- Physical observer specialization of stochastic anchor-check under observer
collapse and one singleton seed fiber. -/
theorem physical_stochastic_anchor_check_of_observer_collapse_and_seed
    {A : Type*} {PInst : Type*} {Sobs : Type*} {n : ℕ}
    [Fintype A] [Fintype PInst] [DecidableEq A] [CoordinateSpace PInst n] [Nonempty PInst]
    (O : PhysicalObserverClass PInst Sobs)
    [Subsingleton (EffectiveStateSpace (observerOfPhysicalObserverClass O))]
    (P : StochasticDecisionProblem A PInst) (I : Finset (Fin n))
    (hObsToAgree :
      ∀ p p' : PInst,
        obsEquiv (observerOfPhysicalObserverClass O) p p' → agreeOn p p' I)
    (hSeed : ∃ p₀ : PInst, ∃ a : A, fiberOpt P I p₀ = ({a} : Set A)) :
    StochasticAnchorSufficiencyCheck P I :=
  stochastic_anchor_check_of_observer_collapse_and_seed
    (O := observerOfPhysicalObserverClass O)
    (P := P) (I := I) hObsToAgree hSeed

end AnchorChecks
end Physics
end DecisionQuotient
