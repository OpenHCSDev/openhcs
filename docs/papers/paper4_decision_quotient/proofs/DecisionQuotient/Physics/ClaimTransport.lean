import DecisionQuotient.Basic
import DecisionQuotient.UniverseObjective
import DecisionQuotient.Hardness.ConfigReduction
import DecisionQuotient.HardnessDistribution
import Mathlib.Tactic

/-!
# Physical Claim Transport

This module formalizes a bridge principle used across the paper:
if a physical family is encoded into the core decision model, then theorem-level
core claims transfer to that physical family under explicit encoding assumptions.
-/

namespace DecisionQuotient
namespace Physics
namespace ClaimTransport

universe u v w

/-- A physical-to-core encoding map into decision problems. -/
structure PhysicalEncoding (PInst : Type u) (A : Type v) (S : Type w) where
  encode : PInst → DecisionProblem A S

/-- Conditional claim transport:
core theorem + physical-to-core assumption transfer gives a physical theorem. -/
theorem physical_claim_lifts_from_core_conditional
    {PInst : Type u} {A : Type v} {S : Type w}
    (E : PhysicalEncoding PInst A S)
    (CoreAssm : DecisionProblem A S → Prop)
    (CoreClaim : DecisionProblem A S → Prop)
    (PhysAssm : PInst → Prop)
    (hCore : ∀ d : DecisionProblem A S, CoreAssm d → CoreClaim d)
    (hAssmTransfer : ∀ p : PInst, PhysAssm p → CoreAssm (E.encode p)) :
    ∀ p : PInst, PhysAssm p → CoreClaim (E.encode p) := by
  intro p hp
  exact hCore (E.encode p) (hAssmTransfer p hp)

/-- Unconditional claim transport for universally quantified core claims. -/
theorem physical_claim_lifts_from_core
    {PInst : Type u} {A : Type v} {S : Type w}
    (E : PhysicalEncoding PInst A S)
    (CoreClaim : DecisionProblem A S → Prop)
    (hCore : ∀ d : DecisionProblem A S, CoreClaim d) :
    ∀ p : PInst, CoreClaim (E.encode p) := by
  intro p
  exact hCore (E.encode p)

/-- Any encoded physical counterexample is a core counterexample (on the encoded slice). -/
theorem physical_counterexample_yields_core_counterexample
    {PInst : Type u} {A : Type v} {S : Type w}
    (E : PhysicalEncoding PInst A S)
    (PhysAssm : PInst → Prop)
    (CoreClaim : DecisionProblem A S → Prop) :
    (∃ p : PInst, PhysAssm p ∧ ¬ CoreClaim (E.encode p)) →
      ∃ d : DecisionProblem A S, CoreClaim d → False := by
  intro h
  rcases h with ⟨p, _, hNot⟩
  exact ⟨E.encode p, hNot⟩

/-- Core theorem on encoded slice rules out physical counterexamples. -/
theorem no_physical_counterexample_of_core_theorem
    {PInst : Type u} {A : Type v} {S : Type w}
    (E : PhysicalEncoding PInst A S)
    (PhysAssm : PInst → Prop)
    (CoreClaim : DecisionProblem A S → Prop)
    (hLifted : ∀ p : PInst, PhysAssm p → CoreClaim (E.encode p)) :
    ¬ ∃ p : PInst, PhysAssm p ∧ ¬ CoreClaim (E.encode p) := by
  intro h
  rcases h with ⟨p, hp, hNot⟩
  exact hNot (hLifted p hp)

/-- Failure direction:
if a physical counterexample exists on the encoded slice and physical assumptions
transfer into the core assumptions, then the purported core rule is false. -/
theorem physical_counterexample_invalidates_core_rule
    {PInst : Type u} {A : Type v} {S : Type w}
    (E : PhysicalEncoding PInst A S)
    (CoreAssm : DecisionProblem A S → Prop)
    (CoreClaim : DecisionProblem A S → Prop)
    (PhysAssm : PInst → Prop)
    (hAssmTransfer : ∀ p : PInst, PhysAssm p → CoreAssm (E.encode p))
    (hCounter : ∃ p : PInst, PhysAssm p ∧ ¬ CoreClaim (E.encode p)) :
    ¬ (∀ d : DecisionProblem A S, CoreAssm d → CoreClaim d) := by
  intro hCoreRule
  rcases hCounter with ⟨p, hp, hNotClaim⟩
  exact hNotClaim (hCoreRule (E.encode p) (hAssmTransfer p hp))

/-! ## Concrete law-induced physical encoding -/

structure LawGapInstance (S : Type u) (A : Type v) where
  dynamics : UniverseDynamics S A
  uAllowed : ℝ
  uBlocked : ℝ
  state : S
  hGap : uBlocked < uAllowed
  hExists : ∃ a : A, dynamics.allowed state a

/-- Encoding from a law-level physical instance to a core decision problem. -/
noncomputable def lawGapEncoding {S : Type u} {A : Type v} :
    PhysicalEncoding (LawGapInstance S A) A S where
  encode x := lawDecisionProblem x.dynamics x.uAllowed x.uBlocked

/-- Physical-side claim for a law-level instance: optimizer equals feasible set. -/
def lawGapPhysicalClaim {S : Type u} {A : Type v} (x : LawGapInstance S A) : Prop :=
  (lawGapEncoding.encode x).Opt x.state = feasibleActions x.dynamics x.state

/-- This law-level physical claim is theorem-level provable in the core model. -/
theorem law_gap_physical_claim_holds
    {S : Type u} {A : Type v}
    (x : LawGapInstance S A) :
    lawGapPhysicalClaim x := by
  exact opt_eq_feasible_of_gap x.dynamics x.hGap x.hExists

/-- No counterexample exists for the law-gap claim over encoded physical instances. -/
theorem no_law_gap_counterexample
    {S : Type u} {A : Type v} :
    ¬ ∃ x : LawGapInstance S A, ¬ lawGapPhysicalClaim x := by
  intro h
  rcases h with ⟨x, hx⟩
  exact hx (law_gap_physical_claim_holds x)

/-! ## Cross-section bridge bundle -/

/-- Bundled physical bridge theorem:
    combines law-induced objective semantics, behavior-preservation reduction,
    and irreducible required-work lower bound. -/
theorem physical_bridge_bundle
    {S : Type u} {A : Type v} {B : Type w} {n : ℕ}
    [CoordinateSpace S n]
    (x : LawGapInstance S A)
    (occurs : B → S → Prop)
    (I : Finset (Fin n))
    (P : HardnessDistribution.SpecificationProblem)
    (Arch : HardnessDistribution.SolutionArchitecture P)
    (siteCount : ℕ)
    (hSites : siteCount ≥ 1) :
    lawGapPhysicalClaim x ∧
      (ConfigReduction.behaviorPreserving occurs I ↔
        (ConfigReduction.configDecisionProblem occurs).isSufficient I) ∧
      HardnessDistribution.hardnessLowerBound P ≤
        HardnessDistribution.requiredWork Arch siteCount := by
  constructor
  · exact law_gap_physical_claim_holds x
  constructor
  · simpa using
      (ConfigReduction.config_sufficiency_iff_behavior_preserving (occurs := occurs) I).symm
  · exact HardnessDistribution.hardness_is_irreducible_required_work P Arch siteCount hSites

end ClaimTransport
end Physics
end DecisionQuotient
