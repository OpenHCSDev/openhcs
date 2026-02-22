/-
  Paper 4: Decision Quotient

  IntegrityCompetence.lean

  Formalizes the Foundations-section split between:
  - Solver integrity (sound certified assertions)
  - Regime competence (integrity + non-abstaining coverage + resource bound)

  LaTeX references:
  - Definition: certifying solver / solver integrity / competence under regime
  - Proposition: Integrity--Competence Separation
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace DecisionQuotient.IntegrityCompetence

open Set

universe u v w

variable {X : Type u} {Y : Type v} {W : Type w}

/-- Regime tuple used by competence claims:
    in-scope instances, encoding length, and resource budget. -/
structure Regime (X : Type u) where
  inScope : Set X
  encLen : X → ℕ
  budget : ℕ → ℕ

/-- Certifying solver: may abstain, otherwise emits candidate output + witness,
    together with a checker and solve-side cost function. -/
structure CertifyingSolver (X : Type u) (Y : Type v) (W : Type w) where
  solve : X → Option (Y × W)
  check : X → Y → W → Prop
  solveCost : X → ℕ

/-- Solver integrity:
    1. Any asserted output must pass the checker.
    2. Any checker-accepted claim is semantically correct. -/
def SolverIntegrity (R : Set (X × Y)) (Q : CertifyingSolver X Y W) : Prop :=
  (∀ x y w, Q.solve x = some (y, w) → Q.check x y w) ∧
  (∀ x y w, Q.check x y w → (x, y) ∈ R)

/-- Competence under a declared regime:
    integrity + non-abstaining coverage on in-scope instances + solve-side budget. -/
def CompetentOn (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W) : Prop :=
  SolverIntegrity R Q ∧
  (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w)) ∧
  (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))

/-- ε-typed objective family:
    for each tolerance ε, `Rε ε` is the certified target relation. -/
abbrev EpsilonRelation (X : Type u) (Y : Type v) := ℝ → Set (X × Y)

/-- ε-competence under a declared regime:
    competence for the ε-indexed target relation. -/
def EpsilonCompetentOn
    (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) : Prop :=
  CompetentOn (Rε ε) Γ Q

/-- Competence implies integrity by definition. -/
theorem competence_implies_integrity
    (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    CompetentOn R Γ Q → SolverIntegrity R Q := by
  intro h
  exact h.1

/-- ε-competence implies integrity for the ε-indexed relation. -/
theorem epsilon_competence_implies_integrity
    (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    EpsilonCompetentOn Rε ε Γ Q → SolverIntegrity (Rε ε) Q := by
  intro h
  exact competence_implies_integrity (R := Rε ε) (Γ := Γ) (Q := Q) h

/-- Zero-ε reduction at the competence level:
    if `Rε 0` is the exact relation `R`, ε-competence at ε=0 is exactly competence on `R`. -/
theorem zero_epsilon_competence_iff_exact
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (h0 : Rε 0 = R) (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    EpsilonCompetentOn Rε 0 Γ Q ↔ CompetentOn R Γ Q := by
  simpa [EpsilonCompetentOn, h0]

/-- A canonical integrity-preserving abstaining solver:
    - Always abstains
    - Checker always rejects
    - Zero solve-side cost
-/
def alwaysAbstain : CertifyingSolver X Y W where
  solve := fun _ => none
  check := fun _ _ _ => False
  solveCost := fun _ => 0

/-- Always-abstain solver satisfies integrity for any target relation. -/
theorem alwaysAbstain_integrity (R : Set (X × Y)) :
    SolverIntegrity R (alwaysAbstain (X := X) (Y := Y) (W := W)) := by
  constructor
  · intro x y w h
    simp [alwaysAbstain] at h
  · intro x y w h
    simp [alwaysAbstain] at h

/-- Competence entails non-abstaining coverage on in-scope instances. -/
theorem competent_has_coverage
    (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (hComp : CompetentOn R Γ Q) :
    ∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w) :=
  hComp.2.1

/-- Integrity does not imply competence on any nonempty scope:
    an always-abstain solver is integrity-preserving but not competent. -/
theorem integrity_not_competent_of_nonempty_scope
    (R : Set (X × Y)) (Γ : Regime X) (hScope : Γ.inScope.Nonempty) :
    ∃ Q : CertifyingSolver X Y W, SolverIntegrity R Q ∧ ¬ CompetentOn R Γ Q := by
  refine ⟨alwaysAbstain (X := X) (Y := Y) (W := W), alwaysAbstain_integrity (R := R), ?_⟩
  intro hComp
  rcases hScope with ⟨x, hx⟩
  rcases competent_has_coverage (R := R) (Γ := Γ)
      (Q := alwaysAbstain (X := X) (Y := Y) (W := W)) hComp x hx with ⟨y, w, hSolve⟩
  simp [alwaysAbstain] at hSolve

/-!
  Integrity-resource closure (conditional pattern):
  if universal competence would force a complexity collapse, then under
  non-collapse universal competence is impossible.
-/

/-- Integrity-Resource Bound (logical core): if universal competence implies
    a complexity collapse, then under non-collapse no universal competence
    predicate can hold. -/
theorem integrity_resource_bound
    {P_eq_coNP PolytimeUniversalCompetence : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : PolytimeUniversalCompetence → P_eq_coNP) :
    ¬ PolytimeUniversalCompetence := by
  intro hPoly
  exact hNeq (hCollapse hPoly)

/-- Integrity forces abstention or budget violation under the same
    integrity-resource obstruction:
    for any integrity-preserving solver, full in-scope coverage and declared
    budget compliance cannot both hold. -/
theorem integrity_forces_abstention
    (R : Set (X × Y)) (Γ : Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : (∃ Q : CertifyingSolver X Y W, CompetentOn R Γ Q) → P_eq_coNP) :
    ∀ Q : CertifyingSolver X Y W, SolverIntegrity R Q →
      ¬ (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w))
      ∨
      ¬ (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x)) := by
  classical
  intro Q hIntegrity
  by_contra hFail
  have hCoverage :
      ∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w) := by
    by_contra hNoCoverage
    exact hFail (Or.inl hNoCoverage)
  have hBudget :
      ∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x) := by
    by_contra hNoBudget
    exact hFail (Or.inr hNoBudget)
  have hComp : CompetentOn R Γ Q := ⟨hIntegrity, hCoverage, hBudget⟩
  have hCollapseWitness : P_eq_coNP := hCollapse ⟨Q, hComp⟩
  exact hNeq hCollapseWitness

/-- Three-way policy verdict used for the attempted-competence matrix:
    rational (conditionally justified), irrational, or inadmissible. -/
inductive OverModelVerdict where
  | rational
  | irrational
  | inadmissible
  deriving DecidableEq, Repr

/-- Attempted-competence matrix decision function.
    Axes:
    - integrity: whether assertions are integrity-preserving
    - attempted: whether exact competence was actually attempted
    - competenceAvailable: whether exact competence is available in the active regime
-/
def overModelVerdict (integrity attempted competenceAvailable : Bool) : OverModelVerdict :=
  if integrity then
    if attempted && (!competenceAvailable) then OverModelVerdict.rational
    else OverModelVerdict.irrational
  else OverModelVerdict.inadmissible

/-- Rational cell characterization for the attempted-competence matrix. -/
theorem overModelVerdict_rational_iff (integrity attempted competenceAvailable : Bool) :
    overModelVerdict integrity attempted competenceAvailable = OverModelVerdict.rational ↔
      integrity = true ∧ attempted = true ∧ competenceAvailable = false := by
  cases integrity <;> cases attempted <;> cases competenceAvailable <;> decide

/-- Irrational cell characterization for the attempted-competence matrix. -/
theorem overModelVerdict_irrational_iff (integrity attempted competenceAvailable : Bool) :
    overModelVerdict integrity attempted competenceAvailable = OverModelVerdict.irrational ↔
      integrity = true ∧ (attempted = false ∨ competenceAvailable = true) := by
  cases integrity <;> cases attempted <;> cases competenceAvailable <;> decide

/-- Inadmissible cell characterization for the attempted-competence matrix. -/
theorem overModelVerdict_inadmissible_iff (integrity attempted competenceAvailable : Bool) :
    overModelVerdict integrity attempted competenceAvailable = OverModelVerdict.inadmissible ↔
      integrity = false := by
  cases integrity <;> cases attempted <;> cases competenceAvailable <;> decide

/-- Number of rational cells in the integrity-preserving plane
    (integrity fixed to true, axes: attempted × competenceAvailable). -/
def admissibleRationalCount : Nat :=
  (((Finset.univ : Finset Bool).product (Finset.univ : Finset Bool)).filter
    (fun p => overModelVerdict true p.1 p.2 = OverModelVerdict.rational)).card

/-- Number of irrational cells in the integrity-preserving plane
    (integrity fixed to true, axes: attempted × competenceAvailable). -/
def admissibleIrrationalCount : Nat :=
  (((Finset.univ : Finset Bool).product (Finset.univ : Finset Bool)).filter
    (fun p => overModelVerdict true p.1 p.2 = OverModelVerdict.irrational)).card

/-- Count theorem for the integrity-preserving attempted-competence matrix:
    exactly one rational cell and three irrational cells. -/
theorem admissible_matrix_counts :
    admissibleRationalCount = 1 ∧ admissibleIrrationalCount = 3 := by
  native_decide

/-- In the integrity-preserving plane, irrational cells strictly outnumber rational cells. -/
theorem admissible_irrational_strictly_more_than_rational :
    admissibleIrrationalCount > admissibleRationalCount := by
  native_decide

end DecisionQuotient.IntegrityCompetence
