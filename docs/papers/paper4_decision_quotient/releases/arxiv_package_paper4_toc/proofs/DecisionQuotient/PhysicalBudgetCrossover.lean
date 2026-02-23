/-
  Paper 4: Decision-Relevant Uncertainty

  PhysicalBudgetCrossover.lean

  Regime-typed budget crossover primitives:
  - Explicit-vs-succinct feasibility split at a declared budget
  - Conditional policy consequence under integrity-resource obstruction

  This module deliberately avoids universal recursion/imperative claims.
  It states only budgeted representation facts and conditional closure lemmas.
-/

import Mathlib.Data.Set.Basic
import DecisionQuotient.IntegrityCompetence

namespace DecisionQuotient
namespace PhysicalBudgetCrossover

open Set
open DecisionQuotient.IntegrityCompetence

universe u v w

/-- Budgeted size model for two encodings of the same decision question. -/
structure EncodingSizeModel where
  explicitSize : ℕ → ℕ
  succinctSize : ℕ → ℕ

/-- Explicit encoding infeasible at budget `B` and size parameter `n`. -/
def ExplicitInfeasible (M : EncodingSizeModel) (B n : ℕ) : Prop :=
  B < M.explicitSize n

/-- Succinct encoding feasible at budget `B` and size parameter `n`. -/
def SuccinctFeasible (M : EncodingSizeModel) (B n : ℕ) : Prop :=
  M.succinctSize n ≤ B

/-- Crossover witness at `(B,n)`:
    explicit encoding is infeasible while succinct encoding is feasible. -/
def CrossoverAt (M : EncodingSizeModel) (B n : ℕ) : Prop :=
  ExplicitInfeasible M B n ∧ SuccinctFeasible M B n

/-- A declared budget has a crossover point for this size model. -/
def HasCrossover (M : EncodingSizeModel) (B : ℕ) : Prop :=
  ∃ n : ℕ, CrossoverAt M B n

/-- Global succinct-size cap: succinct representation never exceeds `C`. -/
def SuccinctBoundedBy (M : EncodingSizeModel) (C : ℕ) : Prop :=
  ∀ n : ℕ, M.succinctSize n ≤ C

/-- Explicit-size unboundedness: every budget is eventually exceeded. -/
def ExplicitUnbounded (M : EncodingSizeModel) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < M.explicitSize n

/-- Core split-feasibility lemma: crossover implies infeasible-vs-feasible split. -/
theorem explicit_infeasible_succinct_feasible_of_crossover
    (M : EncodingSizeModel) (B n : ℕ)
    (hCross : CrossoverAt M B n) :
    ExplicitInfeasible M B n ∧ SuccinctFeasible M B n :=
  hCross

/-- Witness form: if crossover is exhibited at `n`, the budget has a crossover. -/
theorem has_crossover_of_witness
    (M : EncodingSizeModel) (B n : ℕ)
    (hCross : CrossoverAt M B n) :
    HasCrossover M B := by
  exact ⟨n, hCross⟩

/-- If succinct size is globally bounded by `C` and explicit size is unbounded,
then any budget `B ≥ C` admits a crossover witness. -/
theorem has_crossover_of_bounded_succinct_unbounded_explicit
    (M : EncodingSizeModel) (C B : ℕ)
    (hSucc : SuccinctBoundedBy M C)
    (hExp : ExplicitUnbounded M)
    (hBudget : C ≤ B) :
    HasCrossover M B := by
  rcases hExp B with ⟨n, hExplicit⟩
  refine ⟨n, ?_⟩
  refine ⟨hExplicit, ?_⟩
  exact le_trans (hSucc n) hBudget

/-- Eventual-budget form of crossover existence above a succinct-size cap. -/
theorem crossover_for_all_budgets_above_cap
    (M : EncodingSizeModel) (C : ℕ)
    (hSucc : SuccinctBoundedBy M C)
    (hExp : ExplicitUnbounded M) :
    ∀ B : ℕ, C ≤ B → HasCrossover M B := by
  intro B hB
  exact has_crossover_of_bounded_succinct_unbounded_explicit M C B hSucc hExp hB

/-- Crossover + hardness-closure bundle:
    representational crossover can coexist with exact-certification obstruction. -/
theorem crossover_hardness_bundle
    (M : EncodingSizeModel) (B n : ℕ)
    {P_eq_coNP ExactCertificationCompetence : Prop}
    (hCross : CrossoverAt M B n)
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : ExactCertificationCompetence → P_eq_coNP) :
    ExplicitInfeasible M B n ∧ SuccinctFeasible M B n ∧ ¬ ExactCertificationCompetence := by
  refine ⟨hCross.1, hCross.2, ?_⟩
  exact integrity_resource_bound (P_eq_coNP := P_eq_coNP)
    (PolytimeUniversalCompetence := ExactCertificationCompetence) hNeq hCollapse

/-- Policy-level closure in solver form:
    under the same collapse assumption used by `integrity_forces_abstention`,
    any integrity-preserving solver must either abstain on some in-scope input
    or violate the declared budget, even when a crossover witness is present. -/
theorem crossover_integrity_policy
    {X : Type u} {Y : Type v} {W : Type w}
    (M : EncodingSizeModel) (B n : ℕ)
    (hCross : CrossoverAt M B n)
    (R : Set (X × Y)) (Γ : Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : (∃ Q : CertifyingSolver X Y W, CompetentOn R Γ Q) → P_eq_coNP)
    (Q : CertifyingSolver X Y W)
    (hIntegrity : SolverIntegrity R Q) :
    ExplicitInfeasible M B n ∧ SuccinctFeasible M B n ∧
      (¬ (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w))
        ∨
       ¬ (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))) := by
  refine ⟨hCross.1, hCross.2, ?_⟩
  exact integrity_forces_abstention (R := R) (Γ := Γ)
    (P_eq_coNP := P_eq_coNP) hNeq hCollapse Q hIntegrity

end PhysicalBudgetCrossover
end DecisionQuotient
