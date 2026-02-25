/-
  Paper 4: Decision-Relevant Uncertainty

  PhysicalBudgetCrossover.lean

  Regime-typed budget crossover primitives:
  - Explicit-vs-succinct feasibility split at a declared budget
  - Conditional policy consequence under integrity-resource obstruction

  This module deliberately avoids universal recursion/imperative claims.
  It states only budgeted representation facts and conditional closure lemmas.

  ## Triviality Level
  TRIVIAL: This defines budget crossover primitives. The nontrivial work is
  in proving the hardness/competence results that use these primitives.

  ## Dependencies
  - Chain: IntegrityCompetence.lean (definitions) → here
  - Used by: ClaimClosure.lean for budget-aware closure proofs
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Find
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

/-- Succinct encoding infeasible at budget `B` and size parameter `n`. -/
def SuccinctInfeasible (M : EncodingSizeModel) (B n : ℕ) : Prop :=
  B < M.succinctSize n

/-- Succinct-size unboundedness: every budget is eventually exceeded. -/
def SuccinctUnbounded (M : EncodingSizeModel) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < M.succinctSize n

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

/-- Least divergence point at a fixed budget:
if crossover exists, there is a least `ncrit` where it first appears. -/
theorem exists_least_crossover_point
    (M : EncodingSizeModel) (B : ℕ)
    (hCross : HasCrossover M B) :
    ∃ ncrit : ℕ,
      CrossoverAt M B ncrit ∧
      ∀ m : ℕ, m < ncrit → ¬ CrossoverAt M B m := by
  classical
  refine ⟨Nat.find hCross, ?_⟩
  refine ⟨Nat.find_spec hCross, ?_⟩
  intro m hm
  intro hCrossM
  have hle : Nat.find hCross ≤ m := Nat.find_min' hCross hCrossM
  exact (Nat.not_le_of_lt hm) hle

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

/-- Eventual explicit infeasibility from monotone growth and one over-budget witness. -/
theorem explicit_eventual_infeasibility_of_monotone_and_witness
    (M : EncodingSizeModel) (B n₀ : ℕ)
    (hMono : Monotone M.explicitSize)
    (hAt : B < M.explicitSize n₀) :
    ∀ n : ℕ, n ≥ n₀ → ExplicitInfeasible M B n := by
  intro n hn
  exact lt_of_lt_of_le hAt (hMono hn)

/-- Payoff-threshold form:
if after `n₀` explicit is infeasible and succinct is feasible, then every
`n ≥ n₀` is a crossover point. -/
theorem crossover_eventually_of_eventual_split
    (M : EncodingSizeModel) (B n₀ : ℕ)
    (hExpAfter : ∀ n : ℕ, n ≥ n₀ → ExplicitInfeasible M B n)
    (hSuccAfter : ∀ n : ℕ, n ≥ n₀ → SuccinctFeasible M B n) :
    ∀ n : ℕ, n ≥ n₀ → CrossoverAt M B n := by
  intro n hn
  exact ⟨hExpAfter n hn, hSuccAfter n hn⟩

/-- Alias used for prose: the eventual split is exactly the payoff threshold. -/
theorem payoff_threshold_explicit_vs_succinct
    (M : EncodingSizeModel) (B n₀ : ℕ)
    (hExpAfter : ∀ n : ℕ, n ≥ n₀ → ExplicitInfeasible M B n)
    (hSuccAfter : ∀ n : ℕ, n ≥ n₀ → SuccinctFeasible M B n) :
    ∀ n : ℕ, n ≥ n₀ → CrossoverAt M B n :=
  crossover_eventually_of_eventual_split M B n₀ hExpAfter hSuccAfter

/-- Without a succinct bound, there is no universal survivor:
for each fixed budget, both encodings become infeasible at some size. -/
theorem no_universal_survivor_without_succinct_bound
    (M : EncodingSizeModel)
    (hExp : ExplicitUnbounded M)
    (hSucc : SuccinctUnbounded M) :
    ∀ B : ℕ,
      (∃ n : ℕ, ExplicitInfeasible M B n) ∧
      (∃ n : ℕ, SuccinctInfeasible M B n) := by
  intro B
  rcases hExp B with ⟨nE, hE⟩
  rcases hSucc B with ⟨nS, hS⟩
  exact ⟨⟨nE, hE⟩, ⟨nS, hS⟩⟩

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

/-- Named alias: policy closure exactly at the divergence point. -/
theorem policy_closure_at_divergence
    {X : Type u} {Y : Type v} {W : Type w}
    (M : EncodingSizeModel) (B ncrit : ℕ)
    (hCross : CrossoverAt M B ncrit)
    (R : Set (X × Y)) (Γ : Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : (∃ Q : CertifyingSolver X Y W, CompetentOn R Γ Q) → P_eq_coNP)
    (Q : CertifyingSolver X Y W)
    (hIntegrity : SolverIntegrity R Q) :
    ExplicitInfeasible M B ncrit ∧ SuccinctFeasible M B ncrit ∧
      (¬ (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w))
        ∨
       ¬ (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))) :=
  crossover_integrity_policy M B ncrit hCross R Γ hNeq hCollapse Q hIntegrity

/-- If a crossover split holds for all `n ≥ n₀`, policy closure holds for all
such `n` under the same integrity-resource collapse assumption. -/
theorem policy_closure_beyond_divergence
    {X : Type u} {Y : Type v} {W : Type w}
    (M : EncodingSizeModel) (B n₀ : ℕ)
    (hCrossAfter : ∀ n : ℕ, n ≥ n₀ → CrossoverAt M B n)
    (R : Set (X × Y)) (Γ : Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : (∃ Q : CertifyingSolver X Y W, CompetentOn R Γ Q) → P_eq_coNP)
    (Q : CertifyingSolver X Y W)
    (hIntegrity : SolverIntegrity R Q) :
    ∀ n : ℕ, n ≥ n₀ →
      ExplicitInfeasible M B n ∧ SuccinctFeasible M B n ∧
        (¬ (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w))
          ∨
         ¬ (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))) := by
  intro n hn
  exact crossover_integrity_policy M B n (hCrossAfter n hn) R Γ hNeq hCollapse Q hIntegrity

end PhysicalBudgetCrossover
end DecisionQuotient
