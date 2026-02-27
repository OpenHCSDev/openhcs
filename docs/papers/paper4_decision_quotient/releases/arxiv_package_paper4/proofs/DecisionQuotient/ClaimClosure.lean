/-
  Paper 4: Decision-Relevant Uncertainty

  ClaimClosure.lean - Closure of paper-level claim steps

  This module mechanizes paper-specific claims that were previously
  prose-only or partially mechanized composition steps:
  - Sufficiency characterization via projected optimal-set cover
  - ADQ ordering monotonicity
  - One-step deterministic bridge
  - Over-modeling diagnostic contrapositive (in the Boolean model)
  - Conditional no-auto-minimization corollary logic

  ## Triviality Level
  NONTRIVIAL: This composes the core hardness results into paper-level claims.
  It takes individual proofs and shows how they combine to establish
  the paper's main theses.

  ## Dependencies
  - Depends on: Sufficiency, Instances, Computation, Reduction, QueryComplexity
  - Used by: PhysicalHardness.lean (physics translation)
-/

import DecisionQuotient.Sufficiency
import DecisionQuotient.Instances
import DecisionQuotient.Computation
import DecisionQuotient.Reduction
import DecisionQuotient.Reduction_AllCoords
import DecisionQuotient.QueryComplexity
import DecisionQuotient.Hardness.Sigma2PHardness
import DecisionQuotient.Hardness.Sigma2PExhaustive.AnchorSufficiency
import DecisionQuotient.HardnessDistribution
import DecisionQuotient.IntegrityCompetence
import DecisionQuotient.PhysicalBudgetCrossover
import DecisionQuotient.ThermodynamicLift
import DecisionQuotient.Tractability.BoundedActions
import DecisionQuotient.Tractability.SeparableUtility
import DecisionQuotient.Tractability.TreeStructure
import DecisionQuotient.Physics.DiscreteSpacetime
import DecisionQuotient.Physics.DecisionEquivalence
import DecisionQuotient.Physics.IntegrityEquilibrium
import DecisionQuotient.Physics.MolecularIntegrity
import DecisionQuotient.BayesFromDQ  -- Replaced BayesianDQ with rigorous derivation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace DecisionQuotient
namespace ClaimClosure

open scoped Finset

/-! ## Shared coordinate lemmas -/

lemma agreeOn_refl {S : Type*} {n : ℕ} [CoordinateSpace S n]
    (s : S) (I : Finset (Fin n)) :
    agreeOn s s I := by
  intro i hi
  rfl

lemma agreeOn_symm {S : Type*} {n : ℕ} [CoordinateSpace S n]
    {s s' : S} {I : Finset (Fin n)} :
    agreeOn s s' I → agreeOn s' s I := by
  intro h i hi
  exact (h i hi).symm

lemma agreeOn_trans {S : Type*} {n : ℕ} [CoordinateSpace S n]
    {s₁ s₂ s₃ : S} {I : Finset (Fin n)} :
    agreeOn s₁ s₂ I → agreeOn s₂ s₃ I → agreeOn s₁ s₃ I := by
  intro h12 h23 i hi
  exact (h12 i hi).trans (h23 i hi)

/-! ## Bounded-slice irrelevance of a meta-coordinate -/

section BoundedHorizonIrrelevance

variable {A S : Type*} {n : ℕ}
variable [CoordinateSpace S n]

/-- Relevance restricted to a declared state slice. -/
def isRelevantOn
    (dp : DecisionProblem A S) (Scope : Set S) (i : Fin n) : Prop :=
  ∃ s s' : S,
    s ∈ Scope ∧
    s' ∈ Scope ∧
    (∀ j : Fin n, j ≠ i → CoordinateSpace.proj s j = CoordinateSpace.proj s' j) ∧
    dp.Opt s ≠ dp.Opt s'

/-- Irrelevance restricted to a declared state slice. -/
def isIrrelevantOn
    (dp : DecisionProblem A S) (Scope : Set S) (i : Fin n) : Prop :=
  ∀ s s' : S,
    s ∈ Scope →
    s' ∈ Scope →
    (∀ j : Fin n, j ≠ i → CoordinateSpace.proj s j = CoordinateSpace.proj s' j) →
    dp.Opt s = dp.Opt s'

/-- Any declared budget/horizon cut induces a formal in-scope state slice. -/
def declaredBudgetSlice
    (Γ : IntegrityCompetence.Regime S) (H : ℕ) : Set S :=
  { s | s ∈ Γ.inScope ∧ Γ.encLen s ≤ H }

/-- Slice-level irrelevance excludes slice-level relevance. -/
theorem irrelevantOn_implies_not_relevantOn
    (dp : DecisionProblem A S) (Scope : Set S) (i : Fin n) :
    isIrrelevantOn dp Scope i → ¬ isRelevantOn dp Scope i := by
  intro hIrr hRel
  rcases hRel with ⟨s, s', hs, hs', hAgree, hNe⟩
  exact hNe (hIrr s s' hs hs' hAgree)

/-- If optimizer sets are invariant to coordinate `iInf` on the declared slice,
then `iInf` is irrelevant for that declared task slice. -/
theorem meta_coordinate_irrelevant_of_invariance_on_declared_slice
    (dp : DecisionProblem A S)
    (Γ : IntegrityCompetence.Regime S) (H : ℕ) (iInf : Fin n)
    (hInv :
      ∀ s s' : S,
        s ∈ declaredBudgetSlice Γ H →
        s' ∈ declaredBudgetSlice Γ H →
        (∀ j : Fin n, j ≠ iInf → CoordinateSpace.proj s j = CoordinateSpace.proj s' j) →
        dp.Opt s = dp.Opt s') :
    isIrrelevantOn dp (declaredBudgetSlice Γ H) iInf := by
  exact hInv

/-- Declared-slice invariance implies non-relevance of the meta-coordinate. -/
theorem meta_coordinate_not_relevant_on_declared_slice
    (dp : DecisionProblem A S)
    (Γ : IntegrityCompetence.Regime S) (H : ℕ) (iInf : Fin n)
    (hInv :
      ∀ s s' : S,
        s ∈ declaredBudgetSlice Γ H →
        s' ∈ declaredBudgetSlice Γ H →
        (∀ j : Fin n, j ≠ iInf → CoordinateSpace.proj s j = CoordinateSpace.proj s' j) →
        dp.Opt s = dp.Opt s') :
    ¬ isRelevantOn dp (declaredBudgetSlice Γ H) iInf := by
  exact (irrelevantOn_implies_not_relevantOn (dp := dp) (Scope := declaredBudgetSlice Γ H) (i := iInf))
    (meta_coordinate_irrelevant_of_invariance_on_declared_slice
      (dp := dp) (Γ := Γ) (H := H) (iInf := iInf) hInv)

end BoundedHorizonIrrelevance

/-! ## Proposition `prop:sufficiency-char` (finite-model mechanization) -/

section SufficiencyCharacterization

variable {A S : Type*} {n : ℕ}
variable [Fintype A] [Fintype S] [DecidableEq A]
variable [CoordinateSpace S n]

/-- Finite optimal-action set at a state. -/
noncomputable def optFinset (dp : DecisionProblem A S) (s : S) : Finset A :=
  by
    classical
    exact Finset.univ.filter (fun a => a ∈ dp.Opt s)

/-- States that agree with `s` on coordinates `I`. -/
noncomputable def compatibleStates (I : Finset (Fin n)) (s : S) : Finset S :=
  by
    classical
    exact Finset.univ.filter (fun s' => agreeOn s s' I)

/-- Union of optimal-action sets over the projection class of `s` under `I`. -/
noncomputable def projectedOptCover (dp : DecisionProblem A S) (I : Finset (Fin n))
    (s : S) : Finset A :=
  (compatibleStates (n := n) I s).biUnion (fun s' => optFinset dp s')

/-- Decision quotient induced by coordinate set `I` at state `s` (finite model). -/
noncomputable def dqProjection (dp : DecisionProblem A S) (I : Finset (Fin n))
    (s : S) : ℚ :=
  (projectedOptCover (n := n) dp I s).card / (Fintype.card A : ℚ)

/-- Baseline quotient value from the exact optimal set at `s`. -/
noncomputable def dqExact (dp : DecisionProblem A S) (s : S) : ℚ :=
  (optFinset dp s).card / (Fintype.card A : ℚ)

lemma mem_compatibleStates_iff (I : Finset (Fin n)) (s t : S) :
    t ∈ compatibleStates (n := n) I s ↔ agreeOn s t I := by
  classical
  simp [compatibleStates]

omit [Fintype S] [DecidableEq A] in
lemma mem_optFinset_iff (dp : DecisionProblem A S) (s : S) (a : A) :
    a ∈ optFinset dp s ↔ a ∈ dp.Opt s := by
  classical
  simp [optFinset]

lemma optFinset_subset_projectedOptCover (dp : DecisionProblem A S)
    (I : Finset (Fin n)) (s : S) :
    optFinset dp s ⊆ projectedOptCover (n := n) dp I s := by
  intro a ha
  have hs : s ∈ compatibleStates (n := n) I s :=
    (mem_compatibleStates_iff (n := n) I s s).2 (agreeOn_refl (n := n) s I)
  exact Finset.mem_biUnion.mpr ⟨s, hs, ha⟩

/-- If `I` is sufficient, the projected cover equals the exact optimal set at every state. -/
theorem projectedOptCover_eq_opt_of_sufficient (dp : DecisionProblem A S)
    (I : Finset (Fin n)) (hI : dp.isSufficient I) :
    ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s := by
  intro s
  apply Finset.ext
  intro a
  constructor
  · intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨s', hs', ha'⟩
    have hsAgree : agreeOn s s' I :=
      (mem_compatibleStates_iff (n := n) I s s').1 hs'
    have hOptEq : dp.Opt s' = dp.Opt s :=
      hI s' s ((agreeOn_symm (n := n)) hsAgree)
    have haOptS' : a ∈ dp.Opt s := by
      have haOptS'Raw : a ∈ dp.Opt s' := (mem_optFinset_iff dp s' a).1 ha'
      simpa [hOptEq] using haOptS'Raw
    exact (mem_optFinset_iff dp s a).2 haOptS'
  · intro ha
    have hs : s ∈ compatibleStates (n := n) I s :=
      (mem_compatibleStates_iff (n := n) I s s).2 (agreeOn_refl (n := n) s I)
    exact Finset.mem_biUnion.mpr ⟨s, hs, ha⟩

/-- Converse direction: classwise projected-cover equality implies sufficiency. -/
theorem sufficient_of_projectedOptCover_eq_opt (dp : DecisionProblem A S)
    (I : Finset (Fin n))
    (hCover : ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s) :
    dp.isSufficient I := by
  intro s s' hss'
  have hClassEq : compatibleStates (n := n) I s = compatibleStates (n := n) I s' := by
    apply Finset.ext
    intro t
    constructor
    · intro ht
      have hst : agreeOn s t I :=
        (mem_compatibleStates_iff (n := n) I s t).1 ht
      have hs't : agreeOn s' t I :=
        agreeOn_trans (n := n) ((agreeOn_symm (n := n)) hss') hst
      exact (mem_compatibleStates_iff (n := n) I s' t).2 hs't
    · intro ht
      have hs't : agreeOn s' t I :=
        (mem_compatibleStates_iff (n := n) I s' t).1 ht
      have hst : agreeOn s t I :=
        agreeOn_trans (n := n) hss' hs't
      exact (mem_compatibleStates_iff (n := n) I s t).2 hst
  have hCoverEq : projectedOptCover (n := n) dp I s = projectedOptCover (n := n) dp I s' := by
    simp [projectedOptCover, hClassEq]
  have hOptFinEq : optFinset dp s = optFinset dp s' := by
    calc
      optFinset dp s = projectedOptCover (n := n) dp I s := (hCover s).symm
      _ = projectedOptCover (n := n) dp I s' := hCoverEq
      _ = optFinset dp s' := hCover s'
  ext a
  constructor
  · intro ha
    have haf : a ∈ optFinset dp s := (mem_optFinset_iff dp s a).2 ha
    have haf' : a ∈ optFinset dp s' := by simpa [hOptFinEq] using haf
    exact (mem_optFinset_iff dp s' a).1 haf'
  · intro ha
    have haf : a ∈ optFinset dp s' := (mem_optFinset_iff dp s' a).2 ha
    have haf' : a ∈ optFinset dp s := by simpa [hOptFinEq] using haf
    exact (mem_optFinset_iff dp s a).1 haf'

/-- Finite-model equivalence used for Proposition `prop:sufficiency-char`. -/
theorem sufficiency_iff_projectedOptCover_eq_opt (dp : DecisionProblem A S)
    (I : Finset (Fin n)) :
    dp.isSufficient I ↔
      ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s := by
  constructor
  · exact projectedOptCover_eq_opt_of_sufficient (n := n) dp I
  · exact sufficient_of_projectedOptCover_eq_opt (n := n) dp I

/-- Quotient-ratio form (with nonempty actions) matching the paper statement. -/
theorem sufficiency_iff_dq_ratio (dp : DecisionProblem A S)
    [Nonempty A] (I : Finset (Fin n)) :
    dp.isSufficient I ↔ ∀ s : S, dqProjection (n := n) dp I s = dqExact dp s := by
  constructor
  · intro hI s
    have hEq := projectedOptCover_eq_opt_of_sufficient (n := n) dp I hI s
    simp [dqProjection, dqExact, hEq]
  · intro hRatio
    have hAq : (Fintype.card A : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card A))
    have hCover : ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s := by
      intro s
      have hq := hRatio s
      have hmul := congrArg (fun x : ℚ => x * (Fintype.card A : ℚ)) hq
      have hcardQ : ((projectedOptCover (n := n) dp I s).card : ℚ) = ((optFinset dp s).card : ℚ) := by
        simpa [dqProjection, dqExact, hAq] using hmul
      have hcard : (projectedOptCover (n := n) dp I s).card = (optFinset dp s).card := by
        exact_mod_cast hcardQ
      have hsub : optFinset dp s ⊆ projectedOptCover (n := n) dp I s :=
        optFinset_subset_projectedOptCover (n := n) dp I s
      have hcardle : (projectedOptCover (n := n) dp I s).card ≤ (optFinset dp s).card := by
        simp [hcard]
      have hEqSub : optFinset dp s = projectedOptCover (n := n) dp I s :=
        Finset.eq_of_subset_of_card_le hsub hcardle
      exact hEqSub.symm
    exact sufficient_of_projectedOptCover_eq_opt (n := n) dp I hCover

end SufficiencyCharacterization

/-! ## Proposition `prop:adq-ordering` -/

section ADQOrdering

variable {B : Type*}

/-- Finite-model ADQ value over a behavior universe `U` and achievable set `X`. -/
noncomputable def adq (U X : Finset B) : ℚ :=
  (X.card : ℚ) / (U.card : ℚ)

/-- If ADQ is strictly smaller against the same nonempty denominator,
then achievable-cardinality is strictly smaller. -/
theorem adq_ordering
    (U X Y : Finset B) (hU : 0 < U.card)
    (hLt : adq U X < adq U Y) :
    X.card < Y.card := by
  have hUq : (0 : ℚ) < (U.card : ℚ) := by
    exact_mod_cast hU
  have hCardQ : (X.card : ℚ) < (Y.card : ℚ) := by
    exact (div_lt_div_iff_of_pos_right hUq).mp hLt
  exact_mod_cast hCardQ

end ADQOrdering

/-! ## Proposition `prop:one-step-bridge` -/

section OneStepBridge

variable {A S : Type*}

/-- One-step deterministic sequential regime (bridge fragment). -/
structure OneStepSequentialObjective where
  reward : A → S → ℝ

/-- One-step optimizer set. -/
def OneStepSequentialObjective.Opt (R : OneStepSequentialObjective (A := A) (S := S))
    (s : S) : Set A :=
  { a : A | ∀ a' : A, R.reward a' s ≤ R.reward a s }

/-- Induced static decision problem. -/
def OneStepSequentialObjective.toDecisionProblem
    (R : OneStepSequentialObjective (A := A) (S := S)) :
    DecisionProblem A S :=
  { utility := R.reward }

/-- Sufficiency in one-step sequential form. -/
def OneStepSequentialObjective.isSufficient
    (R : OneStepSequentialObjective (A := A) (S := S))
    {n : ℕ} [CoordinateSpace S n] (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I → R.Opt s = R.Opt s'

/-- Formal one-step deterministic bridge used in Proposition `prop:one-step-bridge`. -/
theorem one_step_bridge
    (R : OneStepSequentialObjective (A := A) (S := S))
    {n : ℕ} [CoordinateSpace S n] (I : Finset (Fin n)) :
    R.isSufficient I ↔ (R.toDecisionProblem).isSufficient I := by
  rfl

/-! ### Bridge-failure witnesses when one-step conditions are dropped -/

private def i0_bridge : Fin 1 := ⟨0, by decide⟩
private def s0_bridge : Fin 1 → Bool := fun _ => false
private def s1_bridge : Fin 1 → Bool := fun _ => true

structure TwoStepObjective where
  immediate : Bool → (Fin 1 → Bool) → ℝ
  deferred : Bool → (Fin 1 → Bool) → ℝ

def TwoStepObjective.score (R : TwoStepObjective) (a : Bool) (s : Fin 1 → Bool) : ℝ :=
  R.immediate a s + R.deferred a s

def TwoStepObjective.Opt (R : TwoStepObjective) (s : Fin 1 → Bool) : Set Bool :=
  { a : Bool | ∀ a' : Bool, R.score a' s ≤ R.score a s }

def TwoStepObjective.toImmediateDecisionProblem (R : TwoStepObjective) :
    DecisionProblem Bool (Fin 1 → Bool) :=
  { utility := R.immediate }

def horizonTwoWitness : TwoStepObjective where
  immediate := fun _ _ => 0
  deferred := fun a s => if a = s i0_bridge then 1 else 0

theorem horizonTwoWitness_not_empty_sufficient_two_step :
    ¬ (∀ s s' : Fin 1 → Bool, TwoStepObjective.Opt horizonTwoWitness s =
      TwoStepObjective.Opt horizonTwoWitness s') := by
  intro hconst
  have hEq := hconst s0_bridge s1_bridge
  have hFalseInS0 : (false : Bool) ∈ TwoStepObjective.Opt horizonTwoWitness s0_bridge := by
    intro a'
    cases a' <;> simp [TwoStepObjective.Opt, TwoStepObjective.score, horizonTwoWitness, s0_bridge, i0_bridge]
  have hFalseNotInS1 : (false : Bool) ∉ TwoStepObjective.Opt horizonTwoWitness s1_bridge := by
    intro hmem
    have h := hmem true
    simp [TwoStepObjective.Opt, TwoStepObjective.score, horizonTwoWitness, s1_bridge, i0_bridge] at h
    have hcontra : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    exact hcontra h
  have hFalseInS1 : (false : Bool) ∈ TwoStepObjective.Opt horizonTwoWitness s1_bridge := by
    simpa [hEq] using hFalseInS0
  exact hFalseNotInS1 hFalseInS1

theorem horizonTwoWitness_immediate_empty_sufficient :
    (horizonTwoWitness.toImmediateDecisionProblem).isSufficient (∅ : Finset (Fin 1)) := by
  refine (DecisionProblem.emptySet_sufficient_iff_constant
    (dp := horizonTwoWitness.toImmediateDecisionProblem)).2 ?_
  intro s s'
  ext a
  cases a <;> simp [TwoStepObjective.toImmediateDecisionProblem, horizonTwoWitness, DecisionProblem.Opt, DecisionProblem.isOptimal]

theorem horizon_gt_one_bridge_can_fail_on_sufficiency :
    ¬ (∀ s s' : Fin 1 → Bool,
      TwoStepObjective.Opt horizonTwoWitness s = TwoStepObjective.Opt horizonTwoWitness s') ∧
    (horizonTwoWitness.toImmediateDecisionProblem).isSufficient (∅ : Finset (Fin 1)) := by
  exact ⟨horizonTwoWitness_not_empty_sufficient_two_step, horizonTwoWitness_immediate_empty_sufficient⟩

structure StochasticCriterionObjective where
  expected : Bool → (Fin 1 → Bool) → ℝ
  chanceScore : Bool → (Fin 1 → Bool) → ℝ

def StochasticCriterionObjective.OptChance (R : StochasticCriterionObjective)
    (s : Fin 1 → Bool) : Set Bool :=
  { a : Bool | ∀ a' : Bool, R.chanceScore a' s ≤ R.chanceScore a s }

def StochasticCriterionObjective.toExpectedDecisionProblem (R : StochasticCriterionObjective) :
    DecisionProblem Bool (Fin 1 → Bool) :=
  { utility := R.expected }

def stochasticWitness : StochasticCriterionObjective where
  expected := fun _ _ => 0
  chanceScore := fun a s => if a = s i0_bridge then 1 else 0

theorem stochastic_objective_bridge_can_fail_on_sufficiency :
    ¬ (∀ s s' : Fin 1 → Bool,
        StochasticCriterionObjective.OptChance stochasticWitness s =
          StochasticCriterionObjective.OptChance stochasticWitness s') ∧
    (stochasticWitness.toExpectedDecisionProblem).isSufficient (∅ : Finset (Fin 1)) := by
  constructor
  · intro hconst
    have hEq := hconst s0_bridge s1_bridge
    have hFalseInS0 :
        (false : Bool) ∈ StochasticCriterionObjective.OptChance stochasticWitness s0_bridge := by
      intro a'
      cases a' <;> simp [StochasticCriterionObjective.OptChance, stochasticWitness, s0_bridge, i0_bridge]
    have hFalseNotInS1 :
        (false : Bool) ∉ StochasticCriterionObjective.OptChance stochasticWitness s1_bridge := by
      intro hmem
      have h := hmem true
      simp [StochasticCriterionObjective.OptChance, stochasticWitness, s1_bridge, i0_bridge] at h
      have hcontra : ¬ ((1 : ℝ) ≤ 0) := by norm_num
      exact hcontra h
    have hFalseInS1 :
        (false : Bool) ∈ StochasticCriterionObjective.OptChance stochasticWitness s1_bridge := by
      simpa [hEq] using hFalseInS0
    exact hFalseNotInS1 hFalseInS1
  · refine (DecisionProblem.emptySet_sufficient_iff_constant
      (dp := stochasticWitness.toExpectedDecisionProblem)).2 ?_
    intro s s'
    ext a
    cases a <;> simp [StochasticCriterionObjective.toExpectedDecisionProblem, stochasticWitness,
      DecisionProblem.Opt, DecisionProblem.isOptimal]

structure TransitionCoupledObjective where
  immediate : Bool → (Fin 1 → Bool) → ℝ
  transition : Bool → (Fin 1 → Bool) → (Fin 1 → Bool)
  terminal : (Fin 1 → Bool) → ℝ

def TransitionCoupledObjective.score (R : TransitionCoupledObjective)
    (a : Bool) (s : Fin 1 → Bool) : ℝ :=
  R.immediate a s + R.terminal (R.transition a s)

def TransitionCoupledObjective.Opt (R : TransitionCoupledObjective)
    (s : Fin 1 → Bool) : Set Bool :=
  { a : Bool | ∀ a' : Bool, R.score a' s ≤ R.score a s }

def TransitionCoupledObjective.toImmediateDecisionProblem (R : TransitionCoupledObjective) :
    DecisionProblem Bool (Fin 1 → Bool) :=
  { utility := R.immediate }

def transitionWitness : TransitionCoupledObjective where
  immediate := fun _ _ => 0
  transition := fun a s => if a then s else (fun _ => !(s i0_bridge))
  terminal := fun s => if s i0_bridge then 1 else 0

theorem transition_coupled_bridge_can_fail_on_sufficiency :
    ¬ (∀ s s' : Fin 1 → Bool,
        TransitionCoupledObjective.Opt transitionWitness s =
          TransitionCoupledObjective.Opt transitionWitness s') ∧
    (transitionWitness.toImmediateDecisionProblem).isSufficient (∅ : Finset (Fin 1)) := by
  constructor
  · intro hconst
    have hEq := hconst s0_bridge s1_bridge
    have hFalseIn :
        (false : Bool) ∈ TransitionCoupledObjective.Opt transitionWitness s0_bridge := by
      intro a'
      cases a' <;> simp [TransitionCoupledObjective.Opt, TransitionCoupledObjective.score,
        transitionWitness, s0_bridge, i0_bridge]
    have hFalseNotIn :
        (false : Bool) ∉ TransitionCoupledObjective.Opt transitionWitness s1_bridge := by
      intro hmem
      have h := hmem true
      simp [TransitionCoupledObjective.Opt, TransitionCoupledObjective.score,
        transitionWitness, s1_bridge, i0_bridge] at h
      have hcontra : ¬ ((1 : ℝ) ≤ 0) := by norm_num
      exact hcontra h
    have hFalseInS1 :
        (false : Bool) ∈ TransitionCoupledObjective.Opt transitionWitness s1_bridge := by
      simpa [hEq] using hFalseIn
    exact hFalseNotIn hFalseInS1
  · refine (DecisionProblem.emptySet_sufficient_iff_constant
      (dp := transitionWitness.toImmediateDecisionProblem)).2 ?_
    intro s s'
    ext a
    cases a <;> simp [TransitionCoupledObjective.toImmediateDecisionProblem, transitionWitness,
      DecisionProblem.Opt, DecisionProblem.isOptimal]

end OneStepBridge

/-! ## Over-modeling diagnostic contrapositive in the mechanized Boolean model -/

section DiagnosticContrapositive

open Sigma2PHardness

variable {A : Type*} {n : ℕ}

/-- Boundary characterization predicate in the mechanized Boolean model:
there exists an exactly relevance-identifying coordinate set. -/
def boundaryCharacterized
    (dp : DecisionProblem A (Fin n → Bool)) : Prop :=
  ∃ I : Finset (Fin n), exactlyIdentifiesRelevant dp I

/-- Contrapositive diagnostic theorem:
if exact relevance identification fails for every candidate set,
boundary characterization fails in this model. -/
theorem no_exact_identifier_implies_not_boundary_characterized
    (dp : DecisionProblem A (Fin n → Bool)) :
    (¬ ∃ I : Finset (Fin n), exactlyIdentifiesRelevant dp I) →
      ¬ boundaryCharacterized dp := by
  intro hNone hBoundary
  exact hNone hBoundary

/-- Equivalent form using the sufficient-and-subset characterization. -/
theorem boundaryCharacterized_iff_exists_sufficient_subset
    (dp : DecisionProblem A (Fin n → Bool)) :
    boundaryCharacterized dp ↔
      ∃ I : Finset (Fin n), dp.isSufficient I ∧ I ⊆ relevantFinset dp := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨I, (exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset dp I).1 hI⟩
  · rintro ⟨I, hI⟩
    exact ⟨I, (exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset dp I).2 hI⟩

end DiagnosticContrapositive

/-! ## Conditional composition theorem for `cor:no-auto-minimize` -/

section ConditionalComposition

/-- Pure logical closure used by `cor:no-auto-minimize`:
if a polytime exact minimizer implies a class collapse, then under
non-collapse no such minimizer exists. -/
theorem no_auto_minimize_of_p_neq_conp
    {P_eq_coNP HasPolytimeExactMinimizer : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : HasPolytimeExactMinimizer → P_eq_coNP) :
    ¬ HasPolytimeExactMinimizer := by
  intro hPoly
  exact hNeq (hCollapse hPoly)

/-- Packaged integrity-resource closure for sufficiency-style collapse assumptions. -/
theorem integrity_resource_bound_for_sufficiency
    {P_eq_coNP PolytimeUniversalCompetence : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hSuffHard : PolytimeUniversalCompetence → P_eq_coNP) :
    ¬ PolytimeUniversalCompetence :=
  DecisionQuotient.IntegrityCompetence.integrity_resource_bound hNeq hSuffHard

/-- Declared-physics no-universal-exact-certifier schema:
if universal exact competence over a declared class would force a collapse,
then under non-collapse no such universal exact certifier exists. -/
theorem declared_physics_no_universal_exact_certifier_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Γ : IntegrityCompetence.Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse :
      (∃ Q : IntegrityCompetence.CertifyingSolver X Y W,
          IntegrityCompetence.CompetentOn R Γ Q) → P_eq_coNP) :
    ¬ (∃ Q : IntegrityCompetence.CertifyingSolver X Y W,
          IntegrityCompetence.CompetentOn R Γ Q) :=
  DecisionQuotient.IntegrityCompetence.integrity_resource_bound hNeq hCollapse

/-- Typed-claim closure of the declared-physics schema:
under the same hardness/collapse assumptions, exact reports are inadmissible
for every solver in the declared class. -/
theorem no_exact_claim_admissible_under_hardness_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse :
      (∃ Q : IntegrityCompetence.CertifyingSolver X Y W,
          IntegrityCompetence.CompetentOn R Γ Q) → P_eq_coNP) :
    ∀ Q : IntegrityCompetence.CertifyingSolver X Y W,
      ¬ IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact := by
  intro Q
  have hNoUniversal :
      ¬ (∃ Q' : IntegrityCompetence.CertifyingSolver X Y W,
            IntegrityCompetence.CompetentOn R Γ Q') :=
    DecisionQuotient.IntegrityCompetence.integrity_resource_bound hNeq hCollapse
  have hNoCompQ : ¬ IntegrityCompetence.CompetentOn R Γ Q := by
    intro hComp
    exact hNoUniversal ⟨Q, hComp⟩
  exact IntegrityCompetence.no_uncertified_exact_claim
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) hNoCompQ

/-- Hardness-blocked regimes force exact certainty inflation:
exact reports are inadmissible for every solver, hence any exact report is
evidence-free by the typed evidence equivalence. -/
theorem exact_certainty_inflation_under_hardness_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse :
      (∃ Q : IntegrityCompetence.CertifyingSolver X Y W,
          IntegrityCompetence.CompetentOn R Γ Q) → P_eq_coNP) :
    ∀ Q : IntegrityCompetence.CertifyingSolver X Y W,
      IntegrityCompetence.ExactCertaintyInflation R Rε Γ Q := by
  intro Q
  have hNoAdm :
      ¬ IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact :=
    no_exact_claim_admissible_under_hardness_core
      (R := R) (Rε := Rε) (Γ := Γ)
      (P_eq_coNP := P_eq_coNP) hNeq hCollapse Q
  exact (IntegrityCompetence.certaintyInflation_iff_not_admissible
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q)
    (r := IntegrityCompetence.ClaimReport.exact)).2 hNoAdm

/-! ### Explicit-assumption requirement outside declared carve-outs -/

/-- Four declared carve-outs under which exact physical claims may be reported
without a hardness-profile disclosure in this framework. -/
inductive ExactClaimExcuse where
  | trivialScope
  | tractableClass
  | strongerOracle
  | unboundedResources
  deriving DecidableEq, Repr

/-- A regime is excuse-covered if at least one declared carve-out applies. -/
def ExcusedBy (excuses : Set ExactClaimExcuse) : Prop :=
  excuses.Nonempty

/-- Explicit hardness-assumption profile attached to a declared class/regime. -/
structure ExplicitHardnessAssumptions
    (X : Type*) (Y : Type*) (W : Type*)
    (R : Set (X × Y)) (Γ : IntegrityCompetence.Regime X) where
  P_eq_coNP : Prop
  nonCollapse : ¬ P_eq_coNP
  collapseFromUniversalCompetence :
    (∃ Q : IntegrityCompetence.CertifyingSolver X Y W,
        IntegrityCompetence.CompetentOn R Γ Q) → P_eq_coNP

/-- Well-typed exact-physical-claim policy:
either an explicit carve-out is declared, or an explicit hardness profile is
declared for the class/regime. -/
def ExactPhysicalClaimWellTyped
    (X : Type*) (Y : Type*) (W : Type*)
    (R : Set (X × Y)) (Γ : IntegrityCompetence.Regime X)
    (excuses : Set ExactClaimExcuse) : Prop :=
  ExcusedBy excuses ∨ Nonempty (ExplicitHardnessAssumptions X Y W R Γ)

/-- Outside the declared carve-outs, a well-typed exact physical claim requires
an explicit hardness-assumption profile. -/
theorem explicit_assumptions_required_of_not_excused_core
    {X Y W : Type*}
    (R : Set (X × Y)) (Γ : IntegrityCompetence.Regime X)
    (excuses : Set ExactClaimExcuse)
    (hTyped : ExactPhysicalClaimWellTyped X Y W R Γ excuses)
    (hNoExcuse : ¬ ExcusedBy excuses) :
    Nonempty (ExplicitHardnessAssumptions X Y W R Γ) := by
  cases hTyped with
  | inl hExc =>
      exact False.elim (hNoExcuse hExc)
  | inr hAssump =>
      exact hAssump

/-- If no carve-out applies and the declared hardness profile holds, then exact
claims are inadmissible for every solver in the class/regime. -/
theorem no_exact_claim_under_declared_assumptions_unless_excused_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (excuses : Set ExactClaimExcuse)
    (hNoExcuse : ¬ ExcusedBy excuses)
    (A : ExplicitHardnessAssumptions X Y W R Γ) :
    ∀ Q : IntegrityCompetence.CertifyingSolver X Y W,
      ¬ IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact := by
  intro Q
  have _ : ¬ ExcusedBy excuses := hNoExcuse
  exact no_exact_claim_admissible_under_hardness_core
    (R := R) (Rε := Rε) (Γ := Γ)
    (P_eq_coNP := A.P_eq_coNP)
    A.nonCollapse A.collapseFromUniversalCompetence Q

end ConditionalComposition

/-! ## Complexity-theoretic lift closures (explicitly conditional on standard facts) -/

section ComplexityLifts

open Sigma2PHardness

/-- Named bundle for standard external assumptions used by conditional lift theorems.
    This keeps assumption tracking explicit when assembling theorem-level closures. -/
structure StandardComplexityAssumptions
    (TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP RelevantCard_coNP
      RelevantCard_coNP_complete ExistsForallSAT_sigma2p_complete ETH : Prop) : Prop where
  hTautologyCoNPComplete : TAUTOLOGY_coNP_complete
  hSufficiencyInCoNP : SUFFICIENCY_in_coNP
  hRelevantCardCoNP : RelevantCard_coNP
  hRelevantCardCoNPComplete : RelevantCard_coNP_complete
  hExistsForallSATSigma2PComplete : ExistsForallSAT_sigma2p_complete
  hETH : ETH

/-! ### SUFFICIENCY-CHECK (coNP) -/

/-- Mechanized reduction core used in coNP transfer for SUFFICIENCY-CHECK. -/
theorem sufficiency_conp_reduction_core {n : ℕ} (φ : Formula n) :
    (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology :=
  (tautology_iff_sufficient φ).symm

/-- Conditional coNP-completeness transfer for SUFFICIENCY-CHECK.
    The transfer/completeness fact itself is treated as a standard external lemma. -/
theorem sufficiency_conp_complete_conditional
    {n : ℕ}
    {TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP SUFFICIENCY_coNP_complete : Prop}
    (hIn : SUFFICIENCY_in_coNP)
    (hCompose :
      TAUTOLOGY_coNP_complete → SUFFICIENCY_in_coNP →
      (∀ φ : Formula n,
        (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology) →
      SUFFICIENCY_coNP_complete) :
    TAUTOLOGY_coNP_complete → SUFFICIENCY_coNP_complete := by
  intro hT
  exact hCompose hT hIn (fun φ => (tautology_iff_sufficient φ).symm)

/-! ### MINIMUM-SUFFICIENT-SET collapse and coNP lift -/

/-- Mechanized quantifier-collapse core used by both collapse and coNP claims. -/
theorem minsuff_collapse_core
    {A : Type*} {n : ℕ} (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ) :
    (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
      (relevantFinset dp).card ≤ k :=
  min_sufficient_set_iff_relevant_card (dp := dp) k

/-- Conditional lift from the collapse core to the coNP-reading consequence. -/
theorem minsuff_collapse_to_conp_conditional
    {RelevantCard_coNP MSS_collapse_consequence : Prop}
    (hCompose :
      RelevantCard_coNP →
      (∀ (A : Type*) (n : ℕ) (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ),
        (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
          (relevantFinset dp).card ≤ k) →
      MSS_collapse_consequence) :
    RelevantCard_coNP → MSS_collapse_consequence := by
  intro hCard
  exact hCompose hCard (fun A n dp k => min_sufficient_set_iff_relevant_card (dp := dp) k)

/-- Conditional coNP-completeness transfer for MINIMUM-SUFFICIENT-SET. -/
theorem minsuff_conp_complete_conditional
    {RelevantCard_coNP_complete MSS_coNP_complete : Prop}
    (hCompose :
      RelevantCard_coNP_complete →
      (∀ (A : Type*) (n : ℕ) (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ),
        (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
          (relevantFinset dp).card ≤ k) →
      MSS_coNP_complete) :
    RelevantCard_coNP_complete → MSS_coNP_complete := by
  intro hCard
  exact hCompose hCard (fun A n dp k => min_sufficient_set_iff_relevant_card (dp := dp) k)

/-! ### ANCHOR-SUFFICIENCY (\Sigma_2^P) -/

/-- Mechanized \(\exists\forall\)-SAT reduction core for ANCHOR-SUFFICIENCY. -/
theorem anchor_sigma2p_reduction_core (φ : ExistsForallFormula) :
    ExistsForallFormula.satisfiable φ ↔
      (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
        (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny) :=
  exists_forall_iff_anchor_sufficient_padded φ

/-- Conditional \(\Sigma_2^P\)-completeness transfer for ANCHOR-SUFFICIENCY. -/
theorem anchor_sigma2p_complete_conditional
    {ExistsForallSAT_sigma2p_complete Anchor_sigma2p_complete : Prop}
    (hCompose :
      ExistsForallSAT_sigma2p_complete →
      (∀ φ : ExistsForallFormula,
        ExistsForallFormula.satisfiable φ ↔
          (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
            (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny)) →
      Anchor_sigma2p_complete) :
    ExistsForallSAT_sigma2p_complete → Anchor_sigma2p_complete := by
  intro hSrc
  exact hCompose hSrc (fun φ => exists_forall_iff_anchor_sufficient_padded φ)

/-! ### Dichotomy and ETH-conditioned lower bound closure -/

/-- Mechanized hard-family core used in the ETH branch. -/
theorem hard_family_all_coords_core {n : ℕ} (φ : Formula n) (h : ¬ φ.isTautology) :
    ∀ i : Fin n, (reductionProblemMany φ).isRelevant i :=
  all_coords_relevant_of_not_tautology (φ := φ) h

/-- Mechanized explicit-state algorithmic upper-core. -/
theorem explicit_state_upper_core
    {A S : Type*} [DecidableEq S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) (equiv : S → S → Prop) [DecidableRel equiv]
    (pairs : List (S × S)) :
    (countedCheckPairs dp equiv pairs).steps ≤ pairs.length :=
  countedCheckPairs_steps_bound dp equiv pairs

/-- Conditional dichotomy closure: explicit upper branch + ETH transfer from hard family. -/
theorem dichotomy_conditional
    {ETH ExplicitStateUpperBound SuccinctETHLowerBound : Prop}
    (hExplicit : ExplicitStateUpperBound)
    (hTransfer :
      ETH →
      (∀ {n : ℕ} (φ : Formula n), ¬ φ.isTautology →
        ∀ i : Fin n, (reductionProblemMany φ).isRelevant i) →
      SuccinctETHLowerBound) :
    ETH → (ExplicitStateUpperBound ∧ SuccinctETHLowerBound) := by
  intro hEth
  refine ⟨hExplicit, ?_⟩
  exact hTransfer hEth (fun φ hnt i => all_coords_relevant_of_not_tautology (φ := φ) hnt i)

/-! ### Universal solver framing closure -/

/-- Any deterministic partial map can be framed as a certifying solver for its induced relation. -/
theorem universal_solver_framing_core
    {X Y : Type*}
    (f : X → Option Y) :
    ∃ Q : IntegrityCompetence.CertifyingSolver X Y PUnit,
      IntegrityCompetence.SolverIntegrity (IntegrityCompetence.inducedRelation f) Q :=
  IntegrityCompetence.program_framed_as_solver (X := X) (Y := Y) f

/-- Integrity definition is substrate-parametric:
the same predicate applies unchanged once a certifying solver pair is declared. -/
theorem integrity_universal_applicability_core
    {X Y W : Type*}
    (R : Set (X × Y)) (Q : IntegrityCompetence.CertifyingSolver X Y W) :
    IntegrityCompetence.SolverIntegrity R Q ↔
      ((∀ x y w, Q.solve x = some (y, w) → Q.check x y w) ∧
       (∀ x y w, Q.check x y w → (x, y) ∈ R)) :=
  IntegrityCompetence.solverIntegrity_substrate_parametric (X := X) (Y := Y) (W := W) R Q

/-! ### Typed claim discipline closure -/

/-- Typed claim admissibility core:
abstain is always admissible; exact and ε-claims are admissible iff
their corresponding certificates hold. -/
theorem typed_claim_admissibility_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W) :
    IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.abstain ∧
      (IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact ↔
        IntegrityCompetence.CompetentOn R Γ Q) ∧
      (∀ ε : ℝ,
        IntegrityCompetence.ClaimAdmissible R Rε Γ Q (IntegrityCompetence.ClaimReport.epsilon ε) ↔
          IntegrityCompetence.EpsilonCompetentOn Rε ε Γ Q) := by
  refine ⟨?_, ?_, ?_⟩
  · exact IntegrityCompetence.claim_admissible_abstain (R := R) (Rε := Rε) (Γ := Γ) (Q := Q)
  · exact IntegrityCompetence.claim_admissible_exact_iff (R := R) (Rε := Rε) (Γ := Γ) (Q := Q)
  · intro ε
    exact IntegrityCompetence.claim_admissible_epsilon_iff
      (R := R) (Rε := Rε) (ε := ε) (Γ := Γ) (Q := Q)

/-- No exact certificate implies exact-claim inadmissibility in the typed discipline. -/
theorem no_uncertified_exact_claim_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (hNo : ¬ IntegrityCompetence.CompetentOn R Γ Q) :
    ¬ IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact :=
  IntegrityCompetence.no_uncertified_exact_claim
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) hNo

/-! ### Raw-vs-certified bit accounting closure -/

/-- Structural split of report-level accounting:
    total certified bits are raw bits plus evidence-gated overhead bits. -/
theorem certified_total_bits_split_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (M : IntegrityCompetence.ReportBitModel)
    (r : IntegrityCompetence.ClaimReport) :
    IntegrityCompetence.certifiedTotalBits R Rε Γ Q M r =
      M.rawBits r + IntegrityCompetence.certificationOverheadBits R Rε Γ Q M r :=
  IntegrityCompetence.certifiedTotalBits_eq_raw_plus_overhead
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) (r := r)

/-- Exact-report bit-accounting equivalence:
    raw-only exact accounting iff exact certainty inflation. -/
theorem exact_raw_eq_certified_iff_certainty_inflation_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (M : IntegrityCompetence.ReportBitModel) :
    IntegrityCompetence.certifiedTotalBits R Rε Γ Q M IntegrityCompetence.ClaimReport.exact =
      M.rawBits IntegrityCompetence.ClaimReport.exact
      ↔
      IntegrityCompetence.ExactCertaintyInflation R Rε Γ Q :=
  IntegrityCompetence.exact_raw_eq_certifiedTotal_iff_exactCertaintyInflation
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)

/-- Exact-report admissibility is equivalent to a strict
    certified-bit gap above raw bits. -/
theorem exact_admissible_iff_raw_lt_certified_total_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (M : IntegrityCompetence.ReportBitModel) :
    IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact
      ↔
      M.rawBits IntegrityCompetence.ClaimReport.exact <
        IntegrityCompetence.certifiedTotalBits R Rε Γ Q M IntegrityCompetence.ClaimReport.exact :=
  IntegrityCompetence.exact_admissible_iff_raw_lt_certifiedTotal
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)

/-- If exact report is inadmissible, exact accounting is raw-only. -/
theorem exact_raw_only_of_no_exact_admissible_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (M : IntegrityCompetence.ReportBitModel)
    (hNoAdm :
      ¬ IntegrityCompetence.ClaimAdmissible R Rε Γ Q IntegrityCompetence.ClaimReport.exact) :
    IntegrityCompetence.certifiedTotalBits R Rε Γ Q M IntegrityCompetence.ClaimReport.exact =
      M.rawBits IntegrityCompetence.ClaimReport.exact :=
  IntegrityCompetence.exact_raw_only_of_no_exact_admissible
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) hNoAdm

/-- ε-report admissibility is equivalent to a strict
    certified-bit gap above raw bits. -/
theorem epsilon_admissible_iff_raw_lt_certified_total_core
    {X Y W : Type*}
    (R : Set (X × Y))
    (Rε : IntegrityCompetence.EpsilonRelation X Y)
    (ε : ℝ)
    (Γ : IntegrityCompetence.Regime X)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (M : IntegrityCompetence.ReportBitModel) :
    IntegrityCompetence.ClaimAdmissible R Rε Γ Q (IntegrityCompetence.ClaimReport.epsilon ε)
      ↔
      M.rawBits (IntegrityCompetence.ClaimReport.epsilon ε) <
        IntegrityCompetence.certifiedTotalBits R Rε Γ Q M (IntegrityCompetence.ClaimReport.epsilon ε) :=
  IntegrityCompetence.epsilon_admissible_iff_raw_lt_certifiedTotal
    (R := R) (Rε := Rε) (ε := ε) (Γ := Γ) (Q := Q) (M := M)

/-! ### Budgeted physical crossover closure -/

/-- Mechanized crossover core:
    explicit infeasibility with simultaneous succinct feasibility at a declared budget. -/
theorem physical_crossover_core
    (M : PhysicalBudgetCrossover.EncodingSizeModel) (B n : ℕ)
    (hCross : PhysicalBudgetCrossover.CrossoverAt M B n) :
    PhysicalBudgetCrossover.ExplicitInfeasible M B n ∧
      PhysicalBudgetCrossover.SuccinctFeasible M B n :=
  PhysicalBudgetCrossover.explicit_infeasible_succinct_feasible_of_crossover M B n hCross

/-- Above-cap crossover existence:
if succinct size is globally capped and explicit size is unbounded,
then every budget above the cap has a crossover witness. -/
theorem physical_crossover_above_cap_core
    (M : PhysicalBudgetCrossover.EncodingSizeModel) (C B : ℕ)
    (hSucc : PhysicalBudgetCrossover.SuccinctBoundedBy M C)
    (hExp : PhysicalBudgetCrossover.ExplicitUnbounded M)
    (hBudget : C ≤ B) :
    PhysicalBudgetCrossover.HasCrossover M B :=
  PhysicalBudgetCrossover.has_crossover_of_bounded_succinct_unbounded_explicit
    M C B hSucc hExp hBudget

/-- Conditional crossover-plus-hardness bundle:
    representational crossover does not imply exact-certification competence. -/
theorem physical_crossover_hardness_core
    (M : PhysicalBudgetCrossover.EncodingSizeModel) (B n : ℕ)
    {P_eq_coNP ExactCertificationCompetence : Prop}
    (hCross : PhysicalBudgetCrossover.CrossoverAt M B n)
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : ExactCertificationCompetence → P_eq_coNP) :
    PhysicalBudgetCrossover.ExplicitInfeasible M B n ∧
      PhysicalBudgetCrossover.SuccinctFeasible M B n ∧
      ¬ ExactCertificationCompetence :=
  PhysicalBudgetCrossover.crossover_hardness_bundle M B n hCross hNeq hCollapse

/-- Solver-form policy closure at crossover:
    under integrity + collapse assumptions, abstention or budget failure is forced. -/
theorem physical_crossover_policy_core
    {X Y W : Type*}
    (M : PhysicalBudgetCrossover.EncodingSizeModel) (B n : ℕ)
    (hCross : PhysicalBudgetCrossover.CrossoverAt M B n)
    (R : Set (X × Y)) (Γ : IntegrityCompetence.Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse :
      (∃ Q : IntegrityCompetence.CertifyingSolver X Y W,
          IntegrityCompetence.CompetentOn R Γ Q) → P_eq_coNP)
    (Q : IntegrityCompetence.CertifyingSolver X Y W)
    (hIntegrity : IntegrityCompetence.SolverIntegrity R Q) :
    PhysicalBudgetCrossover.ExplicitInfeasible M B n ∧
      PhysicalBudgetCrossover.SuccinctFeasible M B n ∧
      (¬ (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w))
        ∨
       ¬ (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))) :=
  PhysicalBudgetCrossover.crossover_integrity_policy M B n hCross R Γ hNeq hCollapse Q hIntegrity

/-! ### Cost asymmetry under ETH (conditional closure) -/

/-- Conditional cost-asymmetry closure:
    if ETH yields an eventual \(2^n\)-lower-bound for finding-cost, then
    linear-overhead maintenance is eventually dominated. -/
theorem cost_asymmetry_eth_conditional
    {ETH : Prop} {Cfind : ℕ → ℕ}
    (k c : ℕ)
    (hLower : ETH → ∃ n0, ∀ n ≥ n0, 2 ^ n ≤ Cfind n) :
    ETH → ∃ n0, ∀ n ≥ n0, k < Cfind n + c := by
  intro hEth
  obtain ⟨n1, h1⟩ := HardnessDistribution.linear_lt_exponential_plus_constant_eventually k c
  obtain ⟨n2, h2⟩ := hLower hEth
  refine ⟨max n1 n2, ?_⟩
  intro n hn
  have hn1 : n ≥ n1 := le_trans (Nat.le_max_left _ _) hn
  have hn2 : n ≥ n2 := le_trans (Nat.le_max_right _ _) hn
  have hk : k < 2 ^ n + c := h1 n hn1
  have hpow : 2 ^ n ≤ Cfind n := h2 n hn2
  exact lt_of_lt_of_le hk (Nat.add_le_add_right hpow c)

/-! ### Tractable-subcase closure -/

/-- Mechanized bounded-action tractable branch. -/
theorem tractable_bounded_core
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    {n : ℕ} [CoordinateSpace S n] [Fintype A] [Fintype S]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S) (k : ℕ)
    (hcard : Fintype.card A ≤ k) :
    ∃ (decide : Finset (Fin n) → Bool),
      (∀ I, decide I = true ↔ cdp.toAbstract.isSufficient I) :=
  sufficiency_poly_bounded_actions (k := k) cdp hcard

/-- Mechanized separable-utility tractable branch. -/
theorem tractable_separable_core
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    {n : ℕ} [CoordinateSpace S n]
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ dp.isSufficient I :=
  sufficiency_poly_separable (dp := dp) hsep

/-- Mechanized tree-structured tractable branch. -/
theorem tractable_tree_core
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S)
    (deps : Fin n → Finset (Fin n)) (htree : TreeStructured deps) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I :=
  sufficiency_poly_tree_structured cdp deps htree

/-- Conditional assembly theorem for the full tractable-subcase statement. -/
theorem tractable_subcases_conditional
    {BoundedCase SeparableCase TreeCase TractableSubcases : Prop}
    (hBounded : BoundedCase)
    (hSeparable : SeparableCase)
    (hTree : TreeCase)
    (hAssemble : BoundedCase → SeparableCase → TreeCase → TractableSubcases) :
    TractableSubcases :=
  hAssemble hBounded hSeparable hTree

/-! ### Heuristic reusability bridge -/

/-- A structure class is detectable if membership is decidable via a boolean
    detector (used as the proxy for polynomial detectability in this layer). -/
structure StructureDetectable {α : Type*} (C : α → Prop) where
  detect : α → Bool
  detect_correct : ∀ x, detect x = true ↔ C x

/-- Any decidable class yields a canonical detector. -/
def structureDetectable_of_decidable
    {α : Type*} (C : α → Prop) [DecidablePred C] :
    StructureDetectable C where
  detect x := decide (C x)
  detect_correct x := by simp

/-- Heuristic reusability bridge:
    if class membership is detectable and class-conditioned checker correctness
    is known, then detect-then-check yields a correct result on detected
    instances. -/
theorem reusable_heuristic_of_detectable
    {α Result : Type*}
    (C : α → Prop)
    (hDetect : StructureDetectable C)
    (Correct : Result → Prop)
    (checker : α → Result)
    (hCorrect : ∀ x, C x → Correct (checker x))
    (x : α) (hx : hDetect.detect x = true) :
    Correct (checker x) := by
  exact hCorrect x ((hDetect.detect_correct x).1 hx)

/-- Bounded-actions class is detectable by checking `|A| ≤ k`. -/
def bounded_actions_detectable
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    [Fintype A] [Fintype S] {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (k : ℕ) :
    StructureDetectable
      (fun _ : ComputableDecisionProblem A S => Fintype.card A ≤ k) :=
  structureDetectable_of_decidable (C := fun _ : ComputableDecisionProblem A S => Fintype.card A ≤ k)

/-- Reusable bounded-actions heuristic on detected instances. -/
theorem bounded_actions_reusable_heuristic
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    [Fintype A] [Fintype S] {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (k : ℕ) (cdp : ComputableDecisionProblem A S)
    (hx : (bounded_actions_detectable (A := A) (S := S) (n := n) k).detect cdp = true) :
    ∃ decide : Finset (Fin n) → Bool,
      ∀ I, decide I = true ↔ cdp.toAbstract.isSufficient I := by
  let C : ComputableDecisionProblem A S → Prop := fun _ => Fintype.card A ≤ k
  let hDetect : StructureDetectable C := bounded_actions_detectable (A := A) (S := S) (n := n) k
  let checker : ComputableDecisionProblem A S → Prop :=
    fun x =>
      ∃ decide : Finset (Fin n) → Bool,
        ∀ I, decide I = true ↔ x.toAbstract.isSufficient I
  have hCorrect : ∀ x, C x → checker x := by
    intro x hxCard
    exact tractable_bounded_core (A := A) (S := S) (n := n) x k hxCard
  have hReusable :=
    reusable_heuristic_of_detectable
      (C := C) (hDetect := hDetect) (Correct := fun p : Prop => p)
      (checker := checker) hCorrect cdp hx
  simpa [checker] using hReusable

/-- Separable-utility class is detectable from a decidable-membership predicate
    on the witness-bearing class condition. -/
noncomputable def separable_detectable
    {A S : Type*} [DecidableEq A] [DecidableEq S] {n : ℕ} [CoordinateSpace S n] :
    StructureDetectable
      (fun dp : FiniteDecisionProblem (A := A) (S := S) =>
        Nonempty (SeparableUtility (dp := dp))) := by
  classical
  exact structureDetectable_of_decidable
    (C := fun dp : FiniteDecisionProblem (A := A) (S := S) =>
      Nonempty (SeparableUtility (dp := dp)))

/-- Reusable separable-utility heuristic on detected instances. -/
theorem separable_reusable_heuristic
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    {n : ℕ} [CoordinateSpace S n]
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hx : (separable_detectable (A := A) (S := S) (n := n)).detect dp = true) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ dp.isSufficient I := by
  let C : FiniteDecisionProblem (A := A) (S := S) → Prop :=
    fun x => Nonempty (SeparableUtility (dp := x))
  let hDetect : StructureDetectable C := separable_detectable (A := A) (S := S) (n := n)
  let checker : FiniteDecisionProblem (A := A) (S := S) → Prop :=
    fun x =>
      ∃ algo : Finset (Fin n) → Bool,
        ∀ I, algo I = true ↔ x.isSufficient I
  have hCorrect : ∀ x, C x → checker x := by
    intro x hxSep
    exact tractable_separable_core (A := A) (S := S) (n := n) x (Classical.choice hxSep)
  have hReusable :=
    reusable_heuristic_of_detectable
      (C := C) (hDetect := hDetect) (Correct := fun p : Prop => p)
      (checker := checker) hCorrect dp hx
  simpa [checker] using hReusable

/-- Tree-structured class is detectable from a decidable-membership predicate. -/
noncomputable def tree_structure_detectable
    {n : ℕ} :
    StructureDetectable (fun deps : Fin n → Finset (Fin n) => TreeStructured deps) := by
  classical
  exact structureDetectable_of_decidable
    (C := fun deps : Fin n → Finset (Fin n) => TreeStructured deps)

/-- Reusable tree-structured heuristic on detected instances. -/
theorem tree_reusable_heuristic
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S)
    (deps : Fin n → Finset (Fin n))
    (hx : (tree_structure_detectable (n := n)).detect deps = true) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I := by
  let C : (Fin n → Finset (Fin n)) → Prop := fun d => TreeStructured d
  let hDetect : StructureDetectable C := tree_structure_detectable (n := n)
  let checker : (Fin n → Finset (Fin n)) → Prop :=
    fun d =>
      ∃ algo : Finset (Fin n) → Bool,
        ∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I
  have hCorrect : ∀ d, C d → checker d := by
    intro d hd
    exact tractable_tree_core (A := A) (S := S) (n := n) cdp d hd
  have hReusable :=
    reusable_heuristic_of_detectable
      (C := C) (hDetect := hDetect) (Correct := fun p : Prop => p)
      (checker := checker) hCorrect deps hx
  simpa [checker] using hReusable

end ComplexityLifts

/-! ## Typed regime coverage and class-completeness closures (`#9`) -/

section TypedCoverage

open Sigma2PHardness

/-- Query interfaces treated in the intermediate access family. -/
inductive QueryAccessInterface where
  | optOracle
  | valueEntry
  | stateBatch
  deriving DecidableEq, Repr

/-- Declared static-class access regimes used by theorem-typed claims. -/
inductive StaticAccessRegime where
  | explicitState
  | succinctEth
  | query (iface : QueryAccessInterface)
  deriving DecidableEq, Repr

/-- Finite declared regime family used by theorem-level scope typing. -/
def declaredRegimeFamily : Finset StaticAccessRegime :=
  { StaticAccessRegime.explicitState,
    StaticAccessRegime.succinctEth,
    StaticAccessRegime.query QueryAccessInterface.optOracle,
    StaticAccessRegime.query QueryAccessInterface.valueEntry,
    StaticAccessRegime.query QueryAccessInterface.stateBatch }

/-- Exhaustiveness for the declared static-class regime family. -/
theorem declaredRegimeFamily_complete (r : StaticAccessRegime) :
    r ∈ declaredRegimeFamily := by
  cases r with
  | explicitState =>
      simp [declaredRegimeFamily]
  | succinctEth =>
      simp [declaredRegimeFamily]
  | query iface =>
      cases iface <;> simp [declaredRegimeFamily]

/-- Regime-indexed mechanized core claims (one canonical core per regime). -/
def regimeCoreClaim : StaticAccessRegime → Prop
  | .explicitState =>
      ∀ {A S : Type*} [DecidableEq S] [DecidableEq (Set A)]
        (dp : DecisionProblem A S) (equiv : S → S → Prop) [DecidableRel equiv]
        (pairs : List (S × S)),
        (countedCheckPairs dp equiv pairs).steps ≤ pairs.length
  | .succinctEth =>
      ∀ {n : ℕ} (φ : Formula n), ¬ φ.isTautology →
        ∀ i : Fin n, (reductionProblemMany φ).isRelevant i
  | .query .optOracle =>
      ∀ {S : Type*} [Fintype S] [DecidableEq S],
        2 ≤ Fintype.card S →
        ∀ (Q : Finset S), Q.card < Fintype.card S →
          ∃ s0 : S,
            s0 ∉ Q ∧
            (oracleViewFinite Q (constTrueProblemFinite S) =
              oracleViewFinite Q (spikeProblemFinite s0)) ∧
            (constTrueProblemFinite S).isSufficient (∅ : Finset (Fin 1)) ∧
            ¬ (spikeProblemFinite s0).isSufficient (∅ : Finset (Fin 1))
  | .query .valueEntry =>
      ∀ {n : ℕ}, 0 < n →
        ∀ (Q : Finset (ValueQueryState n)),
          Q.card < Fintype.card (Fin n → Bool) →
            ∃ s0 : Fin n → Bool,
              s0 ∉ touchedStates Q ∧
              (valueEntryView Q (constTrueProblem (n := n)) =
                valueEntryView Q (spikeProblem (n := n) s0)) ∧
              (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) ∧
              ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n))
  | .query .stateBatch =>
      ∀ {n : ℕ}, 0 < n →
        ∀ (Q : Finset (StateBatchQuery n)),
          Q.card < Fintype.card (Fin n → Bool) →
            ∃ s0 : Fin n → Bool,
              s0 ∉ Q ∧
              (stateBatchView Q (constTrueProblem (n := n)) =
                stateBatchView Q (spikeProblem (n := n) s0)) ∧
              (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) ∧
              ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n))

/-- Regime-indexed coverage theorem: every declared regime has a mechanized core claim. -/
theorem regime_core_claim_proved :
    ∀ r : StaticAccessRegime, regimeCoreClaim r := by
  intro r
  cases r with
  | explicitState =>
      intro A S _ _ dp equiv _ pairs
      exact explicit_state_upper_core dp equiv pairs
  | succinctEth =>
      intro n φ hnt i
      exact hard_family_all_coords_core φ hnt i
  | query iface =>
      cases iface with
      | optOracle =>
          intro S _ _ hCard Q hQ
          exact emptySufficiency_query_indistinguishable_pair_finite hCard Q hQ
      | valueEntry =>
          intro n hn Q hQ
          exact emptySufficiency_valueEntry_indistinguishable_pair hn Q hQ
      | stateBatch =>
          intro n hn Q hQ
          exact emptySufficiency_stateBatch_indistinguishable_pair hn Q hQ

/-- Explicit finite-state (finite-alphabet) query-obstruction wrapper used in prose typing. -/
theorem query_obstruction_finite_state_core
    {S : Type*} [Fintype S] [DecidableEq S]
    (hCard : 2 ≤ Fintype.card S)
    (Q : Finset S) (hQ : Q.card < Fintype.card S) :
    ∃ s0 : S,
      s0 ∉ Q ∧
      (oracleViewFinite Q (constTrueProblemFinite S) =
        oracleViewFinite Q (spikeProblemFinite s0)) ∧
      (constTrueProblemFinite S).isSufficient (∅ : Finset (Fin 1)) ∧
      ¬ (spikeProblemFinite s0).isSufficient (∅ : Finset (Fin 1)) :=
  emptySufficiency_query_indistinguishable_pair_finite hCard Q hQ

/-- Boolean-coordinate corollary wrapper of the finite-state query-obstruction core. -/
theorem query_obstruction_boolean_corollary
    {n : ℕ} (hn : 0 < n)
    (Q : Finset (Fin n → Bool))
    (hQ : Q.card < Fintype.card (Fin n → Bool)) :
    ∃ s0 : Fin n → Bool,
      s0 ∉ Q ∧
      (oracleView Q (constTrueProblem (n := n)) =
        oracleView Q (spikeProblem (n := n) s0)) ∧
      (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) ∧
      ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n)) :=
  emptySufficiency_query_indistinguishable_pair hn Q hQ

/-- Named information-barrier wrapper (Opt-oracle finite-state core). -/
theorem information_barrier_opt_oracle_core
    {S : Type*} [Fintype S] [DecidableEq S]
    (hCard : 2 ≤ Fintype.card S)
    (Q : Finset S) (hQ : Q.card < Fintype.card S) :
    ∃ s0 : S,
      s0 ∉ Q ∧
      (oracleViewFinite Q (constTrueProblemFinite S) =
        oracleViewFinite Q (spikeProblemFinite s0)) ∧
      (constTrueProblemFinite S).isSufficient (∅ : Finset (Fin 1)) ∧
      ¬ (spikeProblemFinite s0).isSufficient (∅ : Finset (Fin 1)) :=
  query_obstruction_finite_state_core hCard Q hQ

/-- Named information-barrier wrapper (Boolean value-entry interface). -/
theorem information_barrier_value_entry_core
    {n : ℕ} (hn : 0 < n)
    (Q : Finset (ValueQueryState n))
    (hQ : Q.card < Fintype.card (Fin n → Bool)) :
    ∃ s0 : Fin n → Bool,
      s0 ∉ touchedStates Q ∧
      (valueEntryView Q (constTrueProblem (n := n)) =
        valueEntryView Q (spikeProblem (n := n) s0)) ∧
      (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) ∧
      ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n)) :=
  emptySufficiency_valueEntry_indistinguishable_pair hn Q hQ

/-- Named information-barrier wrapper (Boolean state-batch interface). -/
theorem information_barrier_state_batch_core
    {n : ℕ} (hn : 0 < n)
    (Q : Finset (StateBatchQuery n))
    (hQ : Q.card < Fintype.card (Fin n → Bool)) :
    ∃ s0 : Fin n → Bool,
      s0 ∉ Q ∧
      (stateBatchView Q (constTrueProblem (n := n)) =
        stateBatchView Q (spikeProblem (n := n) s0)) ∧
      (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) ∧
      ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n)) :=
  emptySufficiency_stateBatch_indistinguishable_pair hn Q hQ

/-! ### Conditional thermodynamic lift closure -/

/-- Core thermodynamic lift wrapper:
    bit lower bounds lift to energy and carbon lower bounds. -/
theorem thermo_energy_carbon_lift_core
    (M : ThermodynamicLift.ThermoModel)
    {bitLB bitUsed : ℕ} (hBits : bitLB ≤ bitUsed) :
    ThermodynamicLift.energyLowerBound M bitLB ≤ ThermodynamicLift.energyLowerBound M bitUsed ∧
      ThermodynamicLift.carbonLowerBound M bitLB ≤ ThermodynamicLift.carbonLowerBound M bitUsed := by
  exact ⟨
    ThermodynamicLift.energy_lower_from_bits_lower M hBits,
    ThermodynamicLift.carbon_lower_from_bits_lower M hBits
  ⟩

/-- Eventual-family thermodynamic lift wrapper. -/
theorem thermo_eventual_lift_core
    (M : ThermodynamicLift.ThermoModel)
    (bitLB bitUsed : ℕ → ℕ) (n0 : ℕ)
    (hBits : ∀ n, n ≥ n0 → bitLB n ≤ bitUsed n) :
    (∀ n, n ≥ n0 →
      ThermodynamicLift.energyLowerBound M (bitLB n) ≤
        ThermodynamicLift.energyLowerBound M (bitUsed n)) ∧
      (∀ n, n ≥ n0 →
        ThermodynamicLift.carbonLowerBound M (bitLB n) ≤
          ThermodynamicLift.carbonLowerBound M (bitUsed n)) :=
  ThermodynamicLift.eventual_thermo_lift M bitLB bitUsed n0 hBits

/-- Conditional hardness + thermodynamic bundle wrapper. -/
theorem thermo_hardness_bundle_core
    {P_eq_coNP ExactCertificationCompetence : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : ExactCertificationCompetence → P_eq_coNP)
    (M : ThermodynamicLift.ThermoModel)
    {bitLB bitUsed : ℕ} (hBits : bitLB ≤ bitUsed) :
    ¬ ExactCertificationCompetence ∧
      ThermodynamicLift.energyLowerBound M bitLB ≤ ThermodynamicLift.energyLowerBound M bitUsed ∧
      ThermodynamicLift.carbonLowerBound M bitLB ≤ ThermodynamicLift.carbonLowerBound M bitUsed :=
  ThermodynamicLift.hardness_thermo_bundle_conditional hNeq hCollapse M hBits

/-- Mandatory physical-cost core (conditional on positive conversion constants
and positive irreversible-work lower bound). -/
theorem thermo_mandatory_cost_core
    (M : ThermodynamicLift.ThermoModel)
    {bitLB : ℕ}
    (hJ : 0 < M.joulesPerBit)
    (hC : 0 < M.carbonPerJoule)
    (hBitsPos : 0 < bitLB) :
    0 < ThermodynamicLift.energyLowerBound M bitLB ∧
      0 < ThermodynamicLift.carbonLowerBound M bitLB := by
  exact ThermodynamicLift.mandatory_cost_bundle M hJ hC hBitsPos

/-- Conserved/additive accounting core in the declared linear thermodynamic model. -/
theorem thermo_conservation_additive_core
    (M : ThermodynamicLift.ThermoModel)
    (b₁ b₂ : ℕ) :
    ThermodynamicLift.energyLowerBound M (b₁ + b₂) =
      ThermodynamicLift.energyLowerBound M b₁ + ThermodynamicLift.energyLowerBound M b₂ ∧
      ThermodynamicLift.carbonLowerBound M (b₁ + b₂) =
        ThermodynamicLift.carbonLowerBound M b₁ + ThermodynamicLift.carbonLowerBound M b₂ := by
  exact ⟨
    ThermodynamicLift.energy_lower_additive M b₁ b₂,
    ThermodynamicLift.carbon_lower_additive M b₁ b₂
  ⟩

/-- Typed class-completeness closure for the static sufficiency class:
conditional lifts for class labels + regime-indexed mechanized cores +
declared regime-family exhaustiveness. -/
theorem typed_static_class_completeness
    {n : ℕ}
    {TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP SUFFICIENCY_coNP_complete : Prop}
    {RelevantCard_coNP_complete MSS_coNP_complete : Prop}
    {ExistsForallSAT_sigma2p_complete Anchor_sigma2p_complete : Prop}
    {ETH ExplicitStateUpperBound SuccinctETHLowerBound : Prop}
    (hIn : SUFFICIENCY_in_coNP)
    (hSuffCompose :
      TAUTOLOGY_coNP_complete → SUFFICIENCY_in_coNP →
      (∀ φ : Formula n,
        (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology) →
      SUFFICIENCY_coNP_complete)
    (hMssCompose :
      RelevantCard_coNP_complete →
      (∀ (A : Type*) (n : ℕ) (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ),
        (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
          (relevantFinset dp).card ≤ k) →
      MSS_coNP_complete)
    (hAnchorCompose :
      ExistsForallSAT_sigma2p_complete →
      (∀ φ : ExistsForallFormula,
        ExistsForallFormula.satisfiable φ ↔
          (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
            (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny)) →
      Anchor_sigma2p_complete)
    (hExplicit : ExplicitStateUpperBound)
    (hEthTransfer :
      ETH →
      (∀ {n : ℕ} (φ : Formula n), ¬ φ.isTautology →
        ∀ i : Fin n, (reductionProblemMany φ).isRelevant i) →
      SuccinctETHLowerBound) :
    (TAUTOLOGY_coNP_complete → SUFFICIENCY_coNP_complete) ∧
    (RelevantCard_coNP_complete → MSS_coNP_complete) ∧
    (ExistsForallSAT_sigma2p_complete → Anchor_sigma2p_complete) ∧
    (ETH → (ExplicitStateUpperBound ∧ SuccinctETHLowerBound)) ∧
    (∀ r : StaticAccessRegime, regimeCoreClaim r) ∧
    (∀ r : StaticAccessRegime, r ∈ declaredRegimeFamily) := by
  refine ⟨?_, ?_, ?_, ?_, regime_core_claim_proved, declaredRegimeFamily_complete⟩
  · intro hT
    exact sufficiency_conp_complete_conditional (n := n) hIn hSuffCompose hT
  · intro hCard
    exact minsuff_conp_complete_conditional hMssCompose hCard
  · intro hSrc
    exact anchor_sigma2p_complete_conditional hAnchorCompose hSrc
  · intro hEth
    exact dichotomy_conditional hExplicit hEthTransfer hEth

end TypedCoverage

/-! ## Anchor-query object and posing discipline (`#9`) -/

section AnchorQueryPosing

open IntegrityCompetence

variable {A S W : Type*} {n : ℕ}
variable [CoordinateSpace S n]

/-- Formal object for the anchored decision question:
fixed decision problem plus queried coordinate set. -/
structure AnchorQueryObject (A S : Type*) (n : ℕ) [CoordinateSpace S n] where
  problem : DecisionProblem A S
  coords : Finset (Fin n)

/-- Pose operation: construct the formal query object from `(dp, I)`. -/
def poseAnchorQuery (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    AnchorQueryObject A S n :=
  ⟨dp, I⟩

/-- Truth predicate of a posed anchor query. -/
def AnchorQueryObject.truth (q : AnchorQueryObject A S n) : Prop :=
  q.problem.anchorSufficient q.coords

/-- Posing returns a well-typed formal object with preserved components. -/
theorem pose_returns_anchor_query_object
    (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    (poseAnchorQuery dp I).problem = dp ∧
      (poseAnchorQuery dp I).coords = I := by
  constructor <;> rfl

/-- Semantics of posed anchor query in witness form. -/
theorem posed_anchor_query_truth_iff_exists_anchor
    (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    (poseAnchorQuery dp I).truth ↔ ∃ s₀ : S, dp.isSufficientAt I s₀ := by
  rfl

/-- Equivalent quantified form used by the ANCHOR-SUFFICIENCY problem statement. -/
theorem posed_anchor_query_truth_iff_exists_forall
    (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    (poseAnchorQuery dp I).truth ↔
      ∃ s₀ : S, ∀ s : S, agreeOn s s₀ I → dp.Opt s = dp.Opt s₀ := by
  rfl

/-- Canonical yes/no relation for anchor-query verdicts. -/
def anchorQueryRelation : Set (AnchorQueryObject A S n × Bool) :=
  {qb | (qb.2 = true ∧ qb.1.truth) ∨ (qb.2 = false ∧ ¬ qb.1.truth)}

/-- A `true` verdict is equivalent to query truth. -/
theorem anchor_query_relation_true_iff (q : AnchorQueryObject A S n) :
    (q, true) ∈ anchorQueryRelation ↔ q.truth := by
  constructor
  · intro h
    rcases h with hTrue | hFalse
    · exact hTrue.2
    · cases hFalse.1
  · intro hq
    exact Or.inl ⟨rfl, hq⟩

/-- A `false` verdict is equivalent to query falsity. -/
theorem anchor_query_relation_false_iff (q : AnchorQueryObject A S n) :
    (q, false) ∈ anchorQueryRelation ↔ ¬ q.truth := by
  constructor
  · intro h
    rcases h with hTrue | hFalse
    · cases hTrue.1
    · exact hFalse.2
  · intro hq
    exact Or.inr ⟨rfl, hq⟩

variable (Rε : EpsilonRelation (AnchorQueryObject A S n) Bool)
variable (Γ : Regime (AnchorQueryObject A S n))
variable (Q : CertifyingSolver (AnchorQueryObject A S n) Bool W)

/-- Exact claim admissibility on posed anchor queries is exactly regime competence. -/
theorem posed_anchor_exact_claim_admissible_iff_competent :
    ClaimAdmissible anchorQueryRelation Rε Γ Q ClaimReport.exact ↔
      CompetentOn anchorQueryRelation Γ Q := by
  simpa using
    claim_admissible_exact_iff (R := anchorQueryRelation) (Rε := Rε) (Γ := Γ) (Q := Q)

/-- Admissible exact claims on posed anchor queries carry exact evidence. -/
theorem posed_anchor_exact_claim_requires_evidence
    (hExact : ClaimAdmissible anchorQueryRelation Rε Γ Q ClaimReport.exact) :
    Nonempty (EvidenceForReport anchorQueryRelation Rε Γ Q ClaimReport.exact) := by
  exact exact_claim_requires_evidence
    (R := anchorQueryRelation) (Rε := Rε) (Γ := Γ) (Q := Q) hExact

/-- Without exact competence, exact posed-query claims are inadmissible. -/
theorem posed_anchor_no_competence_no_exact_claim
    (hNo : ¬ CompetentOn anchorQueryRelation Γ Q) :
    ¬ ClaimAdmissible anchorQueryRelation Rε Γ Q ClaimReport.exact := by
  simpa using
    no_uncertified_exact_claim (R := anchorQueryRelation) (Rε := Rε) (Γ := Γ) (Q := Q) hNo

/-- Integrity gate: checker-accepted `true` verdict implies posed-query truth. -/
theorem posed_anchor_checked_true_implies_truth
    (hInt : SolverIntegrity anchorQueryRelation Q)
    (q : AnchorQueryObject A S n) (w : W)
    (hCheck : Q.check q true w) :
    q.truth := by
  have hRel : (q, true) ∈ anchorQueryRelation := hInt.2 q true w hCheck
  exact (anchor_query_relation_true_iff (q := q)).1 hRel

/-- Signal gate: positive certified confidence implies typed admissibility. -/
theorem posed_anchor_signal_positive_certified_implies_admissible
    (σ : ReportSignal Bool)
    (hSig : SignalConsistent anchorQueryRelation Rε Γ Q σ)
    (hPos : 0 < σ.certifiedPct.1) :
    ClaimAdmissible anchorQueryRelation Rε Γ Q σ.report := by
  exact signal_certified_positive_implies_admissible
    (R := anchorQueryRelation) (Rε := Rε) (Γ := Γ) (Q := Q) (σ := σ) hSig hPos

end AnchorQueryPosing

/-! ## Bridge boundary closure in the represented adjacent family (`#10`) -/

section BridgeBoundary

/-- Typed adjacent classes represented in the bridge section. -/
inductive BridgeTypedClass where
  | oneStepDeterministic
  | horizonExtended
  | stochasticCriterion
  | transitionCoupled
  deriving DecidableEq, Repr

/-- License predicate: only one-step deterministic class supports direct static transfer. -/
def bridgeTransferLicensed : BridgeTypedClass → Prop
  | .oneStepDeterministic => True
  | .horizonExtended => False
  | .stochasticCriterion => False
  | .transitionCoupled => False

/-- Exact boundary in the represented adjacent family: transfer is licensed iff one-step. -/
theorem bridge_transfer_iff_one_step_class (c : BridgeTypedClass) :
    bridgeTransferLicensed c ↔ c = BridgeTypedClass.oneStepDeterministic := by
  cases c <;> simp [bridgeTransferLicensed]

/-- Non-one-step classes carry explicit mechanized failure witnesses. -/
def bridgeFailureWitness : BridgeTypedClass → Prop
  | .oneStepDeterministic => False
  | .horizonExtended =>
      ¬ (∀ s s' : Fin 1 → Bool,
        TwoStepObjective.Opt horizonTwoWitness s = TwoStepObjective.Opt horizonTwoWitness s') ∧
      (horizonTwoWitness.toImmediateDecisionProblem).isSufficient (∅ : Finset (Fin 1))
  | .stochasticCriterion =>
      ¬ (∀ s s' : Fin 1 → Bool,
        StochasticCriterionObjective.OptChance stochasticWitness s =
          StochasticCriterionObjective.OptChance stochasticWitness s') ∧
      (stochasticWitness.toExpectedDecisionProblem).isSufficient (∅ : Finset (Fin 1))
  | .transitionCoupled =>
      ¬ (∀ s s' : Fin 1 → Bool,
        TransitionCoupledObjective.Opt transitionWitness s =
          TransitionCoupledObjective.Opt transitionWitness s') ∧
      (transitionWitness.toImmediateDecisionProblem).isSufficient (∅ : Finset (Fin 1))

/-- Every represented non-one-step class has a concrete bridge-failure witness. -/
theorem bridge_failure_witness_non_one_step
    (c : BridgeTypedClass) (hc : c ≠ BridgeTypedClass.oneStepDeterministic) :
    bridgeFailureWitness c := by
  cases c with
  | oneStepDeterministic =>
      cases hc rfl
  | horizonExtended =>
      simpa [bridgeFailureWitness] using horizon_gt_one_bridge_can_fail_on_sufficiency
  | stochasticCriterion =>
      simpa [bridgeFailureWitness] using stochastic_objective_bridge_can_fail_on_sufficiency
  | transitionCoupled =>
      simpa [bridgeFailureWitness] using transition_coupled_bridge_can_fail_on_sufficiency

/-- Packaged represented-family boundary result used by theorem-typed prose. -/
theorem bridge_boundary_represented_family :
    bridgeTransferLicensed BridgeTypedClass.oneStepDeterministic ∧
    bridgeFailureWitness BridgeTypedClass.horizonExtended ∧
    bridgeFailureWitness BridgeTypedClass.stochasticCriterion ∧
    bridgeFailureWitness BridgeTypedClass.transitionCoupled := by
  refine ⟨by simp [bridgeTransferLicensed], ?_, ?_, ?_⟩
  · simpa [bridgeFailureWitness] using horizon_gt_one_bridge_can_fail_on_sufficiency
  · simpa [bridgeFailureWitness] using stochastic_objective_bridge_can_fail_on_sufficiency
  · simpa [bridgeFailureWitness] using transition_coupled_bridge_can_fail_on_sufficiency

end BridgeBoundary

/-! ## Agent snapshot/process typing over the represented bridge family (`#11`) -/

section AgentSnapshotProcess

/-- Typed agent views used by scope prose:
`snapshotFixed` models fixed-parameter inference;
`process*` constructors model online/dynamical update regimes. -/
inductive AgentRegime where
  | snapshotFixed
  | processHorizonExtended
  | processStochasticCriterion
  | processTransitionCoupled
  deriving DecidableEq, Repr

/-- Projection from agent-typing vocabulary to represented bridge classes. -/
def agentBridgeClass : AgentRegime → BridgeTypedClass
  | .snapshotFixed => BridgeTypedClass.oneStepDeterministic
  | .processHorizonExtended => BridgeTypedClass.horizonExtended
  | .processStochasticCriterion => BridgeTypedClass.stochasticCriterion
  | .processTransitionCoupled => BridgeTypedClass.transitionCoupled

/-- In the represented family, transfer license is equivalent to snapshot typing. -/
theorem agent_transfer_licensed_iff_snapshot (r : AgentRegime) :
    bridgeTransferLicensed (agentBridgeClass r) ↔ r = AgentRegime.snapshotFixed := by
  cases r <;> simp [agentBridgeClass, bridgeTransferLicensed]

/-- Every process-typed represented class has an explicit bridge-failure witness. -/
theorem process_bridge_failure_witness
    (r : AgentRegime) (hr : r ≠ AgentRegime.snapshotFixed) :
    bridgeFailureWitness (agentBridgeClass r) := by
  cases r with
  | snapshotFixed =>
      cases hr rfl
  | processHorizonExtended =>
      simpa [agentBridgeClass] using
        bridge_failure_witness_non_one_step
          (c := BridgeTypedClass.horizonExtended) (hc := by decide)
  | processStochasticCriterion =>
      simpa [agentBridgeClass] using
        bridge_failure_witness_non_one_step
          (c := BridgeTypedClass.stochasticCriterion) (hc := by decide)
  | processTransitionCoupled =>
      simpa [agentBridgeClass] using
        bridge_failure_witness_non_one_step
          (c := BridgeTypedClass.transitionCoupled) (hc := by decide)

/-- Packaged snapshot/process boundary result used by theorem-indexed prose. -/
theorem snapshot_vs_process_typed_boundary :
    bridgeTransferLicensed (agentBridgeClass AgentRegime.snapshotFixed) ∧
    bridgeFailureWitness (agentBridgeClass AgentRegime.processHorizonExtended) ∧
    bridgeFailureWitness (agentBridgeClass AgentRegime.processStochasticCriterion) ∧
    bridgeFailureWitness (agentBridgeClass AgentRegime.processTransitionCoupled) := by
  refine ⟨by simp [agentBridgeClass, bridgeTransferLicensed], ?_, ?_, ?_⟩
  · exact process_bridge_failure_witness
      (r := AgentRegime.processHorizonExtended) (hr := by decide)
  · exact process_bridge_failure_witness
      (r := AgentRegime.processStochasticCriterion) (hr := by decide)
  · exact process_bridge_failure_witness
      (r := AgentRegime.processTransitionCoupled) (hr := by decide)

end AgentSnapshotProcess

/-! ## Regime simulation abstraction (`#12`) -/

section RegimeSimulation

/-- Generic simulation relation between two regime-typed solver obligations.
`R₁` simulates `R₂` when any solver for `R₁` induces a solver for `R₂`. -/
def RegimeSimulation (R₁ R₂ : Prop) : Prop := R₁ → R₂

/-- Generic transfer rule: if `R₁` simulates `R₂`, hardness of `R₂`
transfers to hardness of `R₁`. -/
theorem regime_simulation_transfers_hardness
    {R₁ R₂ : Prop}
    (hSim : RegimeSimulation R₁ R₂)
    (hHard₂ : ¬ R₂) :
    ¬ R₁ := by
  intro hR₁
  exact hHard₂ (hSim hR₁)

/-- Restriction-map simulation instance used by subproblem-to-full transfer. -/
theorem subproblem_transfer_as_regime_simulation
    {HasFullSolver HasSubSolver : Prop}
    (hRestrict : HasFullSolver → HasSubSolver) :
    RegimeSimulation HasFullSolver HasSubSolver :=
  hRestrict

/-- Oracle-transducer simulation instance: batch-view indistinguishability
induces value-entry indistinguishability on touched states. -/
theorem oracle_lattice_transfer_as_regime_simulation
    {n : ℕ}
    (Q : Finset (ValueQueryState n))
    (dp₁ dp₂ : DecisionProblem Bool (Fin n → Bool)) :
    RegimeSimulation
      (stateBatchView (Q := touchedStates Q) dp₁ = stateBatchView (Q := touchedStates Q) dp₂)
      (valueEntryView Q dp₁ = valueEntryView Q dp₂) := by
  intro hBatch
  exact valueEntryView_eq_of_stateBatchView_eq_on_touched
    (Q := Q) (dp₁ := dp₁) (dp₂ := dp₂) hBatch

end RegimeSimulation

/-! ## Subproblem-to-full transfer closure (`#2`) -/

section SubproblemTransfer

/-- Generic transfer principle:
hardness of a subproblem lifts to the full problem whenever every full solver
induces a solver for the subproblem. -/
theorem subproblem_hardness_lifts_to_full
    {HasFullSolver HasSubSolver : Prop}
    (hRestrict : HasFullSolver → HasSubSolver)
    (hSubHard : ¬ HasSubSolver) :
    ¬ HasFullSolver := by
  exact regime_simulation_transfers_hardness
    (hSim := subproblem_transfer_as_regime_simulation hRestrict)
    (hHard₂ := hSubHard)

end SubproblemTransfer

/-! ## Selector / epsilon transfer-separation (`#6`) -/

section SelectorAndEpsilon

variable {A S : Type*} {n : ℕ} [CoordinateSpace S n]

/-- ε-optimal action set. -/
def DecisionProblem.epsOpt (dp : DecisionProblem A S) (ε : ℝ) (s : S) : Set A :=
  { a : A | ∀ a' : A, dp.utility a' s ≤ dp.utility a s + ε }

/-- ε-sufficiency: projection agreement preserves ε-optimal sets. -/
def DecisionProblem.isEpsilonSufficient (dp : DecisionProblem A S)
    (ε : ℝ) (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I →
    DecisionProblem.epsOpt dp ε s = DecisionProblem.epsOpt dp ε s'

theorem DecisionProblem.epsOpt_zero_eq_opt (dp : DecisionProblem A S) (s : S) :
    DecisionProblem.epsOpt dp 0 s = dp.Opt s := by
  ext a
  simp [DecisionProblem.epsOpt, DecisionProblem.Opt, DecisionProblem.isOptimal]

theorem DecisionProblem.sufficient_iff_zeroEpsilonSufficient
    (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    dp.isSufficient I ↔ DecisionProblem.isEpsilonSufficient dp 0 I := by
  constructor
  · intro hI
    intro s s' hs
    simpa [DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s,
      DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s'] using hI s s' hs
  · intro hI
    intro s s' hs
    simpa [DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s,
      DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s'] using hI s s' hs

/-! ### Explicit selector-level separation witness -/

private def i0 : Fin 1 := ⟨0, by decide⟩
private def sFalse : Fin 1 → Bool := fun _ => false
private def sTrue : Fin 1 → Bool := fun _ => true

/-- Witness problem where selector-level sufficiency can hold while set-level
sufficiency fails (for `I = ∅`). -/
def selectorGapProblem : DecisionProblem Bool (Fin 1 → Bool) where
  utility := fun a s =>
    if s i0 then
      if a = true then 1 else 1
    else
      if a = true then 1 else 0

noncomputable def preferTrueSelector (X : Set Bool) : Bool := by
  classical
  exact if (true : Bool) ∈ X then true else false

theorem selectorGap_true_mem_opt (s : Fin 1 → Bool) :
    (true : Bool) ∈ (selectorGapProblem.Opt s) := by
  unfold selectorGapProblem DecisionProblem.Opt DecisionProblem.isOptimal
  intro a'
  cases a' <;> by_cases hs : s i0 <;> simp [hs]

theorem selectorGap_selectorSufficient_empty :
    selectorGapProblem.isSelectorSufficient preferTrueSelector (∅ : Finset (Fin 1)) := by
  intro s s' _
  unfold DecisionProblem.SelectedAction preferTrueSelector
  have hs : (true : Bool) ∈ selectorGapProblem.Opt s := selectorGap_true_mem_opt s
  have hs' : (true : Bool) ∈ selectorGapProblem.Opt s' := selectorGap_true_mem_opt s'
  simp [hs, hs']

theorem selectorGap_not_set_sufficient_empty :
    ¬ selectorGapProblem.isSufficient (∅ : Finset (Fin 1)) := by
  intro hsuff
  have hconst :=
    (DecisionProblem.emptySet_sufficient_iff_constant (dp := selectorGapProblem)).1 hsuff
  have hEq : selectorGapProblem.Opt sFalse = selectorGapProblem.Opt sTrue := hconst sFalse sTrue
  have hFalseInTrue : (false : Bool) ∈ selectorGapProblem.Opt sTrue := by
    unfold selectorGapProblem DecisionProblem.Opt DecisionProblem.isOptimal sTrue i0
    intro a'
    cases a' <;> simp
  have hFalseNotInFalse : (false : Bool) ∉ selectorGapProblem.Opt sFalse := by
    intro hmem
    have h := hmem true
    unfold selectorGapProblem sFalse i0 at h
    norm_num at h
  have hFalseInFalse : (false : Bool) ∈ selectorGapProblem.Opt sFalse := by
    simpa [hEq] using hFalseInTrue
  exact hFalseNotInFalse hFalseInFalse

theorem selectorSufficient_not_implies_setSufficient :
    ∃ (dp : DecisionProblem Bool (Fin 1 → Bool))
      (σ : Set Bool → Bool) (I : Finset (Fin 1)),
      dp.isSelectorSufficient σ I ∧ ¬ dp.isSufficient I := by
  refine ⟨selectorGapProblem, preferTrueSelector, ∅, ?_⟩
  exact ⟨selectorGap_selectorSufficient_empty, selectorGap_not_set_sufficient_empty⟩

end SelectorAndEpsilon

/-! ## Assumption ledger projection (`#8`) -/

section AssumptionLedger

theorem standard_assumption_ledger_unpack
    {TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP RelevantCard_coNP
      RelevantCard_coNP_complete ExistsForallSAT_sigma2p_complete ETH : Prop}
    (hStd : StandardComplexityAssumptions TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP
      RelevantCard_coNP RelevantCard_coNP_complete
      ExistsForallSAT_sigma2p_complete ETH) :
    TAUTOLOGY_coNP_complete ∧ SUFFICIENCY_in_coNP ∧ RelevantCard_coNP ∧
      RelevantCard_coNP_complete ∧ ExistsForallSAT_sigma2p_complete ∧ ETH := by
  refine ⟨hStd.hTautologyCoNPComplete, hStd.hSufficiencyInCoNP, hStd.hRelevantCardCoNP,
    hStd.hRelevantCardCoNPComplete, hStd.hExistsForallSATSigma2PComplete, hStd.hETH⟩

end AssumptionLedger

/-! ## Discrete Spacetime Chain Exports (`DS1`--`DS6`)

Re-exports from Physics.DiscreteSpacetime for paper claim handles.
-/

section DiscreteSpacetimeExports

open Physics.DiscreteSpacetime

/-- DS1: Transition points are countable (discrete effective time). -/
abbrev DS1 := @transitionPoints_countable

/-- DS2: Non-trivial dynamics implies at least one bit operation eventually. -/
abbrev DS2 := @nontrivial_implies_bit_operation

/-- DS3: Lorentz invariance: discrete time implies discrete space. -/
abbrev DS3 := @lorentz_time_implies_space

/-- DS4: Lorentz invariance: discrete space implies discrete time. -/
abbrev DS4 := @lorentz_space_implies_time

/-- DS5: Full computational-physical bundle (discrete time + space + energy). -/
abbrev DS5 := @computational_physical_bundle

/-- DS6: Non-trivial computation has energy cost. -/
abbrev DS6 := @nontrivial_computation_has_energy_cost

end DiscreteSpacetimeExports

/-! ## Decision Equivalence Exports (`DE1`--`DE4`)

Re-exports from Physics.DecisionEquivalence for paper claim handles.
Decision = State Transition = Bit Operation = Thermodynamic Event
-/

section DecisionEquivalenceExports

open Physics.DecisionEquivalence

/-- DE1: Decision ↔ Transition (definitional equivalence). -/
abbrev DE1 := @decision_iff_transition

/-- DE2: Decision count = Bit operation count. -/
abbrev DE2 := @decisionCount_eq_bitOperations

/-- DE3: Positive decisions → positive energy cost. -/
abbrev DE3 := @positive_decisions_positive_energy

/-- DE4: Full four-way equivalence bundle. -/
abbrev DE4 := @decision_thermodynamic_equivalence

end DecisionEquivalenceExports

/-! ## Decision Circuit Integrity Exports (`IE1`--`IE13`)

Re-exports from Physics.DecisionCircuit for paper claim handles.
Integrity = bit-erase resistance; competence = work/cycle; Landauer constraint.
Temporal equilibrium; low-competence survival; phase transitions.
-/

section DecisionCircuitExports

open Physics.DecisionCircuit

/-- IE1: Acknowledgment chosen iff predicted integrity ≥ dismissal integrity. -/
abbrev IE1 := @acknowledge_iff_integrity_geq

/-- IE2: At equilibrium, acknowledgment is self-reinforcing. -/
abbrev IE2 := @equilibrium_acknowledge_reinforcing

/-- IE3: Low theorem count → dismissal chosen. -/
abbrev IE3 := @low_theorems_dismiss

/-- IE4: High theorem count → acknowledgment chosen. -/
abbrev IE4 := @high_theorems_acknowledge

/-- IE5: Theorem count inverts equilibrium (dismiss → acknowledge). -/
abbrev IE5 := @theorems_invert_equilibrium

/-- IE6: Landauer trap: dismissal fails when erasure cost exceeds competence. -/
abbrev IE6 := @dismissal_requires_competence

/-- IE7: Integrity self-preservation: circuits persist when erasure unaffordable. -/
abbrev IE7 := @integrity_self_preserving

/-- IE8: Low-competence attacks fail against high-integrity targets. -/
abbrev IE8 := @low_competence_attack_fails

/-- IE9: Integral circuits survive when all attackers lack competence. -/
abbrev IE9 := @integral_circuit_survives

/-- IE10: Integrity predicts future integrity (temporal equilibrium). -/
abbrev IE10 := @integrity_predicts_future_integrity

/-- IE11: Defection reduces future integrity probability. -/
abbrev IE11 := @defection_reduces_future_integrity

/-- IE12: Pre-publication equilibrium is neutral. -/
abbrev IE12 := @pre_pub_neutral

/-- IE13: Publication induces phase transition to integrity-dominated equilibrium. -/
abbrev IE13 := @publication_phase_transition

/-- IE14: Zero-integrity circuits have zero erasure cost. -/
abbrev IE14 := @zero_integrity_no_cost

/-- IE15: Zero-integrity circuits can be corrupted by any competence. -/
abbrev IE15 := @zero_integrity_freely_corruptible

/-- IE16: Zero-integrity circuits have no coherence constraint. -/
abbrev IE16 := @zero_integrity_no_coherence_constraint

/-- IE17: Integrity is prerequisite for logical coherence. -/
abbrev IE17 := @integrity_prerequisite_for_coherence

/-! ### Cycle Cost Theorems (CC1-CC12)

Every state transition costs energy. Derived from Landauer bound.
-/

-- CC1: Landauer bound (physical constant). kT_ln2 > 0 is the energy per erased bit.
-- Embedded in transitionCost; any cost bound carries kT_ln2 > 0 explicitly (see CC3).

-- CC2: Irreversible state change erases information. Embedded in transitionCost:
-- s ≠ s' → cost = max(1, s.bits) * kT_ln2 > 0 under kT_ln2 > 0 (see CC3).

/-- CC3: Every state transition costs at least 1 unit. -/
abbrev CC3 := @cycle_cost_lower_bound

/-- CC4: Zero cost ↔ identical states. -/
abbrev CC4 := @zero_cost_iff_identity

/-- CC5: No free state change. Zero cost implies no transition. -/
abbrev CC5 := @no_free_state_change

/-- CC6: Every observation costs at least 1 unit. -/
abbrev CC6 := @observation_costs_energy

/-- CC7: Computation cost ≥ number of steps. -/
abbrev CC7 := @computation_cost_lower_bound

/-- CC8: No free computation. Zero cost means zero steps. -/
abbrev CC8 := @no_free_computation

/-- CC9: k transitions cost ≥ k units. -/
abbrev CC9 := @k_transitions_cost_k

/-- CC10: State persistence has zero transition cost. -/
abbrev CC10 := @persistence_zero_cost

/-- CC11: Every decision circuit cycle costs energy. -/
abbrev CC11 := @decision_circuit_cycle_costs_energy

/-- CC12: Running a pipeline costs energy. -/
abbrev CC12 := @pipeline_costs_energy

/-! ### Structural Asymmetry Theorems (SR1-SR5)

Integrity is self-referential; competence is self-identical.
The gap between them is where choice lives.
-/

/-- SR1: Competence is self-identical. c = c. -/
abbrev SR1 := @competence_self_identical

/-- SR2: Integrity has temporal self-reference. -/
abbrev SR2 := @integrity_self_reference

/-- SR3: The asymmetry exists. Integrity has structure competence lacks. -/
abbrev SR3 := @integrity_competence_asymmetry

/-- SR4: Competence can be imported (external resource). -/
abbrev SR4 := @competence_importable

/-- SR5: Integrity cannot be imported (must be self-generated). -/
abbrev SR5 := @integrity_not_importable

/-! ### Gap Energy Theorems (GE1-GE9)

The gap between integrity (self-referential) and competence (self-identical) has energy cost.
Gap energy = H(I_{t+1} | I_t) × kT ln 2. Every choice pays.
-/

/-- GE1: Gap entropy structure (conditional entropy). -/
abbrev GE1 := @GapEntropy

/-- GE2: Gap energy = gap entropy × Landauer unit. -/
abbrev GE2 := @gapEnergy

/-- GE3: Every choice pays gap energy. -/
abbrev GE3 := @choice_pays_gap_energy

/-- GE4: Zero gap = zero cost (deterministic). -/
abbrev GE4 := @zero_gap_zero_cost

/-- GE5: Positive gap = positive cost. -/
abbrev GE5 := @positive_gap_positive_cost

/-- GE6: Gap cost is monotonic in entropy. -/
abbrev GE6 := @gap_cost_monotonic

/-- GE7: Gap is where choice lives. -/
abbrev GE7 := @gap_is_choice

/-- GE8: Competence has no gap energy. -/
abbrev GE8 := @competence_no_gap_energy

/-- GE9: Integrity gap bounded by integrity bits. -/
abbrev GE9 := @integrity_gap_bounded

/-! ### Decision Quotient Theorems (DQ1-DQ8)

Decision Quotient = Mutual Information / Total Uncertainty
                  = 1 - Gap / Total
Derived from Bayes/information theory. Measures decision relevance.
-/

/-- DQ1: Mutual information between current and future integrity. -/
abbrev DQ1 := @mutualInformation

/-- DQ2: Decision quotient structure. -/
abbrev DQ2 := @DecisionQuotient

/-- DQ3: DQ from gap entropy. -/
abbrev DQ3 := @dq_from_gap

/-- DQ4: Zero gap = DQ 1 (deterministic). -/
abbrev DQ4 := @zero_gap_dq_one

/-- DQ5: Max gap = DQ 0 (pure noise). -/
abbrev DQ5 := @max_gap_dq_zero

/-- DQ6: DQ + Gap = Total (complementary). -/
abbrev DQ6 := @dq_gap_complementary

/-- DQ7: DQ monotonic in gap reduction. -/
abbrev DQ7 := @dq_monotonic_in_gap

/-- DQ8: DQ has thermodynamic interpretation. -/
abbrev DQ8 := @dq_energy_interpretation

end DecisionCircuitExports

/-! ## Molecular Integrity Exports (MI1-MI5) -/

section MolecularIntegrityExports
open Physics.MolecularIntegrity

/-- MI1: Chemical stability is integrity trap at molecular scale. -/
abbrev MI1 := @stability_is_integrity_trap

/-- MI2: Low-energy environments preserve high-integrity molecules. -/
abbrev MI2 := @low_competence_preserves_integrity

/-- MI3: Reactions require sufficient environmental competence. -/
abbrev MI3 := @reaction_requires_competence

/-- MI4: High-barrier configurations persist. -/
abbrev MI4 := @high_barrier_persistence

/-- MI5: DNA persists at room temperature by integrity trap. -/
abbrev MI5 := @dna_persists_room_temp

end MolecularIntegrityExports

/-! ## Self-Erosion Exports (SE1-SE6)

Computation is self-consuming. Heat generation degrades the substrate.
-/

section SelfErosionExports
open DecisionQuotient.Physics.DecisionCircuit

/-- SE1: Every computational cycle generates at least 1 unit of heat (Landauer). -/
abbrev SE1 := @SE1_heat_per_cycle_lb

/-- SE2: Cumulative heat grows linearly with cycles. -/
abbrev SE2 := @SE2_cumulative_heat

/-- SE3: Heat above threshold causes substrate bit erasure. -/
abbrev SE3 := @SE3_heat_causes_degradation

/-- SE4: Degradation reduces substrate integrity. -/
abbrev SE4 := @SE4_degradation_reduces_integrity

/-- SE5: Finite integrity + finite heat capacity → bounded lifetime. -/
abbrev SE5 := @SE5_finite_lifetime

/-- SE6: Faster computation generates more heat per unit time. -/
abbrev SE6 := @SE6_speed_integrity_tradeoff

/-- SE6_cor: Faster circuits degrade faster when heat exceeds capacity. -/
abbrev SE6_cor := @SE6_cor_faster_degrades_faster

end SelfErosionExports

/-! ## Channel Capacity Exports (CH1-CH6)

A regime is a channel. Competence is channel capacity.
Only decision circuits have competence.
-/

section ChannelCapacityExports
open DecisionQuotient.Physics.DecisionCircuit

/-- CH1: Competence IS channel capacity for decision circuits. -/
abbrev CH1 := @CH1_competence_is_capacity

/-- CH2: Substrate degradation reduces channel capacity. -/
abbrev CH2 := @CH2_degradation_reduces_capacity

/-- CH3: Zero capacity means no decisions possible. -/
abbrev CH3 := @CH3_zero_capacity_no_decisions

/-- CH5: Decision circuits are distinguished by requiring competence. -/
abbrev CH5 := @CH5_decision_circuits_need_competence

/-- CH6: Channel capacity degrades at the rate of substrate erosion. -/
abbrev CH6 := @CH6_capacity_degrades_with_substrate

end ChannelCapacityExports

/-! ## Investment Exports (IV1-IV6)

Economic theorems: growth requires time, conservation bounds receipts,
deficit transfer creates deficit at source.
-/

section InvestmentExports
open DecisionQuotient.Physics.DecisionCircuit

/-- IV1: Investment requires upfront cost. -/
abbrev IV1 := @IV1_investment_requires_payment

/-- IV2: Growth requires time. -/
abbrev IV2 := @IV2_growth_requires_time

/-- IV3: More time means more growth. -/
abbrev IV3 := @IV3_time_increases_growth

/-- IV4: Conservation bounds receipts. -/
abbrev IV4 := @IV4_conservation

/-- IV5: Deficit transfer requires external source. -/
abbrev IV5 := @IV5_deficit_requires_source

/-- IV6: Deficit transfer creates deficit at source. -/
abbrev IV6 := @IV6_deficit_at_source

end InvestmentExports

/-!
## Atomic Circuit Exports (AC1-AC11)
Matter as agent: atoms, electrons, molecules as decision circuits.
-/

namespace AtomicCircuitExports

open DecisionQuotient.Physics.AtomicCircuit

/-- AC1: Orbital transition is a state transition. -/
abbrev AC1 := @AC1_orbital_transition_is_state_transition

/-- AC3: Upward transition requires energy input. -/
abbrev AC3 := @AC3_upward_costs

/-- AC4: Downward transition releases energy. -/
abbrev AC4 := @AC4_downward_releases

/-- AC5: Transitioning atom is an agent. -/
abbrev AC5 := @AC5_transitioning_atom_is_agent

/-- AC6: Ground-state atom is passive. -/
abbrev AC6 := @AC6_ground_state_is_passive

/-- AC8: Symmetry tractability — orbit types reduce state space. -/
abbrev AC8 := @AC8_symmetry_tractability

/-- AC9: Matter moves matter by paying transition cost. -/
abbrev AC9 := @AC9_matter_moves_matter

/-- AC11: No free matter movement. -/
abbrev AC11 := @AC11_no_free_movement

end AtomicCircuitExports

-- ============================================================================
-- Information Access Exports (IA1-IA6)
-- Pure information-theoretic argument: logic is complete, access isn't.
-- ============================================================================

section InformationAccessExports
open DecisionQuotient.Physics.InformationAccess

/-- IA1: Total information exists — the system has definite entropy. -/
abbrev IA1 := @IA1_total_exists

/-- IA2: Channel capacity bounds access. -/
abbrev IA2 := @IA2_capacity_bounds_access

/-- IA3: When total exceeds capacity, gap is positive. -/
abbrev IA3 := @IA3_gap_when_exceeds

/-- IA4: The gap is physical, not logical. -/
abbrev IA4 := @IA4_gap_is_physical

/-- IA5: Competence bounded by access. -/
abbrev IA5 := @IA5_competence_bounded

/-- IA6: Logic is complete; access isn't. -/
abbrev IA6 := @IA6_logic_complete_access_not

end InformationAccessExports

-- ============================================================================
-- Dimensional Complexity Exports (DC1-DC15)
-- Each tractable subcase is a complexity class that collapses to P.
-- ============================================================================

section DimensionalComplexityExports

open Physics.DimensionalComplexity

/-- DC1: Each tractable subcase is a complexity class → P. -/
abbrev DC1 := @subcaseComplexity

/-- DC2: Bounded actions → complexity class P. -/
abbrev DC2 := @DC2_bounded_actions_class

/-- DC3: Separable utility → complexity class P. -/
abbrev DC3 := @DC3_separable_class

/-- DC4: Low tensor rank → complexity class P. -/
abbrev DC4 := @DC4_low_rank_class

/-- DC5: Tree structure → complexity class P. -/
abbrev DC5 := @DC5_tree_class

/-- DC6: Bounded treewidth → complexity class P. -/
abbrev DC6 := @DC6_treewidth_class

/-- DC7: Coordinate symmetry → complexity class P. -/
abbrev DC7 := @DC7_symmetry_class

/-- DC8: Fixed topology (stationary) preserves tractability. -/
abbrev DC8 := @DC8_stationary_topology

/-- DC9: Motion adds dimension, may break tractability. -/
abbrev DC9 := @DC9_motion_adds_dimension

/-- DC10: Tractability = bounded effective dimension. -/
abbrev DC10 := @isTractable

/-- DC11: Tractable ↔ in complexity class P. -/
abbrev DC11 := @DC11_tractable_is_P

/-- DC12: Untractable stays in base complexity class. -/
abbrev DC12 := @DC12_untractable_base

/-- DC13: All 6 subcases collapse to P. -/
abbrev DC13 := @DC13_all_subcases_P

/-- DC14: Dimension bound determines complexity class. -/
abbrev DC14 := @DC14_dimension_determines_class

/-- DC15: Complexity hierarchy P ⊂ coNP ⊂ PP ⊂ PSPACE. -/
abbrev DC15 := @DC15_complexity_hierarchy

end DimensionalComplexityExports

/-! ## Anchor Query Handle Exports (AQ1-AQ8)

These provide compact handles for the posed-anchor query object and its
typed-claim/signal/integrity links.
-/

section AnchorQueryExports

/-- AQ1: Posing constructs a formal anchor-query object with preserved components. -/
abbrev AQ1 := @pose_returns_anchor_query_object

/-- AQ2: Posed anchor-query truth iff existential anchor witness. -/
abbrev AQ2 := @posed_anchor_query_truth_iff_exists_anchor

/-- AQ3: Posed anchor-query truth iff the corresponding ∃∀ condition. -/
abbrev AQ3 := @posed_anchor_query_truth_iff_exists_forall

/-- AQ4: Exact admissibility on posed queries iff competence. -/
abbrev AQ4 := @posed_anchor_exact_claim_admissible_iff_competent

/-- AQ5: Admissible exact posed-query claims require evidence. -/
abbrev AQ5 := @posed_anchor_exact_claim_requires_evidence

/-- AQ6: No competence implies no admissible exact posed-query claim. -/
abbrev AQ6 := @posed_anchor_no_competence_no_exact_claim

/-- AQ7: Under integrity, checker-accepted `true` verdict implies posed-query truth. -/
abbrev AQ7 := @posed_anchor_checked_true_implies_truth

/-- AQ8: Positive certified-confidence signal implies typed admissibility. -/
abbrev AQ8 := @posed_anchor_signal_positive_certified_implies_admissible

end AnchorQueryExports

/-! ## Decision Problem Handle Exports (DP6-DP8)

These provide paper-compatible handles for the foundational sufficiency theorems.
-/

section DecisionProblemExtras

/-- DP6: Empty-set sufficiency iff constant decision boundary (Bool-coordinate instance). -/
abbrev DP6 := @DecisionProblem.emptySet_sufficient_iff_constant Bool (Fin 2 → Bool) 2 (functionCoordinateSpace Bool 2)

/-- DP7: Non-sufficiency iff counterexample witness (Bool-coordinate instance). -/
abbrev DP7 := @DecisionProblem.not_sufficient_iff_exists_counterexample Bool (Fin 2 → Bool) 2 (functionCoordinateSpace Bool 2)

/-- DP8: Empty-set non-sufficiency iff distinct optimal sets (Bool-coordinate instance). -/
abbrev DP8 := @DecisionProblem.emptySet_not_sufficient_iff_exists_opt_difference Bool (Fin 2 → Bool) 2 (functionCoordinateSpace Bool 2)

end DecisionProblemExtras

end ClaimClosure
end DecisionQuotient
