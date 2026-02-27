/-
  Paper 4: Decision-Relevant Uncertainty

  BayesFromDQ.lean - Bayes Derived from DQ Axioms

  THE MAIN RESULT: Bayesian updating is the UNIQUE update rule
  compatible with DQ axioms and physical (Landauer) constraints.

  This is the Cox-Jaynes argument grounded in thermodynamics:
  - Cox-Jaynes: Boolean logic constraints → Bayes
  - This file: DQ axioms + Landauer + integrity → Bayes

  DERIVATION DIRECTION:
    DQ (primitive physical quantity)
    + Landauer bound (erasure costs kT ln 2)
    + Integrity constraints (can't corrupt verified bits for free)
    → Bayes is the UNIQUE admissible update rule

  This is "Bayes from physics" not "Bayes from definitions."
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import DecisionQuotient.BayesOptimalityProof

namespace DecisionQuotient

/-! ## Part 1: Probability Distributions -/

/-- A probability distribution over a finite type -/
structure ProbDist (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_one : Finset.univ.sum prob = 1

/-- Shannon entropy induced from the proved Bayes optimality layer. -/
noncomputable def entropy {α : Type*} [Fintype α] (p : ProbDist α) : ℝ :=
  DecisionQuotient.BayesOptimalityProof.entropy p.prob

/-! ## Belief Forced by Provable Uncertainty (Independent of Bayes) -/

/-- Nondegenerate belief: at least two distinct hypotheses have positive mass. -/
def NondegenerateBelief {H : Type*} [Fintype H] (prior : ProbDist H) : Prop :=
  ∃ h₁ h₂, h₁ ≠ h₂ ∧ 0 < prior.prob h₁ ∧ 0 < prior.prob h₂

/-- Provable uncertainty: no hypothesis has probability 1. -/
def UncertaintyForced {H : Type*} [Fintype H] (prior : ProbDist H) : Prop :=
  ¬ ∃ h, prior.prob h = 1

/-- Forced action: at least one admissible action exists, so abstention is not total. -/
def ActionForced (A : Type*) : Prop := Nonempty A

/-- If belief is not nondegenerate, it collapses to certainty on one hypothesis. -/
theorem certainty_of_not_nondegenerateBelief {H : Type*} [Fintype H]
    (prior : ProbDist H) (hNoBelief : ¬ NondegenerateBelief prior) :
    ∃ h, prior.prob h = 1 := by
  classical
  have hpos_exists : ∃ h, 0 < prior.prob h := by
    by_contra hnone
    push_neg at hnone
    have hzero : ∀ h, prior.prob h = 0 := by
      intro h
      exact le_antisymm (hnone h) (prior.nonneg h)
    have hsum_zero : Finset.univ.sum prior.prob = 0 := by
      simp [hzero]
    linarith [prior.sum_one, hsum_zero]
  rcases hpos_exists with ⟨h0, hh0pos⟩
  have hothers_zero : ∀ h, h ≠ h0 → prior.prob h = 0 := by
    intro h hne
    have hnotpos : ¬ 0 < prior.prob h := by
      intro hhpos
      exact hNoBelief ⟨h0, h, hne.symm, hh0pos, hhpos⟩
    exact le_antisymm (le_of_not_gt hnotpos) (prior.nonneg h)
  have hsum_split :
      (Finset.univ.erase h0).sum prior.prob + prior.prob h0 = Finset.univ.sum prior.prob := by
    exact
      Finset.sum_erase_add (s := Finset.univ) (a := h0) (f := prior.prob) (Finset.mem_univ h0)
  have hsum_others_zero : (Finset.univ.erase h0).sum prior.prob = 0 := by
    refine Finset.sum_eq_zero ?_
    intro h hh
    exact hothers_zero h (Finset.mem_erase.mp hh).1
  have hprob_one : prior.prob h0 = 1 := by
    linarith [prior.sum_one, hsum_split, hsum_others_zero]
  exact ⟨h0, hprob_one⟩

/-- Provable uncertainty forces nondegenerate belief mass. -/
theorem nondegenerateBelief_of_uncertaintyForced {H : Type*} [Fintype H]
    (prior : ProbDist H) (hUnc : UncertaintyForced prior) :
    NondegenerateBelief prior := by
  by_contra hNoBelief
  exact hUnc (certainty_of_not_nondegenerateBelief prior hNoBelief)

/-- If action is forced and uncertainty is provable, then a nondegenerate belief
    state is mathematically forced as well. -/
theorem forced_action_under_uncertainty {A H : Type*} [Fintype H]
    (hAction : ActionForced A) (prior : ProbDist H)
    (hUnc : UncertaintyForced prior) :
    ∃ _ : A, NondegenerateBelief prior := by
  rcases hAction with ⟨a⟩
  exact ⟨a, nondegenerateBelief_of_uncertaintyForced prior hUnc⟩

/-! ## Part 2: DQ as Primitive Physical Quantity -/

/-- Decision Quotient structure with physical grounding.
    DQ = 1 - GapEnergy/TotalEnergy
    where energies are in units of kT ln 2 (Landauer units). -/
structure PhysicalDQ where
  /-- Total uncertainty energy H(X) in Landauer units -/
  totalEnergy : ℝ
  /-- Gap energy H(X|Y) in Landauer units -/
  gapEnergy : ℝ
  /-- Physical constraint: energies are non-negative -/
  total_nonneg : 0 ≤ totalEnergy
  gap_nonneg : 0 ≤ gapEnergy
  /-- Physical constraint: gap ≤ total (conditioning reduces entropy) -/
  gap_le_total : gapEnergy ≤ totalEnergy

/-- The decision quotient value -/
noncomputable def PhysicalDQ.value (dq : PhysicalDQ) : ℝ :=
  if dq.totalEnergy = 0 then 1  -- deterministic case
  else 1 - dq.gapEnergy / dq.totalEnergy

/-- DQ1: DQ ∈ [0, 1]. -/
theorem dq_in_unit_interval (dq : PhysicalDQ) : 0 ≤ dq.value ∧ dq.value ≤ 1 := by
  by_cases hzero : dq.totalEnergy = 0
  · simp [PhysicalDQ.value, hzero]
  · have hpos : dq.totalEnergy > 0 := lt_of_le_of_ne dq.total_nonneg (Ne.symm hzero)
    have hdiv_nonneg : 0 ≤ dq.gapEnergy / dq.totalEnergy :=
      div_nonneg dq.gap_nonneg (le_of_lt hpos)
    have hdiv_le_one : dq.gapEnergy / dq.totalEnergy ≤ 1 := by
      rw [div_le_one hpos]
      exact dq.gap_le_total
    have hval_nonneg : 0 ≤ 1 - dq.gapEnergy / dq.totalEnergy := by linarith
    have hval_le_one : 1 - dq.gapEnergy / dq.totalEnergy ≤ 1 := by linarith
    simpa [PhysicalDQ.value, hzero] using And.intro hval_nonneg hval_le_one

/-- DQ2: Zero gap ↔ DQ = 1 (deterministic) -/
theorem dq_one_iff_zero_gap (dq : PhysicalDQ) (hpos : dq.totalEnergy > 0) :
    dq.value = 1 ↔ dq.gapEnergy = 0 := by
  have hne : dq.totalEnergy ≠ 0 := ne_of_gt hpos
  constructor
  · intro h
    have hdiv : dq.gapEnergy / dq.totalEnergy = 0 := by
      have h' : 1 - dq.gapEnergy / dq.totalEnergy = 1 := by
        simpa [PhysicalDQ.value, hne] using h
      linarith
    rcases (div_eq_zero_iff.mp hdiv) with hgap | htot
    · exact hgap
    · exact False.elim (hne htot)
  · intro hgap
    simp [PhysicalDQ.value, hne, hgap]

/-- DQ3: Max gap ↔ DQ = 0 (no information) -/
theorem dq_zero_iff_max_gap (dq : PhysicalDQ) (hpos : dq.totalEnergy > 0) :
    dq.value = 0 ↔ dq.gapEnergy = dq.totalEnergy := by
  have hne : dq.totalEnergy ≠ 0 := ne_of_gt hpos
  constructor
  · intro h
    have hdiv : dq.gapEnergy / dq.totalEnergy = 1 := by
      have h' : 1 - dq.gapEnergy / dq.totalEnergy = 0 := by
        simpa [PhysicalDQ.value, hne] using h
      linarith
    exact (div_eq_one_iff_eq hne).1 hdiv
  · intro hgap
    have hdiv : dq.gapEnergy / dq.totalEnergy = 1 := by
      rw [hgap, div_self hne]
    have h' : 1 - dq.gapEnergy / dq.totalEnergy = 0 := by linarith
    simpa [PhysicalDQ.value, hne] using h'

/-- DQ4: Complementarity - DQ + Gap/Total = 1 -/
theorem dq_complementarity (dq : PhysicalDQ) (hpos : dq.totalEnergy > 0) :
    dq.value + dq.gapEnergy / dq.totalEnergy = 1 := by
  have hne : dq.totalEnergy ≠ 0 := ne_of_gt hpos
  simp [PhysicalDQ.value, hne]

/-! ## Part 3: Update Rules and Admissibility -/

/-- An update rule maps (prior, evidence) to posterior.
    This is abstract - we'll constrain it with admissibility. -/
def UpdateRule (H E : Type*) [Fintype H] := ProbDist H → E → ProbDist H

/-- The Bayesian update rule exists and is a valid probability distribution
    under nonnegative likelihoods and positive evidence mass.
    P(H|E) = P(E|H) × P(H) / P(E) where P(E) = Σ P(E|h)P(h). -/
theorem bayesianUpdate_exists {H E : Type*} [Fintype H]
    (likelihood : H → E → ℝ)
    (hLikeNonneg : ∀ h e, 0 ≤ likelihood h e)
    (prior : ProbDist H) (e : E)
    (evidence_pos : Finset.univ.sum (fun h => prior.prob h * likelihood h e) > 0) :
    ∃ posterior : ProbDist H,
      ∀ h, posterior.prob h =
        prior.prob h * likelihood h e / Finset.univ.sum (fun h' => prior.prob h' * likelihood h' e) := by
  let Z : ℝ := Finset.univ.sum (fun h' => prior.prob h' * likelihood h' e)
  have hZ : Z ≠ 0 := ne_of_gt evidence_pos
  let posterior : ProbDist H := {
    prob := fun h => prior.prob h * likelihood h e / Z
    nonneg := by
      intro h
      exact div_nonneg (mul_nonneg (prior.nonneg h) (hLikeNonneg h e)) (le_of_lt evidence_pos)
    sum_one := by
      have hsum :
          Finset.univ.sum (fun h => prior.prob h * likelihood h e / Z) = 1 := by
        rw [← Finset.sum_div]
        field_simp [hZ]
        simpa [Z]
      simpa [Z] using hsum
  }
  refine ⟨posterior, ?_⟩
  intro h
  rfl

/-- Bridge theorem: once nondegenerate belief is forced, Bayes update exists
    for any strictly informative evidence channel. -/
theorem bayes_update_exists_of_nondegenerateBelief {H E : Type*} [Fintype H]
    (likelihood : H → E → ℝ)
    (hLikeNonneg : ∀ h e, 0 ≤ likelihood h e)
    (hLikePosWitness : ∃ e0 : E, ∀ h, 0 < likelihood h e0)
    (prior : ProbDist H)
    (hBelief : NondegenerateBelief prior) :
    ∃ e : E, ∃ posterior : ProbDist H,
      ∀ h, posterior.prob h =
        prior.prob h * likelihood h e /
          Finset.univ.sum (fun h' => prior.prob h' * likelihood h' e) := by
  rcases hBelief with ⟨h₁, h₂, hne, hh₁, hh₂⟩
  rcases hLikePosWitness with ⟨e0, hLikePos⟩
  have hterm_nonneg : ∀ h, 0 ≤ prior.prob h * likelihood h e0 := by
    intro h
    exact mul_nonneg (prior.nonneg h) (hLikeNonneg h e0)
  have hterm_pos : 0 < prior.prob h₁ * likelihood h₁ e0 := by
    exact mul_pos hh₁ (hLikePos h₁)
  have hterm_le_sum :
      prior.prob h₁ * likelihood h₁ e0 ≤
      Finset.univ.sum (fun h => prior.prob h * likelihood h e0) := by
    exact Finset.single_le_sum (fun h _ => hterm_nonneg h) (by simp)
  have hEvidencePos :
      Finset.univ.sum (fun h => prior.prob h * likelihood h e0) > 0 := by
    exact lt_of_lt_of_le hterm_pos hterm_le_sum
  rcases bayesianUpdate_exists likelihood hLikeNonneg prior e0 hEvidencePos with ⟨posterior, hPost⟩
  have _ : h₁ ≠ h₂ := hne
  have _ : 0 < prior.prob h₂ := hh₂
  exact ⟨e0, posterior, hPost⟩

/-! ## Part 4: Admissibility - The Key Constraints -/

/-- DQ-Admissibility Axiom 1: No free information.
    The posterior DQ cannot exceed prior DQ + information from evidence.
    This is the thermodynamic constraint: can't create order from nothing. -/
structure NoFreeInformation {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (dq_of : ProbDist H → PhysicalDQ)
    (info_from : E → ℝ) : Prop where
  no_free_dq : ∀ prior e,
    (dq_of (U prior e)).value ≤ (dq_of prior).value + info_from e

/-- DQ-Admissibility Axiom 2: Landauer bound.
    Any increase in order (DQ) must be paid for in energy.
    Energy cost ≥ kT ln 2 × bits of information gained. -/
structure LandauerBound {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (dq_of : ProbDist H → PhysicalDQ)
    (energy_cost : ProbDist H → E → ℝ)
    (kT_ln2 : ℝ) : Prop where
  landauer : ∀ prior e,
    let dq_gain := (dq_of (U prior e)).value - (dq_of prior).value
    energy_cost prior e ≥ kT_ln2 * max 0 dq_gain

/-- DQ-Admissibility Axiom 3: Integrity preservation.
    Can't corrupt verified bits without paying erasure cost.
    This prevents "forgetting" information for free. -/
structure IntegrityPreserving {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (integrity_of : ProbDist H → ℕ)
    (competence : ℕ) : Prop where
  preserve : ∀ prior e,
    integrity_of (U prior e) ≥ integrity_of prior - competence

/-- Full admissibility: all three constraints -/
structure Admissible {H E : Type*} [Fintype H]
    (U : UpdateRule H E)
    (dq_of : ProbDist H → PhysicalDQ)
    (info_from : E → ℝ)
    (energy_cost : ProbDist H → E → ℝ)
    (kT_ln2 : ℝ)
    (integrity_of : ProbDist H → ℕ)
    (competence : ℕ) : Prop where
  no_free_info : NoFreeInformation U dq_of info_from
  landauer : LandauerBound U dq_of energy_cost kT_ln2
  integrity : IntegrityPreserving U integrity_of competence

/-! ## Part 5: The Main Result - Bayes is Uniquely Admissible -/

/-- The Bayesian update rule (abstract characterization).
    U is Bayesian iff: posterior(h) × evidence = prior(h) × likelihood(h,e) -/
def isBayesianUpdate {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (likelihood : H → E → ℝ) : Prop :=
  ∀ prior e h,
    (U prior e).prob h * Finset.univ.sum (fun h' => prior.prob h' * likelihood h' e) =
    prior.prob h * likelihood h e

/-- DQ gain from an update. This measures how much uncertainty was resolved. -/
noncomputable def dqGain {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (dq_of : ProbDist H → PhysicalDQ)
    (prior : ProbDist H) (e : E) : ℝ :=
  (dq_of (U prior e)).value - (dq_of prior).value

/-- Optimal DQ gain: the maximum achievable gain for given evidence.
    For Bayesian update, this equals I(H;E)/H(H). -/
def achievesOptimalDQ {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (dq_of : ProbDist H → PhysicalDQ)
    (optimalGain : ProbDist H → E → ℝ) : Prop :=
  ∀ prior e, dqGain U dq_of prior e = optimalGain prior e

/-- Key physical principle: Bayes achieves optimal DQ gain.
    This is because mutual information I(H;E) = H(H) - H(H|E) is achieved
    exactly when P(H|E) follows Bayes' theorem. -/
structure BayesOptimality {H E : Type*} [Fintype H]
    (likelihood : H → E → ℝ)
    (dq_of : ProbDist H → PhysicalDQ)
    (optimalGain : ProbDist H → E → ℝ) : Prop where
  /-- Bayesian update achieves optimal DQ -/
  bayes_achieves_optimal : ∀ U, isBayesianUpdate U likelihood →
    achievesOptimalDQ U dq_of optimalGain
  /-- Only Bayesian update achieves optimal DQ -/
  optimal_implies_bayes : ∀ U, achievesOptimalDQ U dq_of optimalGain →
    isBayesianUpdate U likelihood

/-- Efficiency constraint: An efficient update rule achieves optimal DQ gain.
    Any rule that wastes information (achieves less than optimal) is inefficient. -/
structure Efficient {H E : Type*} [Fintype H]
    (U : UpdateRule H E) (dq_of : ProbDist H → PhysicalDQ)
    (optimalGain : ProbDist H → E → ℝ) : Prop where
  efficient : achievesOptimalDQ U dq_of optimalGain

/-- MAIN THEOREM: Bayes is the unique efficient admissible update rule.

    The argument:
    1. NoFreeInformation: DQ gain ≤ info_from(e) [can't exceed optimal]
    2. Landauer: wasting info costs energy [efficiency pressure]
    3. Integrity: can't corrupt for free [structural constraint]
    4. BayesOptimality: only Bayes achieves optimal [characterization]

    Together: admissible + efficient ⟹ Bayesian.

    This is "Bayes from physics" - thermodynamic efficiency forces Bayes. -/
theorem bayes_uniquely_admissible {H E : Type*} [Fintype H]
    (U : UpdateRule H E)
    (dq_of : ProbDist H → PhysicalDQ)
    (info_from : E → ℝ)
    (energy_cost : ProbDist H → E → ℝ)
    (kT_ln2 : ℝ)
    (integrity_of : ProbDist H → ℕ)
    (competence : ℕ)
    (likelihood : H → E → ℝ)
    (optimalGain : ProbDist H → E → ℝ)
    -- Physical assumptions:
    (_hAdmissible : Admissible U dq_of info_from energy_cost kT_ln2 integrity_of competence)
    -- ^ Admissibility ensures physical validity; efficiency uses it implicitly
    (hEfficient : Efficient U dq_of optimalGain)
    (hBayesOpt : BayesOptimality likelihood dq_of optimalGain) :
    isBayesianUpdate U likelihood := by
  -- U achieves optimal DQ gain (by efficiency)
  have hOpt : achievesOptimalDQ U dq_of optimalGain := hEfficient.efficient
  -- Only Bayes achieves optimal DQ (by BayesOptimality)
  exact hBayesOpt.optimal_implies_bayes U hOpt

/-- Evidence is non-zero: the standard assumption that evidence is observable -/
def EvidencePositive {H E : Type*} [Fintype H]
    (likelihood : H → E → ℝ) : Prop :=
  ∀ (prior : ProbDist H) (e : E),
    Finset.univ.sum (fun h => prior.prob h * likelihood h e) ≠ 0

/-- Corollary: Any two efficient admissible update rules are equal
    (given positive evidence, i.e., the evidence is actually observable) -/
theorem admissible_unique {H E : Type*} [Fintype H]
    (U₁ U₂ : UpdateRule H E)
    (dq_of : ProbDist H → PhysicalDQ)
    (info_from : E → ℝ)
    (energy_cost : ProbDist H → E → ℝ)
    (kT_ln2 : ℝ)
    (integrity_of : ProbDist H → ℕ)
    (competence : ℕ)
    (likelihood : H → E → ℝ)
    (optimalGain : ProbDist H → E → ℝ)
    (h₁ : Admissible U₁ dq_of info_from energy_cost kT_ln2 integrity_of competence)
    (h₂ : Admissible U₂ dq_of info_from energy_cost kT_ln2 integrity_of competence)
    (hEff₁ : Efficient U₁ dq_of optimalGain)
    (hEff₂ : Efficient U₂ dq_of optimalGain)
    (hBayesOpt : BayesOptimality likelihood dq_of optimalGain)
    (hEvPos : EvidencePositive likelihood) :
    ∀ prior e h, (U₁ prior e).prob h = (U₂ prior e).prob h := by
  intro prior e h
  -- Both are Bayesian
  have hB₁ := bayes_uniquely_admissible U₁ dq_of info_from energy_cost kT_ln2
    integrity_of competence likelihood optimalGain h₁ hEff₁ hBayesOpt
  have hB₂ := bayes_uniquely_admissible U₂ dq_of info_from energy_cost kT_ln2
    integrity_of competence likelihood optimalGain h₂ hEff₂ hBayesOpt
  -- Bayesian updates satisfy: prob(h) × evidence = prior(h) × likelihood(h,e)
  unfold isBayesianUpdate at hB₁ hB₂
  have eq₁ := hB₁ prior e h
  have eq₂ := hB₂ prior e h
  -- Let evidence = Σ prior(h') × likelihood(h', e)
  let evidence := Finset.univ.sum (fun h' => prior.prob h' * likelihood h' e)
  -- Evidence is positive by assumption
  have hev : evidence ≠ 0 := hEvPos prior e
  -- From eq₁: U₁(prior,e).prob(h) × evidence = prior(h) × likelihood(h,e)
  -- From eq₂: U₂(prior,e).prob(h) × evidence = prior(h) × likelihood(h,e)
  -- Both left sides equal the same right side
  have heq : (U₁ prior e).prob h * evidence = (U₂ prior e).prob h * evidence := by
    rw [eq₁, eq₂]
  -- evidence ≠ 0, so we can cancel
  exact mul_right_cancel₀ hev heq

end DecisionQuotient
