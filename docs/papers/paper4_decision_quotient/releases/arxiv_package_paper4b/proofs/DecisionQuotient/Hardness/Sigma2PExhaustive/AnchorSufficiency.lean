/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/AnchorSufficiency.lean

  Σ₂ᴾ-hardness via ∃∀-SAT for a fixed-coordinate ("anchor") sufficiency problem:
  Given a decision problem and a fixed coordinate set I, does there exist a state
  s₀ such that Opt is constant over all states agreeing with s₀ on I?
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import DecisionQuotient.Instances
import DecisionQuotient.Hardness.QBF
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

namespace DecisionQuotient

open Classical

set_option linter.unnecessarySimpa false

/-! ## Anchor sufficiency -/

/-- `isSufficientAt` means: fixing coordinates in `I` to those of `s₀`
    makes the optimal set constant. -/
def DecisionProblem.isSufficientAt {A S : Type*} {n : ℕ} [CoordinateSpace S n]
    (dp : DecisionProblem A S) (I : Finset (Fin n)) (s₀ : S) : Prop :=
  ∀ s : S, agreeOn s s₀ I → dp.Opt s = dp.Opt s₀

/-- Anchor sufficiency: there exists a witness state `s₀`. -/
def DecisionProblem.anchorSufficient {A S : Type*} {n : ℕ} [CoordinateSpace S n]
    (dp : DecisionProblem A S) (I : Finset (Fin n)) : Prop :=
  ∃ s₀ : S, dp.isSufficientAt I s₀

/-! ## Reduction from ∃∀-SAT -/

inductive QBFAction where
  | yes : QBFAction
  | no  : QBFAction
  deriving DecidableEq

open QBFAction

lemma two_le_one_false : ¬ ((2 : ℝ) ≤ 1) := by linarith
lemma two_le_zero_false : ¬ ((2 : ℝ) ≤ 0) := by linarith

abbrev QBFState (nx ny : ℕ) := Fin (nx + ny) → Bool

def xPart {nx ny : ℕ} (s : QBFState nx ny) : AssignX nx :=
  fun i => s (Fin.castAdd ny i)

def yPart {nx ny : ℕ} (s : QBFState nx ny) : AssignY ny :=
  fun j => s (Fin.natAdd nx j)

def mkState {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) : QBFState nx ny :=
  fun i => Fin.addCases (motive := fun _ => Bool) x y i

@[simp] lemma mkState_castAdd {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) (i : Fin nx) :
    mkState x y (Fin.castAdd ny i) = x i := by
  simp [mkState]

@[simp] lemma mkState_natAdd {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) (j : Fin ny) :
    mkState x y (Fin.natAdd nx j) = y j := by
  simp [mkState]

@[simp] lemma xPart_mkState {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) :
    xPart (mkState x y) = x := by
  funext i
  simp [xPart]

@[simp] lemma yPart_mkState {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) :
    yPart (mkState x y) = y := by
  funext j
  simp [yPart]

/-- Evaluate the QBF formula under the assignment induced by a state. -/
def qbfEval (φ : ExistsForallFormula) (s : QBFState φ.nx φ.ny) : Bool :=
  φ.formula.eval (ExistsForallFormula.sumAssignment (xPart s) (yPart s))

@[simp] lemma qbfEval_mkState (φ : ExistsForallFormula) (x : AssignX φ.nx) (y : AssignY φ.ny) :
    qbfEval φ (mkState x y) =
      φ.formula.eval (ExistsForallFormula.sumAssignment x y) := by
  simp [qbfEval]

def yAllFalse {nx ny : ℕ} (s : QBFState nx ny) : Prop :=
  ∀ j : Fin ny, yPart s j = false

@[simp] lemma yAllFalse_mkState {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) :
    yAllFalse (mkState x y) ↔ (∀ j : Fin ny, y j = false) := by
  simp [yAllFalse, yPart]

/-- Utility for the reduction. YES gets 2 iff φ holds; NO gets 1 iff y = 0. -/
noncomputable def qbfUtility (φ : ExistsForallFormula) : QBFAction → QBFState φ.nx φ.ny → ℝ
  | yes, s => if qbfEval φ s then 2 else 0
  | no,  s => if yAllFalse s then 1 else 0

noncomputable def qbfProblem (φ : ExistsForallFormula) : DecisionProblem QBFAction (QBFState φ.nx φ.ny) where
  utility := qbfUtility φ

def xCoords (nx ny : ℕ) : Finset (Fin (nx + ny)) :=
  (Finset.univ.image (Fin.castAdd ny))

lemma mem_xCoords {nx ny : ℕ} (i : Fin nx) :
    Fin.castAdd ny i ∈ xCoords nx ny := by
  simp [xCoords]

lemma agreeOn_xCoords_iff {nx ny : ℕ} (s s' : QBFState nx ny) :
    agreeOn s s' (xCoords nx ny) ↔
      ∀ i : Fin nx, s (Fin.castAdd ny i) = s' (Fin.castAdd ny i) := by
  constructor
  · intro h i
    exact h _ (mem_xCoords i)
  · intro h i hi
    rcases Finset.mem_image.mp hi with ⟨i', _, rfl⟩
    exact h i'

open QBFAction

lemma opt_yes_only (φ : ExistsForallFormula) (s : QBFState φ.nx φ.ny)
    (h : qbfEval φ s = true) :
    (qbfProblem φ).Opt s = {yes} := by
  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq,
             Set.mem_singleton_iff]
  constructor
  · intro hopt
    cases a with
    | yes => rfl
    | no =>
      exfalso
      have h1 := hopt yes
      by_cases hy : yAllFalse s
      · have h1' : (2 : ℝ) ≤ 1 := by
          simpa [qbfProblem, qbfUtility, h, hy] using h1
        exact two_le_one_false h1'
      · have h1' : (2 : ℝ) ≤ 0 := by
          simpa [qbfProblem, qbfUtility, h, hy] using h1
        exact two_le_zero_false h1'
  · intro ha
    subst ha
    intro a'
    cases a' with
    | yes => simp [qbfProblem, qbfUtility, h]
    | no =>
      by_cases hy : yAllFalse s
      · simp [qbfProblem, qbfUtility, h, hy]
      · simp [qbfProblem, qbfUtility, h, hy]

lemma opt_no_only (φ : ExistsForallFormula) (s : QBFState φ.nx φ.ny)
    (hφ : qbfEval φ s = false) (hy : yAllFalse s) :
    (qbfProblem φ).Opt s = {no} := by
  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq,
             Set.mem_singleton_iff]
  constructor
  · intro hopt
    cases a with
    | yes =>
      have h1 := hopt no
      simp [qbfProblem, qbfUtility, hφ, hy] at h1
      linarith
    | no => rfl
  · intro ha
    subst ha
    intro a'
    cases a' with
    | yes => simp [qbfProblem, qbfUtility, hφ, hy]
    | no  => simp [qbfProblem, qbfUtility, hφ, hy]

lemma opt_both (φ : ExistsForallFormula) (s : QBFState φ.nx φ.ny)
    (hφ : qbfEval φ s = false) (hy : ¬ yAllFalse s) :
    (qbfProblem φ).Opt s = {yes, no} := by
  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq,
             Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro _; cases a <;> simp
  · intro _
    intro a'
    cases a' <;> cases a <;> simp [qbfProblem, qbfUtility, hφ, hy]

/-! ## Main reduction theorem -/

theorem exists_forall_iff_anchor_sufficient (φ : ExistsForallFormula) (hny : 0 < φ.ny) :
    ExistsForallFormula.satisfiable φ ↔
      (qbfProblem φ).anchorSufficient (xCoords φ.nx φ.ny) := by
  constructor
  · intro hsat
    rcases hsat with ⟨x, hx⟩
    let y0 : AssignY φ.ny := fun _ => false
    let s0 : QBFState φ.nx φ.ny := mkState x y0
    refine ⟨s0, ?_⟩
    intro s hagree
    have hx' : ∀ i : Fin φ.nx, xPart s i = x i := by
      have h' := (agreeOn_xCoords_iff (s := s) (s' := s0)).1 hagree
      intro i
      specialize h' i
      simpa [xPart, s0, y0] using h'
    have hxval : xPart s = x := by
      funext i; exact hx' i
    have hq' : φ.formula.eval (ExistsForallFormula.sumAssignment x (yPart s)) = true := by
      have := hx (yPart s)
      simpa [ExistsForallFormula.satisfiedBy] using this
    have hq : qbfEval φ s = true := by
      simpa [qbfEval, hxval] using hq'
    have hq0' : φ.formula.eval (ExistsForallFormula.sumAssignment x y0) = true := by
      have := hx y0
      simpa [ExistsForallFormula.satisfiedBy] using this
    have hq0 : qbfEval φ s0 = true := by
      simpa [qbfEval, s0, y0] using hq0'
    rw [opt_yes_only φ s hq, opt_yes_only φ s0 hq0]
  · intro hanch
    rcases hanch with ⟨s0, hsuff⟩
    let x : AssignX φ.nx := xPart s0
    refine ⟨x, ?_⟩
    intro y
    let s : QBFState φ.nx φ.ny := mkState x y
    let y0 : AssignY φ.ny := fun _ => false
    let s0' : QBFState φ.nx φ.ny := mkState x y0
    have hagree : agreeOn s s0 (xCoords φ.nx φ.ny) := by
      apply (agreeOn_xCoords_iff (s := s) (s' := s0)).2
      intro i
      simp [s, x, xPart]
    have hagree0 : agreeOn s0' s0 (xCoords φ.nx φ.ny) := by
      apply (agreeOn_xCoords_iff (s := s0') (s' := s0)).2
      intro i
      simp [s0', x, xPart]
    have hOpt : (qbfProblem φ).Opt s = (qbfProblem φ).Opt s0 := hsuff s hagree
    have hOpt0 : (qbfProblem φ).Opt s0' = (qbfProblem φ).Opt s0 := hsuff s0' hagree0
    have hOptConst : (qbfProblem φ).Opt s = (qbfProblem φ).Opt s0' := hOpt.trans hOpt0.symm
    by_cases hq : qbfEval φ s = true
    · have hq' : φ.formula.eval (ExistsForallFormula.sumAssignment x y) = true := by
        simpa [qbfEval, s] using hq
      simpa [ExistsForallFormula.satisfiedBy] using hq'
    · have hq' : qbfEval φ s = false := by simpa using hq
      by_cases hy : yAllFalse s
      · -- y is all false
        have hOptS : (qbfProblem φ).Opt s = {no} := opt_no_only φ s hq' hy
        -- pick y1 not all false
        let y1 : AssignY φ.ny := fun j => j = ⟨0, hny⟩
        let s1 : QBFState φ.nx φ.ny := mkState x y1
        have hy1 : ¬ yAllFalse s1 := by
          intro h
          have := h ⟨0, hny⟩
          simp [s1, y1] at this
        have hagree1 : agreeOn s1 s0 (xCoords φ.nx φ.ny) := by
          apply (agreeOn_xCoords_iff (s := s1) (s' := s0)).2
          intro i
          simp [s1, x, xPart]
        have hOpt1 : (qbfProblem φ).Opt s1 = (qbfProblem φ).Opt s0 := hsuff s1 hagree1
        have hOptConst1 : (qbfProblem φ).Opt s1 = (qbfProblem φ).Opt s0' :=
          hOpt1.trans hOpt0.symm
        by_cases hq1 : qbfEval φ s1 = true
        · have hOptS1 : (qbfProblem φ).Opt s1 = {yes} := opt_yes_only φ s1 hq1
          have hOptS0' : (qbfProblem φ).Opt s0' = {yes} := by
            calc
              (qbfProblem φ).Opt s0' = (qbfProblem φ).Opt s1 := by
                symm; exact hOptConst1
              _ = {yes} := hOptS1
          have hOptS' : (qbfProblem φ).Opt s = {yes} := by
            simpa [hOptConst] using hOptS0'
          have : ({no} : Set QBFAction) ≠ ({yes} : Set QBFAction) := by
            intro hset
            have hmem := congrArg (fun t => yes ∈ t) hset
            simp at hmem
          exact (this (hOptS ▸ hOptS')).elim
        · have hOptS1 : (qbfProblem φ).Opt s1 = {yes, no} :=
            opt_both φ s1 (by simpa using hq1) hy1
          have hOptS0' : (qbfProblem φ).Opt s0' = {yes, no} := by
            calc
              (qbfProblem φ).Opt s0' = (qbfProblem φ).Opt s1 := by
                symm; exact hOptConst1
              _ = {yes, no} := hOptS1
          have hOptS' : (qbfProblem φ).Opt s = {yes, no} := by
            simpa [hOptConst] using hOptS0'
          have : ({no} : Set QBFAction) ≠ ({yes, no} : Set QBFAction) := by
            intro hset
            have hmem := congrArg (fun t => yes ∈ t) hset
            simp at hmem
          exact (this (hOptS ▸ hOptS')).elim
      · -- y is not all false
        have hOptS : (qbfProblem φ).Opt s = {yes, no} := opt_both φ s hq' hy
        have hy0 : yAllFalse s0' := by
          intro j
          simp [yAllFalse, yPart, s0', y0]
        by_cases hq0 : qbfEval φ s0' = true
        · have hOptS0 : (qbfProblem φ).Opt s0' = {yes} := opt_yes_only φ s0' hq0
          have hOptS' : (qbfProblem φ).Opt s = {yes} := by
            simpa [hOptConst] using hOptS0
          have : ({yes, no} : Set QBFAction) ≠ ({yes} : Set QBFAction) := by
            intro hset
            have hmem := congrArg (fun t => no ∈ t) hset
            simp at hmem
          exact (this (hOptS ▸ hOptS')).elim
        · have hOptS0 : (qbfProblem φ).Opt s0' = {no} := opt_no_only φ s0' (by simpa using hq0) hy0
          have hOptS' : (qbfProblem φ).Opt s = {no} := by
            simpa [hOptConst] using hOptS0
          have : ({yes, no} : Set QBFAction) ≠ ({no} : Set QBFAction) := by
            intro hset
            have hmem := congrArg (fun t => yes ∈ t) hset
            simp at hmem
          exact (this (hOptS ▸ hOptS')).elim

theorem exists_forall_iff_anchor_sufficient_padded (φ : ExistsForallFormula) :
    ExistsForallFormula.satisfiable φ ↔
      (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
        (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny) := by
  have hny : 0 < (ExistsForallFormula.padUniversal φ).ny := by
    simp [ExistsForallFormula.padUniversal]
  have hpad := exists_forall_iff_anchor_sufficient (φ := ExistsForallFormula.padUniversal φ) hny
  constructor
  · intro hsat
    have hsat' : ExistsForallFormula.satisfiable (ExistsForallFormula.padUniversal φ) :=
      (ExistsForallFormula.satisfiable_iff_padUniversal φ).1 hsat
    exact hpad.mp hsat'
  · intro hanch
    have hsat' : ExistsForallFormula.satisfiable (ExistsForallFormula.padUniversal φ) :=
      hpad.mpr hanch
    exact (ExistsForallFormula.satisfiable_iff_padUniversal φ).2 hsat'

end DecisionQuotient
