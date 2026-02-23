/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/QBF.lean - Minimal QBF (∃∀-SAT) encoding

  This module provides a lightweight quantified Boolean formula framework
  for Σ₂ᴾ reductions. It is intentionally minimal: CNF over a sum of
  variables (existential X and universal Y), evaluation, and the
  ∃x ∀y satisfiability predicate.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

namespace DecisionQuotient

open Classical

/-! ## Generic Boolean Formula over an arbitrary variable type -/

/-- A Boolean formula over an arbitrary variable type. -/
inductive QFormula (Var : Type*) where
  | var : Var → QFormula Var
  | not : QFormula Var → QFormula Var
  | and : QFormula Var → QFormula Var → QFormula Var
  | or : QFormula Var → QFormula Var → QFormula Var
  deriving DecidableEq, Repr

/-- Map a formula by mapping its variables. -/
def QFormula.map {Var W : Type*} (f : Var → W) : QFormula Var → QFormula W
  | var v => var (f v)
  | not φ => not (map f φ)
  | and φ1 φ2 => and (map f φ1) (map f φ2)
  | or φ1 φ2 => or (map f φ1) (map f φ2)

/-- Evaluate a formula under an assignment. -/
def QFormula.eval {Var : Type*} (assignment : Var → Bool) : QFormula Var → Bool
  | var v => assignment v
  | not φ => !(eval assignment φ)
  | and φ1 φ2 => (eval assignment φ1) && (eval assignment φ2)
  | or φ1 φ2 => (eval assignment φ1) || (eval assignment φ2)

lemma QFormula.eval_map {Var W : Type*} (f : Var → W) (φ : QFormula Var) (a : W → Bool) :
    (φ.map f).eval a = φ.eval (fun v => a (f v)) := by
  induction φ with
  | var v => simp [map, eval]
  | not φ ih => simp [map, eval, ih]
  | and φ1 φ2 ih1 ih2 => simp [map, eval, ih1, ih2]
  | or φ1 φ2 ih1 ih2 => simp [map, eval, ih1, ih2]

/-! ## ∃∀-SAT (Σ₂ᴾ) Instances -/

abbrev AssignX (nx : ℕ) := Fin nx → Bool
abbrev AssignY (ny : ℕ) := Fin ny → Bool

/-- An ∃∀-SAT instance: a Boolean formula over variables X ⊕ Y. -/
structure ExistsForallFormula where
  nx : ℕ
  ny : ℕ
  formula : QFormula (Sum (Fin nx) (Fin ny))

namespace ExistsForallFormula

/-- Combine X and Y assignments into a single assignment over `Sum`. -/
def sumAssignment {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) : Sum (Fin nx) (Fin ny) → Bool
  | Sum.inl i => x i
  | Sum.inr j => y j

/-- Satisfied by a pair of assignments. -/
def satisfiedBy (φ : ExistsForallFormula) (x : AssignX φ.nx) (y : AssignY φ.ny) : Prop :=
  φ.formula.eval (sumAssignment x y) = true

/-- ∃x ∀y satisfiability predicate. -/
def satisfiable (φ : ExistsForallFormula) : Prop :=
  ∃ x : AssignX φ.nx, ∀ y : AssignY φ.ny, φ.satisfiedBy x y

/-! ## Padding a universal variable (for ny = 0) -/

def embedVar {nx ny : ℕ} : Sum (Fin nx) (Fin ny) → Sum (Fin nx) (Fin (ny + 1))
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr (Fin.castLT j (Nat.lt_succ_of_lt j.isLt))

def padUniversal (φ : ExistsForallFormula) : ExistsForallFormula where
  nx := φ.nx
  ny := φ.ny + 1
  formula := φ.formula.map (embedVar)

def restrictY {ny : ℕ} (y : AssignY (ny + 1)) : AssignY ny :=
  fun j => y (Fin.castLT j (Nat.lt_succ_of_lt j.isLt))

lemma sumAssignment_embed {nx ny : ℕ} (x : AssignX nx) (y : AssignY (ny + 1)) :
    (fun v => sumAssignment x y (embedVar v)) = sumAssignment x (restrictY y) := by
  funext v
  cases v <;> simp [sumAssignment, restrictY, embedVar]

lemma eval_padUniversal (φ : ExistsForallFormula) (x : AssignX φ.nx) (y : AssignY (φ.ny + 1)) :
    (padUniversal φ).formula.eval (sumAssignment x y) =
      φ.formula.eval (sumAssignment x (restrictY y)) := by
  have hmap := QFormula.eval_map embedVar φ.formula (sumAssignment x y)
  simpa [padUniversal, sumAssignment_embed] using hmap

theorem satisfiable_iff_padUniversal (φ : ExistsForallFormula) :
    satisfiable φ ↔ satisfiable (padUniversal φ) := by
  constructor
  · intro hsat
    rcases hsat with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro y
    have hy := hx (restrictY y)
    have hmap := eval_padUniversal φ x y
    simpa [ExistsForallFormula.satisfiedBy] using hmap.trans hy
  · intro hsat
    rcases hsat with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro y
    -- extend y by ignoring the extra coordinate (set it to false)
    let y' : AssignY (φ.ny + 1) :=
      fun j =>
        if h : (j : Nat) < φ.ny then y ⟨j, h⟩ else false
    have := hx y'
    -- reduce to the original formula
    have hrest : restrictY y' = y := by
      funext j
      simp [restrictY, y', Fin.castLT, Fin.ext_iff]
    have hmap := eval_padUniversal φ x y'
    have h := hmap.symm.trans this
    simpa [ExistsForallFormula.satisfiedBy, hrest] using h

end ExistsForallFormula

end DecisionQuotient
