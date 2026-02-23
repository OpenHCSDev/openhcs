/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/SAT.lean - 3-SAT Instances for Reductions

  This module provides a minimal 3-SAT encoding that can be used as a
  source problem for hardness reductions (see Part 3 of
  `IMPLEMENTATION_PLAN.md`). The focus here is on clear, computable
  semantics: literals, 3-clauses, evaluation under assignments, and the
  satisfiability predicate.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

namespace DecisionQuotient

open Classical

/-- A Boolean literal over `n` variables: variable index plus polarity. -/
structure Literal (n : ℕ) where
  /-- Zero-based variable index (as `Fin n`). -/
  var : Fin n
  /-- `true` for positive, `false` for negated. -/
  polarity : Bool
  deriving DecidableEq, Repr

/-- Evaluate a literal under an assignment. -/
def Literal.eval (l : Literal n) (assignment : Fin n → Bool) : Bool :=
  if l.polarity then assignment l.var else !assignment l.var

/-- A 3-CNF clause with exactly three literals. -/
structure Clause3 (n : ℕ) where
  l1 : Literal n
  l2 : Literal n
  l3 : Literal n
  deriving DecidableEq, Repr

/-- Evaluate a 3-literal clause under an assignment. -/
def Clause3.eval (c : Clause3 n) (assignment : Fin n → Bool) : Bool :=
  c.l1.eval assignment || c.l2.eval assignment || c.l3.eval assignment

/-- A Boolean assignment over `n` variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A 3-SAT instance: number of variables and a list of 3-clauses. -/
structure SAT3Instance where
  numVars : ℕ
  clauses : List (Clause3 numVars)
  deriving Repr

namespace SAT3Instance

/-- Evaluate the whole formula under an assignment. -/
def eval (φ : SAT3Instance) (a : Assignment φ.numVars) : Bool :=
  φ.clauses.all (fun c => Clause3.eval c a)

/-- A 3-SAT instance is satisfied by `a` if all clauses evaluate to true. -/
def satisfiedBy (φ : SAT3Instance) (a : Assignment φ.numVars) : Prop :=
  ∀ c ∈ φ.clauses, Clause3.eval c a = true

/-- Satisfiability predicate. -/
def satisfiable (φ : SAT3Instance) : Prop :=
  ∃ a : Assignment φ.numVars, φ.satisfiedBy a

/-- Boolean evaluation agrees with the propositional predicate. -/
theorem eval_eq_true_iff (φ : SAT3Instance) (a : Assignment φ.numVars) :
    φ.eval a = true ↔ φ.satisfiedBy a := by
  unfold eval satisfiedBy
  induction φ.clauses with
  | nil =>
      simp
  | cons c cs ih =>
      simp [List.all_cons, ih]

end SAT3Instance

end DecisionQuotient

