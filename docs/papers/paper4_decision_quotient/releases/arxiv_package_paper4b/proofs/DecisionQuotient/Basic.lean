/-
  Paper 4: Decision-Relevant Uncertainty

  Basic.lean - Core definitions for decision problems under uncertainty

  Key structures:
  - DecisionProblem: (A, S, U) where A is alternatives, S is states, U is utility
  - Opt: S → Set A (the optimizer map)
  - DecisionEquiv: s ∼ s' ⟺ Opt(s) = Opt(s')
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

namespace DecisionQuotient

/-! ## Decision Problem Structure -/

/-- A decision problem consists of:
  - A: Type of alternatives (decisions/actions)
  - S: Type of states (world configurations under uncertainty)
  - U: Utility function mapping (alternative, state) to real value -/
structure DecisionProblem (A S : Type*) where
  utility : A → S → ℝ

variable {A S : Type*}

/-- An alternative a is optimal at state s if it maximizes utility -/
def DecisionProblem.isOptimal (dp : DecisionProblem A S) (a : A) (s : S) : Prop :=
  ∀ a' : A, dp.utility a' s ≤ dp.utility a s

/-- The optimizer map: returns the set of optimal alternatives at state s -/
def DecisionProblem.Opt (dp : DecisionProblem A S) (s : S) : Set A :=
  { a : A | dp.isOptimal a s }

/-- Two states are decision-equivalent if they have the same optimal set -/
def DecisionProblem.DecisionEquiv (dp : DecisionProblem A S) (s s' : S) : Prop :=
  dp.Opt s = dp.Opt s'

-- DecisionEquiv is an equivalence relation
theorem DecisionProblem.decisionEquiv_refl (dp : DecisionProblem A S) (s : S) :
    dp.DecisionEquiv s s := rfl

theorem DecisionProblem.decisionEquiv_symm (dp : DecisionProblem A S) {s s' : S}
    (h : dp.DecisionEquiv s s') : dp.DecisionEquiv s' s := h.symm

theorem DecisionProblem.decisionEquiv_trans (dp : DecisionProblem A S) {s₁ s₂ s₃ : S}
    (h₁ : dp.DecisionEquiv s₁ s₂) (h₂ : dp.DecisionEquiv s₂ s₃) :
    dp.DecisionEquiv s₁ s₃ := h₁.trans h₂

/-- DecisionEquiv as a Setoid -/
def DecisionProblem.decisionSetoid (dp : DecisionProblem A S) : Setoid S where
  r := dp.DecisionEquiv
  iseqv := {
    refl := dp.decisionEquiv_refl
    symm := fun h => dp.decisionEquiv_symm h
    trans := fun h₁ h₂ => dp.decisionEquiv_trans h₁ h₂
  }

/-! ## The Decision Quotient -/

/-- The Decision Quotient Q = S/∼ where s ∼ s' ⟺ Opt(s) = Opt(s')
    This is the minimal state abstraction preserving the optimal decision -/
def DecisionProblem.DecisionQuotientType (dp : DecisionProblem A S) : Type _ :=
  @Quotient S dp.decisionSetoid

/-- The quotient map π: S → Q -/
def DecisionProblem.quotientMap (dp : DecisionProblem A S) : S → dp.DecisionQuotientType :=
  @Quotient.mk S dp.decisionSetoid

/-! ## Key Properties -/

/-- Opt factors through the quotient: there exists F such that Opt = F ∘ π -/
theorem DecisionProblem.opt_factors_through_quotient (dp : DecisionProblem A S) :
    ∃ F : dp.DecisionQuotientType → Set A,
      ∀ s : S, dp.Opt s = F (dp.quotientMap s) := by
  use fun q => @Quotient.lift S (Set A) dp.decisionSetoid dp.Opt (fun _ _ h => h) q
  intro s
  rfl

/-- The lifted optimizer on the quotient -/
def DecisionProblem.OptQuotient (dp : DecisionProblem A S) : dp.DecisionQuotientType → Set A :=
  @Quotient.lift S (Set A) dp.decisionSetoid dp.Opt (fun _ _ h => h)

/-- Opt = OptQuotient ∘ quotientMap -/
theorem DecisionProblem.opt_eq_optQuotient_comp (dp : DecisionProblem A S) (s : S) :
    dp.Opt s = dp.OptQuotient (dp.quotientMap s) := rfl

end DecisionQuotient

