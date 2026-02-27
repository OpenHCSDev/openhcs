/- 
# Leverage Framework - Physical Edit-Energy Grounding

This module adds a minimal physical grounding layer:

- One physical parameter: positive energy per independent edit (`joulesPerEdit > 0`)
- No additional architectural assumptions beyond `Architecture` and
  `modification_complexity = DOF` from Foundations

Key results:
- Energy lower bound is exactly proportional to DOF in this model
- Lower DOF implies strictly lower physical edit-energy floor
- In a fixed capability class, higher leverage implies lower energy floor
-/

import Leverage.Foundations

namespace Leverage.Physical

/-- Minimal physical calibration: positive energy per independent edit. -/
structure PhysicalEditModel where
  joulesPerEdit : Nat
  joulesPerEdit_pos : joulesPerEdit > 0

/-- Physical lower bound on edit energy for an architecture. -/
def energyLowerBound (M : PhysicalEditModel) (a : Architecture) : Nat :=
  M.joulesPerEdit * a.modification_complexity

/-- Energy lower bound equals joules-per-edit times DOF. -/
theorem energyLowerBound_eq_joules_times_dof (M : PhysicalEditModel) (a : Architecture) :
    energyLowerBound M a = M.joulesPerEdit * a.dof := by
  simp [energyLowerBound, Architecture.modification_complexity]

/-- Any well-formed architecture has strictly positive physical edit-energy floor. -/
theorem positive_energy_of_wellformed_arch (M : PhysicalEditModel) (a : Architecture) :
    energyLowerBound M a > 0 := by
  simpa [energyLowerBound, Architecture.modification_complexity] using
    (Nat.mul_pos M.joulesPerEdit_pos a.dof_pos)

/-- Lower DOF implies strictly lower physical edit-energy floor. -/
theorem lower_dof_lower_energy (M : PhysicalEditModel) (a₁ a₂ : Architecture)
    (h_dof : a₁.dof < a₂.dof) :
    energyLowerBound M a₁ < energyLowerBound M a₂ := by
  simp [energyLowerBound, Architecture.modification_complexity]
  exact Nat.mul_lt_mul_of_pos_left h_dof M.joulesPerEdit_pos

/-- In a fixed capability class, higher leverage implies lower energy floor. -/
theorem higher_leverage_same_caps_implies_lower_energy
    (M : PhysicalEditModel) (a₁ a₂ : Architecture)
    (h_caps : a₁.capabilities = a₂.capabilities)
    (h_lev : a₁.higher_leverage a₂) :
    energyLowerBound M a₁ < energyLowerBound M a₂ := by
  unfold Architecture.higher_leverage at h_lev
  rw [h_caps] at h_lev
  have h_dof : a₁.dof < a₂.dof := Nat.lt_of_mul_lt_mul_left h_lev
  exact lower_dof_lower_energy M a₁ a₂ h_dof

/-- The energy gap induced by higher leverage is strictly positive. -/
theorem positive_energy_gap_of_higher_leverage
    (M : PhysicalEditModel) (a₁ a₂ : Architecture)
    (h_caps : a₁.capabilities = a₂.capabilities)
    (h_lev : a₁.higher_leverage a₂) :
    0 < energyLowerBound M a₂ - energyLowerBound M a₁ := by
  exact Nat.sub_pos_of_lt
    (higher_leverage_same_caps_implies_lower_energy M a₁ a₂ h_caps h_lev)

/-- SSOT minimizes the physical edit-energy floor. -/
theorem ssot_minimal_energy (M : PhysicalEditModel) (a_ssot a_other : Architecture)
    (h_ssot : a_ssot.is_ssot) :
    energyLowerBound M a_ssot ≤ energyLowerBound M a_other := by
  unfold energyLowerBound
  exact Nat.mul_le_mul_left _ (Leverage.ssot_minimal_modification a_ssot a_other h_ssot)

/-- Feasibility predicate under an explicit energy budget. -/
def feasibleUnderBudget (M : PhysicalEditModel) (budget : Nat) (a : Architecture) : Prop :=
  energyLowerBound M a ≤ budget

/-- Feasibility is equivalent to clearing the energy floor. -/
theorem feasible_iff_floor_le_budget (M : PhysicalEditModel) (budget : Nat) (a : Architecture) :
    feasibleUnderBudget M budget a ↔ energyLowerBound M a ≤ budget := by
  rfl

/-- If budget is below floor, implementation is impossible in this model. -/
theorem infeasible_of_budget_lt_floor (M : PhysicalEditModel) (budget : Nat) (a : Architecture)
    (h_lt : budget < energyLowerBound M a) :
    ¬ feasibleUnderBudget M budget a := by
  intro h_feas
  exact Nat.not_lt_of_ge h_feas h_lt

/-- The energy floor itself is always a feasible budget witness. -/
theorem feasible_at_floor (M : PhysicalEditModel) (a : Architecture) :
    feasibleUnderBudget M (energyLowerBound M a) a := by
  unfold feasibleUnderBudget
  exact Nat.le_refl _

/-- Without an externally imposed upper budget, feasibility is always witnessable. -/
theorem feasible_budget_exists (M : PhysicalEditModel) (a : Architecture) :
    ∃ budget : Nat, feasibleUnderBudget M budget a := by
  exact ⟨energyLowerBound M a, feasible_at_floor M a⟩

/-- Same budget: if lower-leverage architecture is feasible, higher-leverage one is feasible. -/
theorem higher_leverage_same_caps_preserves_feasibility_under_same_budget
    (M : PhysicalEditModel) (a₁ a₂ : Architecture) (budget : Nat)
    (h_caps : a₁.capabilities = a₂.capabilities)
    (h_lev : a₁.higher_leverage a₂)
    (h_feas₂ : feasibleUnderBudget M budget a₂) :
    feasibleUnderBudget M budget a₁ := by
  unfold feasibleUnderBudget at *
  have h_floor_lt : energyLowerBound M a₁ < energyLowerBound M a₂ :=
    higher_leverage_same_caps_implies_lower_energy M a₁ a₂ h_caps h_lev
  exact Nat.le_trans (Nat.le_of_lt h_floor_lt) h_feas₂

/-- Relaxed physical model without positivity requirement (for necessity witnesses). -/
structure PhysicalEditModelRelaxed where
  joulesPerEdit : Nat

/-- Relaxed energy lower bound. -/
def energyLowerBoundRelaxed (M : PhysicalEditModelRelaxed) (a : Architecture) : Nat :=
  M.joulesPerEdit * a.modification_complexity

/-- Zero-conversion relaxed model. -/
def zeroJoulesModel : PhysicalEditModelRelaxed where
  joulesPerEdit := 0

/-- Dropping positivity admits a zero-floor countermodel. -/
theorem zero_model_energy_is_zero (a : Architecture) :
    energyLowerBoundRelaxed zeroJoulesModel a = 0 := by
  simp [energyLowerBoundRelaxed, zeroJoulesModel, Architecture.modification_complexity]

/-- Positivity of the conversion constant is necessary for strict positive floor claims. -/
theorem positive_floor_requires_positive_joules_assumption (a : Architecture) :
    ¬ (0 < energyLowerBoundRelaxed zeroJoulesModel a) := by
  simp [zero_model_energy_is_zero]

/-- Assumption-necessity witnesses for this physical layer. -/
theorem physical_assumption_necessity_witnesses (a : Architecture) :
    (energyLowerBoundRelaxed zeroJoulesModel a = 0) ∧
    (∀ M : PhysicalEditModel, ∃ budget : Nat, feasibleUnderBudget M budget a) := by
  constructor
  · exact zero_model_energy_is_zero a
  · intro M
    exact feasible_budget_exists M a

end Leverage.Physical
