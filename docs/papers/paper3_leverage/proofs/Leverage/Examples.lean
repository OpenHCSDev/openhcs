/-
# Leverage Framework - Concrete Examples

This module provides concrete calculations of leverage for various
architectural decisions.

Examples:
- Microservices vs Monolith
- REST API design
- Configuration systems
- Database normalization

All examples use definitional proofs - no sorry placeholders.

Author: Examples for Paper 3
Date: 2025-12-30
-/

import Leverage.Foundations
import Leverage.Theorems
import Leverage.Probability

namespace Leverage.Examples

/-!
## Example 1: Microservices vs Monolith
-/

/-- Monolithic architecture: DOF = 1, limited caps -/
def monolith (base_caps : Nat) : Architecture where
  dof := 1
  capabilities := base_caps
  dof_pos := by decide

/-- Microservices architecture: DOF = n, more caps -/
def microservices (n : Nat) (h : n > 0) (extra_caps : Nat) : Architecture where
  dof := n
  capabilities := 1 + extra_caps  -- base + microservice-specific
  dof_pos := h

/-- Microservices gain 5 additional capabilities -/
def microservice_extra_caps : Nat := 5
-- independent_scaling, independent_deployment, fault_isolation, team_autonomy, polyglot_persistence

/-- Example: 5 microservices -/
example : let mono := monolith 1
          let micro := microservices 5 (by decide) microservice_extra_caps
          micro.capabilities > mono.capabilities := by
  simp [monolith, microservices, microservice_extra_caps]

/-- Example: Monolith has higher leverage when caps are equal -/
example : let mono := monolith 6
          let micro := microservices 5 (by decide) 5
          mono.higher_leverage micro := by
  simp only [monolith, microservices, Architecture.higher_leverage]
  native_decide

/-!
## Example 2: REST API Design
-/

/-- Specific endpoints: one per use case, DOF = n -/
def specific_api (n : Nat) (h : n > 0) : Architecture where
  dof := n
  capabilities := n  -- Each endpoint handles one use case
  dof_pos := h

/-- Generic endpoint: single endpoint handles all, DOF = 1 -/
def generic_api (n : Nat) : Architecture where
  dof := 1
  capabilities := n  -- Handles n use cases
  dof_pos := by decide

/-- Example: 10 use cases - generic has higher leverage -/
example : let spec := specific_api 10 (by decide)
          let gen := generic_api 10
          gen.higher_leverage spec := by
  simp only [specific_api, generic_api, Architecture.higher_leverage]
  native_decide

/-- Leverage ratio for generic vs specific -/
theorem generic_api_leverage_ratio (n : Nat) (h : n > 1) :
    let spec := specific_api n (by omega)
    let gen := generic_api n
    gen.capabilities * spec.dof = n * n ∧
    spec.capabilities * gen.dof = n * 1 := by
  simp [specific_api, generic_api]

/-!
## Example 3: Configuration Systems
-/

/-- Explicit configuration: DOF = n (must set all) -/
def explicit_config (n : Nat) (h : n > 0) : Architecture where
  dof := n
  capabilities := n
  dof_pos := h

/-- Convention over configuration: DOF = overrides only -/
def convention_config (total_params overrides : Nat) (h : overrides > 0) : Architecture where
  dof := overrides
  capabilities := total_params  -- Can configure all, only set overrides
  dof_pos := h

/-- Example: 100 parameters, 5 overrides - convention wins -/
example : let explicit := explicit_config 100 (by decide)
          let convention := convention_config 100 5 (by decide)
          convention.higher_leverage explicit := by
  simp only [explicit_config, convention_config, Architecture.higher_leverage]
  native_decide

/-- Leverage improvement factor -/
theorem convention_leverage_improvement (total overrides : Nat)
    (h1 : total > 0) (h2 : overrides > 0) (h3 : overrides < total) :
    let explicit := explicit_config total h1
    let convention := convention_config total overrides h2
    convention.capabilities * explicit.dof > explicit.capabilities * convention.dof := by
  simp [explicit_config, convention_config]
  -- total * total > total * overrides when overrides < total
  have : total * total > total * overrides := Nat.mul_lt_mul_of_pos_left h3 h1
  omega

/-!
## Example 4: Database Schema Design
-/

/-- Denormalized schema: n redundant copies, DOF = n -/
def denormalized (n : Nat) (h : n > 0) (caps : Nat) : Architecture where
  dof := n
  capabilities := caps
  dof_pos := h

/-- Normalized schema: single source, DOF = 1 -/
def normalized (caps : Nat) : Architecture where
  dof := 1
  capabilities := caps
  dof_pos := by decide

/-- Example: 3 redundant tables vs 1 normalized - same caps -/
example : let denorm := denormalized 3 (by decide) 10
          let norm := normalized 10
          norm.higher_leverage denorm := by
  simp only [denormalized, normalized, Architecture.higher_leverage]
  native_decide

/-- Normalized always wins for same capabilities -/
theorem normalized_wins (n caps : Nat) (h : n > 1) :
    let denorm := denormalized n (by omega) caps
    let norm := normalized caps
    norm.dof < denorm.dof := by
  simp only [denormalized, normalized]
  exact h

/-!
## Example 5: Error Probability Calculations
-/

/-- Standard error rate: 1% = 1/100 -/
def p_one_percent : ErrorRate where
  numerator := 1
  denominator := 100
  rate_valid := by decide

/-- DOF = 1: Expected errors = 1/100 -/
example : expected_errors (Architecture.mk 1 10 (by decide)) p_one_percent = (1, 100) := rfl

/-- DOF = 10: Expected errors = 10/100 = 0.1 -/
example : expected_errors (Architecture.mk 10 10 (by decide)) p_one_percent = (10, 100) := rfl

/-- DOF = 100: Expected errors = 100/100 = 1.0 -/
example : expected_errors (Architecture.mk 100 10 (by decide)) p_one_percent = (100, 100) := rfl

/-- Error scales linearly with DOF -/
theorem error_linear_scaling (d₁ d₂ : Nat) (h₁ : d₁ > 0) (h₂ : d₂ > 0) :
    let a₁ := Architecture.mk d₁ 1 h₁
    let a₂ := Architecture.mk d₂ 1 h₂
    (expected_errors a₁ p_one_percent).1 * d₂ =
    (expected_errors a₂ p_one_percent).1 * d₁ := by
  simp only [expected_errors, p_one_percent]
  -- d₁ * 1 * d₂ = d₂ * 1 * d₁
  simp only [Nat.mul_one]
  exact Nat.mul_comm d₁ d₂

end Leverage.Examples
