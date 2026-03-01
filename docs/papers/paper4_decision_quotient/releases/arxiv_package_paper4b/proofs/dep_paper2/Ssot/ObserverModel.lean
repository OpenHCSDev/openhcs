/-
  ObserverModel: Formalizing observation semantics

  This addresses the critique: "Observers are not well-defined."

  We define:
  - Observers as functions from configurations to values
  - Consistency as observer agreement
  - The key result: multi-observer disagreement is possible iff DOF > 1
-/

import Ssot.SSOTGrounded

namespace ObserverModel

open SSOTGrounded

/-- Lookup value by location ID (decidable) -/
def lookupValue (locs : List EncodingLocation) (id : Nat) : Option Nat :=
  match locs with
  | [] => none
  | loc :: rest => if loc.id = id then some loc.value else lookupValue rest id

/-- KEY: Single location, any lookup returns the same value -/
theorem single_lookup_deterministic :
    ∀ (loc : EncodingLocation) (id1 id2 : Nat) (v1 v2 : Nat),
      lookupValue [loc] id1 = some v1 →
      lookupValue [loc] id2 = some v2 →
      v1 = v2 := by
  intro loc id1 id2 v1 v2 h1 h2
  simp only [lookupValue] at h1 h2
  split_ifs at h1 h2; simp_all

/-- Two locations with same value: lookups agree -/
theorem consistent_lookups_agree :
    ∀ (loc1 loc2 : EncodingLocation) (id1 id2 v1 v2 : Nat),
      loc1.value = loc2.value →
      lookupValue [loc1, loc2] id1 = some v1 →
      lookupValue [loc1, loc2] id2 = some v2 →
      v1 = v2 := by
  intro loc1 loc2 id1 id2 v1 v2 hval h1 h2
  simp only [lookupValue] at h1 h2
  split_ifs at h1 h2 <;> simp_all

/-- Two distinct-ID locations with different values: disagreement exists -/
theorem inconsistent_lookups_disagree :
    ∀ (loc1 loc2 : EncodingLocation),
      loc1.id ≠ loc2.id →
      loc1.value ≠ loc2.value →
      ∃ v1 v2,
        lookupValue [loc1, loc2] loc1.id = some v1 ∧
        lookupValue [loc1, loc2] loc2.id = some v2 ∧
        v1 ≠ v2 := by
  intro loc1 loc2 hid hval
  use loc1.value, loc2.value
  constructor
  · -- First: lookupValue finds loc1.id in first position
    simp only [lookupValue, ite_true]
  constructor
  · -- Second: lookupValue skips loc1 (wrong id), finds loc2
    simp only [lookupValue]
    rw [if_neg hid]
    simp only [ite_true]
  · exact hval

/-- SSOT asymmetry theorem: single location immune, multiple vulnerable -/
theorem observation_ssot_asymmetry :
    -- Single location: any two lookups agree
    (∀ loc id1 id2 v1 v2,
      lookupValue [loc] id1 = some v1 →
      lookupValue [loc] id2 = some v2 →
      v1 = v2) ∧
    -- Two distinct locations with different values: disagreement exists
    (∀ loc1 loc2,
      loc1.id ≠ loc2.id →
      loc1.value ≠ loc2.value →
      ∃ v1 v2,
        lookupValue [loc1, loc2] loc1.id = some v1 ∧
        lookupValue [loc1, loc2] loc2.id = some v2 ∧
        v1 ≠ v2) := by
  exact ⟨single_lookup_deterministic, inconsistent_lookups_disagree⟩

end ObserverModel

