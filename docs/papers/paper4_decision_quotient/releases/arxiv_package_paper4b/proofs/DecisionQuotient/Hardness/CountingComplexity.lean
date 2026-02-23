/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/CountingComplexity.lean

  Reduction from #SAT to decision-quotient computation.
-/

import DecisionQuotient.Finite
import DecisionQuotient.Hardness.SAT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

namespace DecisionQuotient

open Classical

/-- A #SAT instance wraps a 3-SAT formula. -/
structure SharpSATInstance where
  formula : SAT3Instance
  deriving Repr

/-- Actions: all assignments plus a special junk action. -/
abbrev DQAction (n : ℕ) := Option (Assignment n)

private def someEmbedding (n : ℕ) : Assignment n ↪ DQAction n :=
  ⟨Option.some, fun _ _ h => Option.some.inj h⟩

/-- Explicit finiteness/decidability instances for assignments and actions. -/
noncomputable instance assignmentFintype (n : ℕ) : Fintype (Assignment n) := by
  classical
  infer_instance

local instance (priority := 1000) assignmentDecEq (n : ℕ) : DecidableEq (Assignment n) := by
  classical
  infer_instance


noncomputable instance dqActionFintype (n : ℕ) : Fintype (DQAction n) := by
  classical
  infer_instance

local instance (priority := 1000) dqActionDecEq (n : ℕ) : DecidableEq (DQAction n) := by
  classical
  infer_instance


/-- All satisfying assignments for φ. -/
noncomputable def satSet (φ : SAT3Instance) : Finset (Assignment φ.numVars) :=
  (Finset.univ.filter fun a => φ.satisfiedBy a)

/-- Count satisfying assignments. -/
noncomputable def countSatisfyingAssignments (φ : SAT3Instance) : ℕ := (satSet φ).card

/-- Decision problem for the reduction. -/
noncomputable def buildDQProblem (φ : SAT3Instance) : FiniteDecisionProblem
    (A := DQAction φ.numVars) (S := Unit) :=
  { actions := Finset.univ
    states := {()}
    utility := fun a _ =>
      match a with
      | none => (1 : ℤ)
      | some asg => if φ.satisfiedBy asg then 1 else 0 }

/-! ## Helper lemmas -/

lemma satSet_empty_of_count_zero (φ : SAT3Instance) (hzero : countSatisfyingAssignments φ = 0) :
    satSet φ = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa [countSatisfyingAssignments] using hzero

lemma no_satisfying_of_count_zero (φ : SAT3Instance) (hzero : countSatisfyingAssignments φ = 0) :
    ∀ a, ¬ φ.satisfiedBy a := by
  intro a hsat
  have : a ∈ satSet φ := by
    simp [satSet, hsat]
  have hEmpty : satSet φ = ∅ := satSet_empty_of_count_zero φ hzero
  simp [hEmpty] at this

/-! ## Action count -/

/-- Cardinality of the action set: 1 + 2^n. -/
lemma actions_card (φ : SAT3Instance) :
    (buildDQProblem φ).actions.card = 1 + 2 ^ φ.numVars := by
  classical
  -- actions = Finset.univ on DQAction
  simp [buildDQProblem, DQAction, Assignment, Fintype.card_option, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-! ## Optimal actions -/

lemma optimalActions_unsat (φ : SAT3Instance) (hzero : countSatisfyingAssignments φ = 0) :
    (buildDQProblem φ).optimalActions () = {none} := by
  classical
  ext a; constructor
  · intro ha
    have hmem := (buildDQProblem φ).mem_optimalActions_iff (s := ()) (a := a) |>.1 ha
    rcases hmem with ⟨_, hmax⟩
    cases a with
    | none => simp
    | some asg =>
        have hnsat : ¬ φ.satisfiedBy asg := no_satisfying_of_count_zero φ hzero asg
        have hcmp := hmax none (by simp [buildDQProblem])
        have hcontra : False := by
          have hcmp' := hcmp
          simp [buildDQProblem, hnsat] at hcmp'
        exact hcontra.elim
  · intro ha
    have ha' : a = none := by simpa using ha
    subst ha'
    refine (buildDQProblem φ).mem_optimalActions_iff (s := ()) (a := none) |>.2 ?_
    refine ⟨by simp [buildDQProblem], ?_⟩
    intro a' ha'
    cases a' with
    | none => simp [buildDQProblem]
    | some asg =>
        have hnsat : ¬ φ.satisfiedBy asg := no_satisfying_of_count_zero φ hzero asg
        simp [buildDQProblem, hnsat]

lemma optimalActions_sat (φ : SAT3Instance) (hpos : countSatisfyingAssignments φ > 0) :
    (buildDQProblem φ).optimalActions () =
      insert none
        ((satSet φ).map (someEmbedding φ.numVars)) := by
  classical
  have hnonempty : (satSet φ).Nonempty := Finset.card_pos.mp hpos
  rcases hnonempty with ⟨b, hb⟩
  have hsatb : φ.satisfiedBy b := by
    simpa [satSet] using hb
  ext a; constructor
  · intro ha
    have hmem := (buildDQProblem φ).mem_optimalActions_iff (s := ()) (a := a) |>.1 ha
    rcases hmem with ⟨_, hmax⟩
    cases a with
    | none =>
        simp
    | some asg =>
        have hsat : φ.satisfiedBy asg := by
          by_contra hnsat
          have hcmp := hmax (some b) (by simp [buildDQProblem])
          have hcmp' := hcmp
          simp [buildDQProblem, hsatb, hnsat] at hcmp'
        -- show membership in map
        have : some asg ∈ (satSet φ).map (someEmbedding φ.numVars) := by
          refine Finset.mem_map.mpr ?_
          refine ⟨asg, ?_, rfl⟩
          simp [satSet, hsat]
        have : some asg ∈ insert none
            ((satSet φ).map (someEmbedding φ.numVars)) := by
          exact Finset.mem_insert_of_mem this
        exact this
  · intro ha
    rcases Finset.mem_insert.mp ha with hnone | hmap
    · have ha' : a = none := by simpa using hnone
      subst ha'
      refine (buildDQProblem φ).mem_optimalActions_iff (s := ()) (a := none) |>.2 ?_
      refine ⟨by simp [buildDQProblem], ?_⟩
      intro a' ha'
      cases a' with
      | none => simp [buildDQProblem]
      | some asg' =>
          by_cases hs' : φ.satisfiedBy asg'
          · simp [buildDQProblem, hs']
          · simp [buildDQProblem, hs']
    · rcases Finset.mem_map.mp hmap with ⟨asg, hasg, rfl⟩
      have hsat : φ.satisfiedBy asg := by
        simpa [satSet] using hasg
      refine (buildDQProblem φ).mem_optimalActions_iff (s := ()) (a := some asg) |>.2 ?_
      refine ⟨by simp [buildDQProblem], ?_⟩
      intro a' ha'
      cases a' with
      | none =>
          simp [buildDQProblem, hsat]
      | some asg' =>
          by_cases hs' : φ.satisfiedBy asg'
          · simp [buildDQProblem, hsat, hs']
          · simp [buildDQProblem, hsat, hs']

/-! ## Decision quotient -/

lemma decisionQuotient_cases (φ : SAT3Instance) :
    (buildDQProblem φ).decisionQuotient =
      ((countSatisfyingAssignments φ + 1 : ℕ) : ℚ) /
        (1 + 2 ^ φ.numVars : ℚ) := by
  classical
  let dp : FiniteDecisionProblem (A := DQAction φ.numVars) (S := Unit) :=
    buildDQProblem φ
  have hmain :
      dp.decisionQuotient =
        ((countSatisfyingAssignments φ + 1 : ℕ) : ℚ) /
          (1 + 2 ^ φ.numVars : ℚ) := by
    by_cases hzero : countSatisfyingAssignments φ = 0
    · have hopt : dp.optimalActions () = {none} := by
        simpa [dp] using optimalActions_unsat φ hzero
      have hden : dp.actions.card = 1 + 2 ^ φ.numVars := by
        simpa [dp] using actions_card φ
      have hcard_nonzero : dp.actions.card ≠ 0 := by
        intro hzero'
        have hzero'' := hzero'
        simp [hden] at hzero''
      have hq'' :
          dp.decisionQuotient =
            (↑((dp.optimalActions ()).card : ℕ) : ℚ) /
              ↑(dp.actions.card) := by
        unfold FiniteDecisionProblem.decisionQuotient
        by_cases hzero' : dp.actions.card = 0
        · exact (hcard_nonzero hzero').elim
        · simp [hzero', dp, buildDQProblem, -Finset.card_eq_zero]
      have hoptCard : (dp.optimalActions ()).card = 1 := by
        rw [hopt]
        simp
      have hq :
          dp.decisionQuotient =
            ((countSatisfyingAssignments φ + 1 : ℕ) : ℚ) /
              (1 + 2 ^ φ.numVars : ℚ) := by
        calc
          dp.decisionQuotient =
              (↑((dp.optimalActions ()).card : ℕ) : ℚ) / ↑(dp.actions.card) := hq''
          _ = ((countSatisfyingAssignments φ + 1 : ℕ) : ℚ) /
                (1 + 2 ^ φ.numVars : ℚ) := by
              rw [hoptCard, hden, hzero]
              simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      exact hq
    · have hpos : countSatisfyingAssignments φ > 0 := Nat.pos_of_ne_zero hzero
      have hopt : dp.optimalActions () =
          insert none
            ((satSet φ).map (someEmbedding φ.numVars)) := by
        simpa [dp] using optimalActions_sat φ hpos
      have hden : dp.actions.card = 1 + 2 ^ φ.numVars := by
        simpa [dp] using actions_card φ
      have hcard_nonzero : dp.actions.card ≠ 0 := by
        intro hzero'
        have hzero'' := hzero'
        simp [hden] at hzero''
      have hcard_map :
          ((satSet φ).map (someEmbedding φ.numVars)).card =
            (satSet φ).card := by
        exact (Finset.card_map (f := someEmbedding φ.numVars) (s := satSet φ))
      have hnone_not_mem :
          (none : DQAction φ.numVars) ∉
            (satSet φ).map (someEmbedding φ.numVars) := by
        intro hmem
        rcases Finset.mem_map.mp hmem with ⟨a, _, h⟩
        cases h
      have hoptCard :
          (dp.optimalActions ()).card = countSatisfyingAssignments φ + 1 := by
        rw [hopt]
        simp [hcard_map, countSatisfyingAssignments, hnone_not_mem, Nat.add_comm]
      have hq :
          dp.decisionQuotient =
            ((countSatisfyingAssignments φ + 1 : ℕ) : ℚ) /
              (1 + 2 ^ φ.numVars : ℚ) := by
        calc
          dp.decisionQuotient =
              (↑((dp.optimalActions ()).card : ℕ) : ℚ) / ↑(dp.actions.card) := by
                unfold FiniteDecisionProblem.decisionQuotient
                by_cases hzero' : dp.actions.card = 0
                · exact (hcard_nonzero hzero').elim
                · simp [hzero', dp, buildDQProblem, -Finset.card_eq_zero]
          _ = ((countSatisfyingAssignments φ + 1 : ℕ) : ℚ) /
                (1 + 2 ^ φ.numVars : ℚ) := by
              rw [hoptCard, hden]
              simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      exact hq
  simpa [dp] using hmain

/-- Reduction instance. -/
noncomputable def sharpSATtoDQ (φ : SharpSATInstance) :
    FiniteDecisionProblem (A := DQAction φ.formula.numVars) (S := Unit) :=
  buildDQProblem φ.formula

/-- Correctness of the reduction. -/
theorem sharpSAT_encoded_in_DQ (φ : SharpSATInstance) :
    (sharpSATtoDQ φ).decisionQuotient =
      ((countSatisfyingAssignments φ.formula + 1 : ℕ) : ℚ) /
        (1 + 2 ^ φ.formula.numVars : ℚ) := by
  classical
  simpa [sharpSATtoDQ] using decisionQuotient_cases (φ := φ.formula)

/-- Existence of the #P-hard reduction. -/
theorem decision_quotient_sharp_P_hard :
    ∃ reduce : (φ : SharpSATInstance) →
        FiniteDecisionProblem (A := DQAction φ.formula.numVars) (S := Unit),
      ∀ φ, (reduce φ).decisionQuotient =
        ((countSatisfyingAssignments φ.formula + 1 : ℕ) : ℚ) /
          (1 + 2 ^ φ.formula.numVars : ℚ) :=
  ⟨fun φ => sharpSATtoDQ φ, sharpSAT_encoded_in_DQ⟩

end DecisionQuotient
