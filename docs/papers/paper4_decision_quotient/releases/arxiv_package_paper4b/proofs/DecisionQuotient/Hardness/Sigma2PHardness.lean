/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/Sigma2PHardness.lean - Σ₂ᴾ Completeness Proofs

  This module proves Σ₂ᴾ-completeness for decision-quotient problems:
  - Shows MINIMUM-SUFFICIENT-SET is Σ₂ᴾ-complete
  - Gadget constructions for QBF encoding

  ## Triviality Level
  NONTRIVIAL: This is a core hardness proof - Σ₂ᴾ completeness.

  ## Dependencies
  - Chain: QBF.lean + Sufficiency.lean → here (Σ₂ᴾ reduction)
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import DecisionQuotient.Instances
import DecisionQuotient.Hardness.QBF
import DecisionQuotient.HardnessDistribution
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace DecisionQuotient

open Classical
open scoped Finset

set_option linter.unnecessarySimpa false

namespace Sigma2PHardness

/-- Boolean bit as a natural number. -/
def bit (b : Bool) : Nat := if b then 1 else 0

lemma bit_le_one (b : Bool) : bit b ≤ 1 := by
  cases b <;> simp [bit]

lemma bit_lt_two (b : Bool) : bit b < 2 := by
  cases b <;> decide

lemma two_mul_add_one_lt_two_mul {a b : Nat} (h : a < b) : 2 * a + 1 < 2 * b := by
  have h' : a + 1 ≤ b := Nat.succ_le_iff.mpr h
  have hmul : 2 * (a + 1) ≤ 2 * b := Nat.mul_le_mul_left 2 h'
  have hmul' : 2 * a + 2 ≤ 2 * b := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmul
  have hlt : 2 * a + 1 < 2 * a + 2 := Nat.lt_succ_self (2 * a + 1)
  exact lt_of_lt_of_le hlt hmul'

abbrev GadgetState (m k : ℕ) := Fin (2 * m + k) → Bool

/-- Coordinate for the gadget pairs (x-encoding). -/
def cCoord (m k : ℕ) (i : Fin m) (b : Bool) : Fin (2 * m + k) :=
  ⟨2 * i.val + bit b, by
    have hi : i.val < m := i.isLt
    by_cases hb : b
    · have hlt : 2 * i.val + 1 < 2 * m := two_mul_add_one_lt_two_mul hi
      have hlt' : 2 * i.val + bit b < 2 * m := by
        simpa [bit, hb] using hlt
      exact lt_of_lt_of_le hlt' (Nat.le_add_right _ _)
    · have hlt : 2 * i.val < 2 * m := (Nat.mul_lt_mul_left (Nat.succ_pos 1)).2 hi
      have hlt' : 2 * i.val + bit b < 2 * m := by
        simpa [bit, hb] using hlt
      exact lt_of_lt_of_le hlt' (Nat.le_add_right _ _)⟩

/-- Coordinate for the universal (y) variables. -/
def yCoord (m k : ℕ) (j : Fin k) : Fin (2 * m + k) :=
  ⟨2 * m + j.val, by
    have hj : j.val < k := j.isLt
    exact Nat.add_lt_add_left hj (2 * m)⟩

@[simp] lemma cCoord_val (m k : ℕ) (i : Fin m) (b : Bool) :
    (cCoord m k i b).val = 2 * i.val + bit b := rfl

@[simp] lemma yCoord_val (m k : ℕ) (j : Fin k) :
    (yCoord m k j).val = 2 * m + j.val := rfl

lemma cCoord_val_lt_of_lt {m k : ℕ} {i j : Fin m} (hij : i.val < j.val)
    (b b' : Bool) :
    (cCoord m k i b).val < (cCoord m k j b').val := by
  have hbit : bit b ≤ 1 := bit_le_one b
  have hbit' : bit b' ≤ 1 := bit_le_one b'
  have hle : 2 * i.val + bit b ≤ 2 * i.val + 1 := Nat.add_le_add_left hbit _
  have hlt : 2 * i.val + 1 < 2 * j.val := two_mul_add_one_lt_two_mul hij
  have hlt' : 2 * i.val + bit b < 2 * j.val := lt_of_le_of_lt hle hlt
  have hle' : 2 * j.val ≤ 2 * j.val + bit b' := Nat.le_add_right _ _
  exact lt_of_lt_of_le hlt' hle'

lemma cCoord_inj {m k : ℕ} {i j : Fin m} {b b' : Bool} :
    cCoord m k i b = cCoord m k j b' → i = j := by
  intro h
  have hval : (cCoord m k i b).val = (cCoord m k j b').val := congrArg Fin.val h
  have htri := lt_trichotomy i.val j.val
  cases htri with
  | inl hlt =>
      have hlt' : (cCoord m k i b).val < (cCoord m k j b').val :=
        cCoord_val_lt_of_lt (m := m) (k := k) hlt b b'
      exact (ne_of_lt hlt' hval).elim
  | inr hrest =>
      cases hrest with
      | inl heq =>
          apply Fin.ext
          exact heq
      | inr hgt =>
          have hlt' : (cCoord m k j b').val < (cCoord m k i b).val :=
            cCoord_val_lt_of_lt (m := m) (k := k) hgt b' b
          exact (ne_of_lt hlt' hval.symm).elim

lemma cCoord_inj_bits {m k : ℕ} {i : Fin m} {b b' : Bool} :
    cCoord m k i b = cCoord m k i b' → b = b' := by
  intro h
  have hval : 2 * i.val + bit b = 2 * i.val + bit b' := by
    simpa [cCoord_val] using congrArg Fin.val h
  have hbit : bit b = bit b' := Nat.add_left_cancel hval
  cases b <;> cases b' <;> simp [bit] at hbit <;> simp [hbit]

/-- Valid coordinate set: choose exactly one from each gadget pair. -/
def validI (m k : ℕ) (I : Finset (Fin (2 * m + k))) : Prop :=
  I.card = m ∧ ∀ i : Fin m, (cCoord m k i false ∈ I) ↔ (cCoord m k i true ∉ I)

/-- Decode a coordinate set into an assignment. -/
def encodeX (m k : ℕ) (I : Finset (Fin (2 * m + k))) : Fin m → Bool :=
  fun i => decide (cCoord m k i true ∈ I)

/-- The canonical coordinate set encoded by an assignment. -/
def I_of_x (m k : ℕ) (x : Fin m → Bool) : Finset (Fin (2 * m + k)) :=
  Finset.univ.image (fun i : Fin m => cCoord m k i (x i))

lemma cCoord_injective (m k : ℕ) (x : Fin m → Bool) :
    Function.Injective (fun i : Fin m => cCoord m k i (x i)) := by
  intro i j h
  exact cCoord_inj (m := m) (k := k) (i := i) (j := j) (b := x i) (b' := x j) h

lemma I_of_x_card (m k : ℕ) (x : Fin m → Bool) :
    (I_of_x m k x).card = m := by
  classical
  have hinj : Function.Injective (fun i : Fin m => cCoord m k i (x i)) :=
    cCoord_injective (m := m) (k := k) x
  have hcard :
      (Finset.univ.image (fun i : Fin m => cCoord m k i (x i))).card = m := by
    simpa [Finset.card_univ] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin m))) hinj)
  simpa [I_of_x] using hcard

lemma mem_I_of_x_iff {m k : ℕ} (x : Fin m → Bool) (i : Fin m) (b : Bool) :
    cCoord m k i b ∈ I_of_x m k x ↔ x i = b := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, _, hEq⟩
    have hij : j = i :=
      cCoord_inj (m := m) (k := k) (i := j) (j := i) (b := x j) (b' := b) hEq
    subst j
    have hb : x i = b := by
      exact (cCoord_inj_bits (m := m) (k := k) (i := i) (b := x i) (b' := b) hEq)
    exact hb
  · intro h
    refine Finset.mem_image.mpr ?_
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [h]

lemma validI_I_of_x (m k : ℕ) (x : Fin m → Bool) :
    validI m k (I_of_x m k x) := by
  refine ⟨I_of_x_card (m := m) (k := k) x, ?_⟩
  intro i
  have hfalse : cCoord m k i false ∈ I_of_x m k x ↔ x i = false :=
    mem_I_of_x_iff (m := m) (k := k) x i false
  have htrue : cCoord m k i true ∈ I_of_x m k x ↔ x i = true :=
    mem_I_of_x_iff (m := m) (k := k) x i true
  have hbool : x i = false ↔ ¬ x i = true := by
    cases hx : x i <;> simp [hx]
  have htrue' : (cCoord m k i true ∉ I_of_x m k x) ↔ ¬ x i = true := by
    exact not_congr htrue
  calc
    cCoord m k i false ∈ I_of_x m k x ↔ x i = false := hfalse
    _ ↔ ¬ x i = true := hbool
    _ ↔ cCoord m k i true ∉ I_of_x m k x := htrue'.symm

lemma encodeX_I_of_x (m k : ℕ) (x : Fin m → Bool) :
    encodeX m k (I_of_x m k x) = x := by
  funext i
  by_cases hx : x i
  · have hmem : cCoord m k i true ∈ I_of_x m k x :=
      (mem_I_of_x_iff (m := m) (k := k) x i true).2 hx
    simp [encodeX, hmem, hx]
  · have hnot : cCoord m k i true ∉ I_of_x m k x := by
      intro hmem
      have hx' : x i = true := (mem_I_of_x_iff (m := m) (k := k) x i true).1 hmem
      exact (hx hx').elim
    simp [encodeX, hnot, hx]

lemma I_of_encodeX_subset {m k : ℕ} (I : Finset (Fin (2 * m + k)))
    (hI : validI m k I) :
    I_of_x m k (encodeX m k I) ⊆ I := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
  by_cases hmem : cCoord m k i true ∈ I
  · have henc : encodeX m k I i = true := by
      simp [encodeX, hmem]
    simpa [henc] using hmem
  · have henc : encodeX m k I i = false := by
      simp [encodeX, hmem]
    have hpair : (cCoord m k i false ∈ I) ↔ (cCoord m k i true ∉ I) := hI.2 i
    have hfalse : cCoord m k i false ∈ I := hpair.mpr hmem
    simpa [henc] using hfalse

lemma I_eq_I_of_encodeX {m k : ℕ} (I : Finset (Fin (2 * m + k)))
    (hI : validI m k I) :
    I = I_of_x m k (encodeX m k I) := by
  classical
  have hsubset : I_of_x m k (encodeX m k I) ⊆ I := I_of_encodeX_subset (m := m) (k := k) I hI
  have hcardI : I.card = m := hI.1
  have hcardIm : (I_of_x m k (encodeX m k I)).card = m :=
    I_of_x_card (m := m) (k := k) (encodeX m k I)
  have hcard : #(I) ≤ #(I_of_x m k (encodeX m k I)) := by
    simpa [hcardI, hcardIm]
  have hEq := Finset.eq_of_subset_of_card_le hsubset hcard
  exact hEq.symm

lemma validI_iff_exists_x {m k : ℕ} (I : Finset (Fin (2 * m + k))) :
    validI m k I ↔ ∃ x : Fin m → Bool, I = I_of_x m k x := by
  constructor
  · intro hI
    refine ⟨encodeX m k I, ?_⟩
    exact I_eq_I_of_encodeX (m := m) (k := k) I hI
  · rintro ⟨x, rfl⟩
    exact validI_I_of_x (m := m) (k := k) x

end Sigma2PHardness

namespace Sigma2PHardness

/-! ### Sufficiency via relevant coordinates on Boolean cubes -/

theorem univ_sufficient_bool {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) :
    dp.isSufficient (Finset.univ : Finset (Fin n)) := by
  classical
  have hinj : ∀ s s' : (Fin n → Bool),
      (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s' := by
    intro s s' h
    funext i
    simpa using h i
  exact dp.univ_sufficient_of_injective hinj

theorem sufficient_of_contains_relevant {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n))
    (hI : ∀ i : Fin n, dp.isRelevant i → i ∈ I) :
    dp.isSufficient I := by
  classical
  let J : Finset (Fin n) := Finset.univ \ I
  have hJirrel : ∀ j ∈ J, dp.isIrrelevant j := by
    intro j hj
    have hjI : j ∉ I := by
      exact (Finset.mem_sdiff.mp hj).2
    have hnotrel : ¬ dp.isRelevant j := by
      intro hrel
      exact hjI (hI j hrel)
    exact (dp.irrelevant_iff_not_relevant j).mpr hnotrel
  have hbase : dp.isSufficient (Finset.univ : Finset (Fin n)) :=
    univ_sufficient_bool dp
  have hInd :
      ∀ J' : Finset (Fin n),
        (∀ j ∈ J', dp.isIrrelevant j) →
        dp.isSufficient (Finset.univ \ J') := by
    intro J'
    refine Finset.induction ?h0 ?hstep J'
    · intro _
      simpa using hbase
    · intro a s ha hInd' hIrrel
      have hIrrel_a : dp.isIrrelevant a := hIrrel a (Finset.mem_insert_self a s)
      have hIrrel_s : ∀ j ∈ s, dp.isIrrelevant j := by
        intro j hj
        exact hIrrel j (Finset.mem_insert_of_mem hj)
      have hSuff : dp.isSufficient (Finset.univ \ s) := hInd' hIrrel_s
      have hErase : dp.isSufficient ((Finset.univ \ s).erase a) :=
        dp.sufficient_erase_irrelevant' (I := (Finset.univ \ s)) a hSuff hIrrel_a
      simpa [Finset.sdiff_insert] using hErase
  have hSuffJ : dp.isSufficient (Finset.univ \ J) := hInd J hJirrel
  -- univ \ (univ \ I) = I
  simpa [J] using hSuffJ

theorem sufficient_iff_relevant_subset {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    dp.isSufficient I ↔ (∀ i : Fin n, dp.isRelevant i → i ∈ I) := by
  constructor
  · intro hI
    exact dp.sufficient_contains_all_relevant I hI
  · intro hI
    exact sufficient_of_contains_relevant dp I hI

noncomputable def relevantFinset {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => decide (dp.isRelevant i))

lemma mem_relevantFinset_iff {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (i : Fin n) :
    i ∈ relevantFinset dp ↔ dp.isRelevant i := by
  classical
  simp [relevantFinset]

theorem sufficient_iff_relevantFinset_subset {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    dp.isSufficient I ↔ relevantFinset dp ⊆ I := by
  constructor
  · intro hI i hi
    have hrel : dp.isRelevant i := (mem_relevantFinset_iff dp i).1 hi
    exact (sufficient_iff_relevant_subset dp I).1 hI i hrel
  · intro hsub
    refine (sufficient_iff_relevant_subset dp I).2 ?_
    intro i hrel
    have hi : i ∈ relevantFinset dp := (mem_relevantFinset_iff dp i).2 hrel
    exact hsub hi

/-! ### Representation Gap ε (first-class object) -/

/-- Representation gap ε between attended coordinates `I` and the minimal sufficient set.
    This is the symmetric-difference cardinality:
    attended-but-irrelevant + relevant-but-unattended. -/
noncomputable def representationGap {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) : ℕ :=
  (I \ relevantFinset dp).card + (relevantFinset dp \ I).card

/-- ε decomposes as waste plus unhandled-relevant coordinates. -/
theorem representationGap_eq_waste_plus_missing {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    representationGap dp I =
      (I \ relevantFinset dp).card + (relevantFinset dp \ I).card := by
  rfl

/-- The unhandled-relevant component of ε is exactly `gapCard`. -/
theorem representationGap_missing_eq_gapCard {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    (relevantFinset dp \ I).card =
      HardnessDistribution.gapCard (relevantFinset dp) I := by
  rfl

/-- Zero representation gap iff the attended set is exactly the relevant set. -/
theorem representationGap_eq_zero_iff {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    representationGap dp I = 0 ↔ I = relevantFinset dp := by
  constructor
  · intro hgap
    have hleft_card : (I \ relevantFinset dp).card = 0 :=
      Nat.eq_zero_of_add_eq_zero_right hgap
    have hright_card : (relevantFinset dp \ I).card = 0 :=
      Nat.eq_zero_of_add_eq_zero_left hgap
    have hleft_empty : I \ relevantFinset dp = ∅ :=
      (Finset.card_eq_zero).1 hleft_card
    have hright_empty : relevantFinset dp \ I = ∅ :=
      (Finset.card_eq_zero).1 hright_card
    have hI_sub_rel : I ⊆ relevantFinset dp :=
      (Finset.sdiff_eq_empty_iff_subset).1 hleft_empty
    have hRel_sub_I : relevantFinset dp ⊆ I :=
      (Finset.sdiff_eq_empty_iff_subset).1 hright_empty
    exact Finset.Subset.antisymm hI_sub_rel hRel_sub_I
  · intro hEq
    subst hEq
    simp [representationGap]

/-- Zero representation gap iff the set is minimal sufficient (Boolean-coordinate model). -/
theorem representationGap_zero_iff_minimalSufficient {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    representationGap dp I = 0 ↔ dp.isMinimalSufficient I := by
  constructor
  · intro hgap
    have hEq : I = relevantFinset dp := (representationGap_eq_zero_iff dp I).1 hgap
    subst hEq
    refine ⟨?_, ?_⟩
    · exact (sufficient_iff_relevantFinset_subset dp _).2 (Finset.Subset.refl _)
    · intro J hJ hJsuff
      have hJsub : J ⊆ relevantFinset dp := (Finset.ssubset_iff_subset_ne.mp hJ).1
      have hJne : J ≠ relevantFinset dp := (Finset.ssubset_iff_subset_ne.mp hJ).2
      have hRel_sub_J : relevantFinset dp ⊆ J :=
        (sufficient_iff_relevantFinset_subset dp J).1 hJsuff
      have hJeq : J = relevantFinset dp := Finset.Subset.antisymm hJsub hRel_sub_J
      exact hJne hJeq
  · intro hmin
    have hmem : ∀ i : Fin n, i ∈ I ↔ dp.isRelevant i :=
      dp.minimalSufficient_iff_relevant I hmin
    have hEq : I = relevantFinset dp := by
      apply Finset.ext
      intro i
      constructor
      · intro hi
        exact (mem_relevantFinset_iff dp i).2 ((hmem i).1 hi)
      · intro hri
        exact (hmem i).2 ((mem_relevantFinset_iff dp i).1 hri)
    exact (representationGap_eq_zero_iff dp I).2 hEq

/-- Exact relevance identifiability: candidate coordinates match the full relevant set. -/
def exactlyIdentifiesRelevant {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) : Prop :=
  I = relevantFinset dp

theorem exactlyIdentifiesRelevant_iff_mem_relevant {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    exactlyIdentifiesRelevant dp I ↔ ∀ i : Fin n, i ∈ I ↔ dp.isRelevant i := by
  constructor
  · intro h i
    subst h
    simpa using (mem_relevantFinset_iff dp i)
  · intro hmem
    apply Finset.ext
    intro i
    exact (hmem i).trans (mem_relevantFinset_iff dp i).symm

theorem exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    exactlyIdentifiesRelevant dp I ↔
      dp.isSufficient I ∧ I ⊆ relevantFinset dp := by
  constructor
  · intro h
    subst h
    constructor
    · exact (sufficient_iff_relevantFinset_subset dp _).2 (Finset.Subset.refl _)
    · exact Finset.Subset.refl _
  · rintro ⟨hI, hsub⟩
    have hrelSub : relevantFinset dp ⊆ I :=
      (sufficient_iff_relevantFinset_subset dp I).1 hI
    exact Finset.Subset.antisymm hsub hrelSub

/-- Certifying ε = 0 is exactly exact relevance identification. -/
theorem representationGap_zero_iff_exactlyIdentifiesRelevant {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    representationGap dp I = 0 ↔ exactlyIdentifiesRelevant dp I := by
  simpa [exactlyIdentifiesRelevant] using (representationGap_eq_zero_iff dp I)

/-- Certifying ε = 0 is equivalent to sufficiency plus no extra coordinates outside relevance. -/
theorem representationGap_zero_iff_sufficient_and_subset_relevantFinset {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    representationGap dp I = 0 ↔
      dp.isSufficient I ∧ I ⊆ relevantFinset dp := by
  calc
    representationGap dp I = 0
        ↔ exactlyIdentifiesRelevant dp I :=
      representationGap_zero_iff_exactlyIdentifiesRelevant dp I
    _ ↔ dp.isSufficient I ∧ I ⊆ relevantFinset dp :=
      exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset dp I

/-- Certifying ε = 0 requires establishing sufficiency for `I`. -/
theorem representationGap_zero_implies_sufficient {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    representationGap dp I = 0 → dp.isSufficient I := by
  intro hgap
  exact (representationGap_zero_iff_sufficient_and_subset_relevantFinset dp I).1 hgap |>.1

/-- Exact relevance identification implies ε = 0. -/
theorem exactlyIdentifiesRelevant_implies_representationGap_zero {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) :
    exactlyIdentifiesRelevant dp I → representationGap dp I = 0 := by
  intro hI
  exact (representationGap_zero_iff_exactlyIdentifiesRelevant dp I).2 hI

/-- Size-bounded ε=0 search collapses to the relevance-cardinality bound. -/
theorem min_representationGap_zero_iff_relevant_card {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ) :
    (∃ I : Finset (Fin n), I.card ≤ k ∧ representationGap dp I = 0) ↔
      (relevantFinset dp).card ≤ k := by
  constructor
  · rintro ⟨I, hcard, hgap⟩
    have hEq : I = relevantFinset dp := (representationGap_eq_zero_iff dp I).1 hgap
    simpa [hEq] using hcard
  · intro hcard
    refine ⟨relevantFinset dp, hcard, ?_⟩
    exact (representationGap_eq_zero_iff dp _).2 rfl

theorem not_sufficient_of_missing_relevantFinset {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) (i : Fin n)
    (hrel : i ∈ relevantFinset dp) (hmiss : i ∉ I) :
    ¬ dp.isSufficient I := by
  intro hI
  have hsub : relevantFinset dp ⊆ I :=
    (sufficient_iff_relevantFinset_subset dp I).1 hI
  exact hmiss (hsub hrel)

theorem min_sufficient_set_iff_relevant_card {A : Type*} {n : ℕ}
    (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ) :
    (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
      (relevantFinset dp).card ≤ k := by
  constructor
  · rintro ⟨I, hcard, hI⟩
    have hsub : relevantFinset dp ⊆ I :=
      (sufficient_iff_relevantFinset_subset dp I).1 hI
    exact le_trans (Finset.card_le_card hsub) hcard
  · intro hcard
    refine ⟨relevantFinset dp, hcard, ?_⟩
    exact (sufficient_iff_relevantFinset_subset dp _).2 (Finset.Subset.refl _)

/-! ### Vector 1 obstruction (specific predicate not representable) -/

def x00 : Fin 2 → Bool := fun _ => false
def x11 : Fin 2 → Bool := fun _ => true
def x01 : Fin 2 → Bool := fun i => if i = ⟨0, by decide⟩ then false else true

def goodEq (x : Fin 2 → Bool) : Prop :=
  x ⟨0, by decide⟩ = x ⟨1, by decide⟩

lemma goodEq_x00 : goodEq x00 := by
  simp [goodEq, x00]

lemma goodEq_x11 : goodEq x11 := by
  simp [goodEq, x11]

lemma not_goodEq_x01 : ¬ goodEq x01 := by
  simp [goodEq, x01]

lemma disjoint_I_of_x00_x11 :
    Disjoint (I_of_x 2 1 x00) (I_of_x 2 1 x11) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro a ha00 ha11
  rcases Finset.mem_image.mp ha00 with ⟨i, _, hEq⟩
  subst hEq
  have h11 : x11 i = false :=
    (mem_I_of_x_iff (m := 2) (k := 1) x11 i false).1 ha11
  simp [x11] at h11

theorem vector1_obstruction :
    ¬ ∃ dp : DecisionProblem Bool (GadgetState 2 1),
      ∀ x : Fin 2 → Bool,
        dp.isSufficient (I_of_x 2 1 x) ↔ goodEq x := by
  intro h
  rcases h with ⟨dp, hdp⟩
  have hsuff00 : dp.isSufficient (I_of_x 2 1 x00) := (hdp x00).2 goodEq_x00
  have hsuff11 : dp.isSufficient (I_of_x 2 1 x11) := (hdp x11).2 goodEq_x11
  have hrel_in_00 :
      ∀ i : Fin (2 * 2 + 1), dp.isRelevant i → i ∈ I_of_x 2 1 x00 :=
    (sufficient_iff_relevant_subset dp (I_of_x 2 1 x00)).1 hsuff00
  have hrel_in_11 :
      ∀ i : Fin (2 * 2 + 1), dp.isRelevant i → i ∈ I_of_x 2 1 x11 :=
    (sufficient_iff_relevant_subset dp (I_of_x 2 1 x11)).1 hsuff11
  have hno_rel : ∀ i : Fin (2 * 2 + 1), ¬ dp.isRelevant i := by
    intro i hrel
    have hi00 : i ∈ I_of_x 2 1 x00 := hrel_in_00 i hrel
    have hi11 : i ∈ I_of_x 2 1 x11 := hrel_in_11 i hrel
    have hdis := disjoint_I_of_x00_x11
    exact (Finset.disjoint_left.mp hdis) hi00 hi11
  have hsuff01 : dp.isSufficient (I_of_x 2 1 x01) := by
    refine (sufficient_iff_relevant_subset dp (I_of_x 2 1 x01)).2 ?_
    intro i hrel
    exact (hno_rel i hrel).elim
  have hfalse : goodEq x01 := (hdp x01).1 hsuff01
  exact not_goodEq_x01 hfalse

end Sigma2PHardness

end DecisionQuotient
