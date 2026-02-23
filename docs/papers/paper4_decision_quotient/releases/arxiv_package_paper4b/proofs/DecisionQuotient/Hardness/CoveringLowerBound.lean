import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import DecisionQuotient.Instances
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  Covering lower bound for refutation certificates of MINIMUM-SUFFICIENT-SET.

  The key idea formalized here: for any polynomial-size set of witness pairs P,
  we can construct an Opt function that makes a fixed I insufficient while every
  pair in P agrees on Opt. This is a certificate lower bound, not a coNP
  separation.
-/

namespace DecisionQuotient

open Classical

set_option linter.unnecessarySimpa false

abbrev BinaryState (n : ℕ) := Fin n → Bool

instance (n : ℕ) : CoordinateSpace (BinaryState n) n := by
  infer_instance

instance (n : ℕ) : Fintype (BinaryState n) := by
  dsimp [BinaryState]
  infer_instance

@[simp] lemma proj_binary_state {n : ℕ} (s : BinaryState n) (i : Fin n) :
    CoordinateSpace.proj s i = s i := rfl

def agreementSet {n : ℕ} (s s' : BinaryState n) : Finset (Fin n) :=
  Finset.univ.filter fun i => s i = s' i

lemma agreeOn_iff_subset_agreementSet {n : ℕ} (s s' : BinaryState n) (I : Finset (Fin n)) :
    agreeOn s s' I ↔ I ⊆ agreementSet s s' := by
  constructor
  · intro h i hi
    have h' : s i = s' i := by
      simpa using h i hi
    simp [agreementSet, h', hi]
  · intro h i hi
    have hi' : i ∈ agreementSet s s' := h hi
    have h' : s i = s' i := by
      simpa [agreementSet] using hi'
    simpa using h'

def covers {n : ℕ} (s s' : BinaryState n) (I : Finset (Fin n)) : Prop :=
  I ⊆ agreementSet s s'

lemma covers_iff_agreeOn {n : ℕ} (s s' : BinaryState n) (I : Finset (Fin n)) :
    covers s s' I ↔ agreeOn s s' I :=
  (agreeOn_iff_subset_agreementSet s s' I).symm

def endpoints {n : ℕ} (P : Finset (BinaryState n × BinaryState n)) : Finset (BinaryState n) :=
  (P.image Prod.fst) ∪ (P.image Prod.snd)

lemma endpoints_card_le {n : ℕ} (P : Finset (BinaryState n × BinaryState n)) :
    (endpoints P).card ≤ 2 * P.card := by
  classical
  have hfst : (P.image Prod.fst).card ≤ P.card := by
    exact Finset.card_image_le
  have hsnd : (P.image Prod.snd).card ≤ P.card := by
    exact Finset.card_image_le
  have hunion : (endpoints P).card ≤ (P.image Prod.fst).card + (P.image Prod.snd).card := by
    simpa [endpoints] using (Finset.card_union_le (P.image Prod.fst) (P.image Prod.snd))
  have hsum : (P.image Prod.fst).card + (P.image Prod.snd).card ≤ P.card + P.card :=
    Nat.add_le_add hfst hsnd
  calc
    (endpoints P).card
        ≤ (P.image Prod.fst).card + (P.image Prod.snd).card := hunion
    _ ≤ P.card + P.card := hsum
    _ = 2 * P.card := by simp [Nat.two_mul, Nat.mul_comm]

lemma card_binary_state (n : ℕ) : Fintype.card (BinaryState n) = 2 ^ n := by
  simp [BinaryState, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

lemma exists_not_mem_of_card_lt_univ {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (h : s.card < (Finset.univ : Finset α).card) :
    ∃ x : α, x ∉ s := by
  classical
  by_contra hno
  push_neg at hno
  have hsub : (Finset.univ : Finset α) ⊆ s := by
    intro x _; exact hno x
  have hsup : s ⊆ (Finset.univ : Finset α) := by
    intro x hx; exact Finset.mem_univ x
  have hEq : s = (Finset.univ : Finset α) := Finset.Subset.antisymm hsup hsub
  have hcard : s.card = (Finset.univ : Finset α).card := by
    simp [hEq]
  have hcontra : ¬ s.card < (Finset.univ : Finset α).card := by
    simp [hcard]
  exact hcontra h

lemma exists_state_not_in_endpoints {n : ℕ} (P : Finset (BinaryState n × BinaryState n))
    (hn : 1 ≤ n) (hP : P.card < 2 ^ (n - 1)) :
    ∃ s : BinaryState n, s ∉ endpoints P := by
  classical
  have hP2 : 2 * P.card < 2 ^ n := by
    have h' : 2 * P.card < 2 * 2 ^ (n - 1) :=
      (Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hP
    have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
      cases n with
      | zero => cases hn
      | succ n =>
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    simpa [hpow] using h'
  have hcard_end : (endpoints P).card < (Finset.univ : Finset (BinaryState n)).card := by
    have hle : (endpoints P).card ≤ 2 * P.card := endpoints_card_le P
    have hlt : (endpoints P).card < 2 ^ n := lt_of_le_of_lt hle hP2
    simpa [card_binary_state] using hlt
  simpa using (exists_not_mem_of_card_lt_univ (s := endpoints P) hcard_end)

lemma exists_coord_not_mem {n : ℕ} (I : Finset (Fin n)) (hI : I.card < n) :
    ∃ j : Fin n, j ∉ I := by
  classical
  by_contra hno
  push_neg at hno
  have hEq : I = Finset.univ := by
    apply Finset.ext
    intro j
    constructor
    · intro hj; exact Finset.mem_univ j
    · intro _; exact hno j
  have hcard : I.card = n := by
    simp [hEq]
  have hI' : n < n := by
    simpa [hcard] using hI
  exact (Nat.lt_irrefl n) hI'

def flipAt {n : ℕ} (s : BinaryState n) (j : Fin n) : BinaryState n :=
  fun i => if i = j then !s i else s i

lemma flipAt_ne {n : ℕ} (s : BinaryState n) (j : Fin n) :
    flipAt s j ≠ s := by
  intro h
  by_cases hsj : s j
  · have h' := congrArg (fun f => f j) h
    simpa [flipAt, hsj] using h'
  · have h' := congrArg (fun f => f j) h
    simpa [flipAt, hsj] using h'

lemma agreeOn_flipAt {n : ℕ} (s : BinaryState n) (I : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ I) :
    agreeOn (flipAt s j) s I := by
  intro i hi
  have hne : i ≠ j := by
    intro h; subst h; exact hj hi
  by_cases h' : i = j
  · exact (hne h').elim
  · simp [flipAt, h']

noncomputable def adversarialOpt {n : ℕ} (s₁ : BinaryState n) : BinaryState n → Bool :=
  fun s => decide (s = s₁)

lemma adversarialOpt_eq_false_of_ne {n : ℕ} (s₁ s : BinaryState n) (h : s ≠ s₁) :
    adversarialOpt s₁ s = false := by
  classical
  by_cases hs : s = s₁
  · exact (h hs).elim
  · simp [adversarialOpt, hs]

lemma adversarialOpt_eq_true_of_eq {n : ℕ} (s₁ : BinaryState n) :
    adversarialOpt s₁ s₁ = true := by
  simp [adversarialOpt]

theorem certificate_lower_bound_for_I {n : ℕ} (I : Finset (Fin n))
    (hn : 1 ≤ n) (hI : I.card < n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card < 2 ^ (n - 1)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_state_not_in_endpoints (P := P) hn hP
  obtain ⟨j, hj⟩ := exists_coord_not_mem (I := I) hI
  let s₀ : BinaryState n := flipAt s₁ j
  refine ⟨adversarialOpt s₁, ?_, ?_⟩
  · refine ⟨s₀, s₁, ?_, ?_⟩
    · exact agreeOn_flipAt s₁ I j hj
    · have hs₀ : s₀ ≠ s₁ := flipAt_ne s₁ j
      have htrue : adversarialOpt s₁ s₁ = true := adversarialOpt_eq_true_of_eq s₁
      have hfalse : adversarialOpt s₁ s₀ = false := adversarialOpt_eq_false_of_ne s₁ s₀ hs₀
      simp [htrue, hfalse]
  · intro p hp _
    have hfst : p.1 ≠ s₁ := by
      intro h
      apply hs₁
      have : s₁ ∈ P.image Prod.fst := by
        simpa [h] using (Finset.mem_image_of_mem Prod.fst hp)
      exact (Finset.mem_union.mpr (Or.inl this))
    have hsnd : p.2 ≠ s₁ := by
      intro h
      apply hs₁
      have : s₁ ∈ P.image Prod.snd := by
        simpa [h] using (Finset.mem_image_of_mem Prod.snd hp)
      exact (Finset.mem_union.mpr (Or.inr this))
    have h1 : adversarialOpt s₁ p.1 = false :=
      adversarialOpt_eq_false_of_ne s₁ p.1 hfst
    have h2 : adversarialOpt s₁ p.2 = false :=
      adversarialOpt_eq_false_of_ne s₁ p.2 hsnd
    simp [h1, h2]

theorem certificate_lower_bound_for_I_card {n : ℕ} (I : Finset (Fin n))
    (hn : 1 ≤ n) (hI : I.card < n) (hIpos : 0 < I.card)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card < 2 ^ (n - I.card)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) := by
  have hI1 : 1 ≤ I.card := Nat.succ_le_iff.mpr hIpos
  have hle : n - I.card ≤ n - 1 := Nat.sub_le_sub_left hI1 n
  have hpow : 2 ^ (n - I.card) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hle
  have hP' : P.card < 2 ^ (n - 1) := lt_of_lt_of_le hP hpow
  exact certificate_lower_bound_for_I (I := I) hn hI P hP'

theorem certificate_lower_bound_for_I_empty {n : ℕ}
    (hn : 1 ≤ n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card < 2 ^ (n - 1)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' (∅ : Finset (Fin n)) ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 (∅ : Finset (Fin n)) → Opt p.1 = Opt p.2) := by
  have hI : (∅ : Finset (Fin n)).card < n := by
    simpa using (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hn)
  simpa using (certificate_lower_bound_for_I (I := (∅ : Finset (Fin n))) hn hI P hP)

private lemma succ_cube (n : ℕ) : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by
  ring

private lemma cubic_step_bound (n : ℕ) (hn : 4 ≤ n) :
    3 * n ^ 2 + 3 * n + 1 ≤ n ^ 3 := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 4) hn
  have h4n : 4 * n ≤ n ^ 2 := by
    have h' : 4 * n ≤ n * n := by
      have h := Nat.mul_le_mul_left n hn
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    simpa [Nat.pow_two] using h'
  have h3n : 3 * n + 1 ≤ n ^ 2 := by
    have h6 : 3 * n + 1 ≤ 4 * n := by
      calc
        3 * n + 1 ≤ 3 * n + n := Nat.add_le_add_left hn1 (3 * n)
        _ = 4 * n := by
          calc
            3 * n + n = 3 * n + 1 * n := by simp
            _ = (3 + 1) * n := (Nat.add_mul 3 1 n).symm
            _ = 4 * n := by simp
    exact le_trans h6 h4n
  have hsum : 3 * n ^ 2 + 3 * n + 1 ≤ 3 * n ^ 2 + n ^ 2 :=
    Nat.add_le_add_left h3n (3 * n ^ 2)
  have h4 : 3 * n ^ 2 + n ^ 2 = 4 * n ^ 2 := by
    calc
      3 * n ^ 2 + n ^ 2 = 3 * n ^ 2 + 1 * n ^ 2 := by simp
      _ = (3 + 1) * n ^ 2 := (Nat.add_mul 3 1 (n ^ 2)).symm
      _ = 4 * n ^ 2 := by simp
  have h4' : 4 * n ^ 2 ≤ n ^ 3 := by
    have h := Nat.mul_le_mul_right (n ^ 2) hn
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  exact le_trans (by simpa [h4] using hsum) h4'

theorem cube_lt_pow {n : ℕ} (hn : 12 ≤ n) : n ^ 3 < 2 ^ (n - 1) := by
  refine Nat.le_induction ?base ?step n hn
  · decide
  · intro n hn h
    have hstep : 3 * n ^ 2 + 3 * n + 1 ≤ n ^ 3 := by
      have hn4 : 4 ≤ n := le_trans (by decide : 4 ≤ 12) hn
      exact cubic_step_bound n hn4
    have hsum : (n + 1) ^ 3 = n ^ 3 + (3 * n ^ 2 + 3 * n + 1) := by
      calc
        (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := succ_cube n
        _ = n ^ 3 + (3 * n ^ 2 + 3 * n + 1) := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      cases n with
      | zero => simp at hn
      | succ n =>
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hlt : n ^ 3 + (3 * n ^ 2 + 3 * n + 1) < 2 * 2 ^ (n - 1) := by
      have hle : n ^ 3 + (3 * n ^ 2 + 3 * n + 1) ≤ n ^ 3 + n ^ 3 :=
        Nat.add_le_add_left hstep (n ^ 3)
      have hlt' : n ^ 3 + n ^ 3 < 2 ^ (n - 1) + 2 ^ (n - 1) :=
        Nat.add_lt_add h h
      have hlt'' : n ^ 3 + (3 * n ^ 2 + 3 * n + 1) < 2 ^ (n - 1) + 2 ^ (n - 1) :=
        lt_of_le_of_lt hle hlt'
      simpa [Nat.two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt''
    simpa [hsum, hpow] using hlt

theorem certificate_lower_bound_poly {n : ℕ} (I : Finset (Fin n))
    (hn : 1 ≤ n) (hI : I.card < n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card ≤ n ^ 3) (hpow : n ^ 3 < 2 ^ (n - 1)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) := by
  apply certificate_lower_bound_for_I (I := I) hn hI P
  exact lt_of_le_of_lt hP hpow

theorem certificate_lower_bound_poly_ge {n : ℕ} (I : Finset (Fin n))
    (hn : 12 ≤ n) (hI : I.card < n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card ≤ n ^ 3) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) := by
  have hpow : n ^ 3 < 2 ^ (n - 1) := cube_lt_pow hn
  exact certificate_lower_bound_poly (I := I) (hn := le_trans (by decide : 1 ≤ 12) hn) hI P hP hpow

end DecisionQuotient
