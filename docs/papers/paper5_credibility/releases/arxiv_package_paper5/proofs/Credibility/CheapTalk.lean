/-
  Credibility/CheapTalk.lean

  Proofs for the cheap-talk section (Theorems 3.1-3.4).

  IMPORTANT FLAG: These theorems ONLY apply to CHEAP TALK signals.
  A signal is cheap talk iff isCheapTalk(costIfTrue, costIfFalse) holds.
  
  Key result: Cheap talk credibility is bounded by p/(p + (1-p)q)
  where p = prior, q = mimicability (probability deceptive sender mimics signal).
  
  To escape these bounds, see CostlySignals.lean - costly signals can achieve
  arbitrarily high credibility because faking is expensive.
-/

import Credibility.Basic
import Mathlib.Tactic

namespace Credibility

/-! ## Theorem 3.1: The Cheap Talk Bound -/

/-!
  CRITICAL: This is the main theorem of Paper 5.
  
  For CHEAP TALK signals (cost independent of truth):
  P(C=1 | S) ≤ p / (p + (1-p)q)
  
  where:
  - p = prior probability of true claim
  - q = mimicability (probability deceiver can fake the signal)
  
  IMPORTANT: This bound is TIGHT - equality holds when α=1, β=q.
  But it ONLY applies to cheap talk. Costly signals escape this bound.
-/

/-- The cheap talk bound is nonnegative when prior and mimicability are valid. -/
lemma cheapTalkBound_nonneg (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hq' : q ≤ 1) (hp' : p ≤ 1) :
    0 ≤ cheapTalkBound p q := by
  unfold cheapTalkBound
  apply div_nonneg hp
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ (1 - p) * q := mul_nonneg h1 hq
  linarith

/-- The cheap talk bound is strictly positive when p>0 and q≥0. -/
lemma cheapTalkBound_pos (p q : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1) (hq : 0 ≤ q) :
    0 < cheapTalkBound p q := by
  unfold cheapTalkBound
  have h_denom_pos : 0 < p + (1 - p) * q := by
    have h1 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith [hp']) hq
    linarith
  exact div_pos hp h_denom_pos

/-- If mimicability is 0 and p>0, cheap talk credibility is 1. -/
lemma cheapTalkBound_q_zero (p : ℝ) (hp : 0 < p) :
    cheapTalkBound p 0 = 1 := by
  have h : (p : ℝ) ≠ 0 := ne_of_gt hp
  simp [cheapTalkBound, h]

/-- If mimicability is 1, cheap talk credibility reduces to the prior. -/
lemma cheapTalkBound_q_one (p : ℝ) : cheapTalkBound p 1 = p := by
  simp [cheapTalkBound]

/-- The cheap talk bound is at most 1 when mimicability is positive. -/
lemma cheapTalkBound_le_one (p q : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 < q) :
    cheapTalkBound p q ≤ 1 := by
  unfold cheapTalkBound
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ (1 - p) * q := mul_nonneg h1 (le_of_lt hq)
  have h_denom_pos : 0 < p + (1 - p) * q := by
    have := mul_pos (by linarith : 0 < 1 - p + p) hq
    nlinarith [sq_nonneg p, sq_nonneg q]
  rw [div_le_one h_denom_pos]
  linarith

/-- The cheap talk bound is strictly less than 1 when 0<p<1 and q>0. -/
lemma cheapTalkBound_lt_one (p q : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) :
    cheapTalkBound p q < 1 := by
  unfold cheapTalkBound
  have hdenom_pos : 0 < p + (1 - p) * q := by
    have h1 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith) (le_of_lt hq)
    linarith
  have hnum_lt : p < p + (1 - p) * q := by
    have hprod_pos : 0 < (1 - p) * q := mul_pos (by linarith) hq
    linarith
  exact (div_lt_one hdenom_pos).2 hnum_lt

/-- Cheap talk credibility is bounded (Theorem 3.1).
    P(C=1 | S) ≤ p / (p + (1-p)q) with equality when α=1, β=q. -/
theorem cheap_talk_bound (p q : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1)
    (hq : 0 < q) (hq' : q ≤ 1) :
    cheapTalkCredibility p q ≤ cheapTalkBound p q := by
  have hdenom : p + (1 - p) * q ≠ 0 := by
    have h1 : 0 ≤ 1 - p := by linarith
    have h2 : 0 < (1 - p) * q ∨ p > 0 := Or.inr hp
    nlinarith
  rw [cheapTalkCredibility_eq_bound p q hdenom]

/-- The bound is tight: equality holds when β = q exactly. -/
theorem cheap_talk_bound_tight (p q : ℝ)
    (hdenom : p + (1 - p) * q ≠ 0) :
    cheapTalkCredibility p q = cheapTalkBound p q :=
  cheapTalkCredibility_eq_bound p q hdenom

/-! ## Theorem 3.2: Magnitude Penalty -/

/-- Helper: The denominator p + (1-p)q is positive when p ≥ 0 and q > 0 and q ≤ 1. -/
lemma cheapTalkBound_denom_pos (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    0 < p + (1 - p) * q := by
  -- p + (1-p)q = p(1-q) + q
  have eq : p + (1 - p) * q = p * (1 - q) + q := by ring
  rw [eq]
  have h1 : 0 ≤ p * (1 - q) := mul_nonneg hp (by linarith)
  linarith

/-- The cheap talk bound is strictly increasing in p (for fixed q ∈ (0,1)) on the interval (0,1).
    Proof: f(p) = p/(p + (1-p)q) = p/(p(1-q) + q)
    f(p₂) - f(p₁) = (p₂ - p₁) · q / [(p₁(1-q)+q)(p₂(1-q)+q)] > 0 when p₂ > p₁ -/
lemma cheapTalkBound_strictMono_prior (q : ℝ) (hq : 0 < q) (hq' : q < 1) :
    StrictMonoOn (fun p => cheapTalkBound p q) (Set.Ioo 0 1) := by
  intro p₁ ⟨hp1_pos, hp1_lt1⟩ p₂ ⟨hp2_pos, hp2_lt1⟩ h12
  simp only [cheapTalkBound]
  -- p + (1-p)q = p(1-q) + q
  have eq1 : p₁ + (1 - p₁) * q = p₁ * (1 - q) + q := by ring
  have eq2 : p₂ + (1 - p₂) * q = p₂ * (1 - q) + q := by ring
  have h1q : 0 < 1 - q := by linarith
  -- With 0 < p < 1 and 0 < q < 1, the denominator p(1-q) + q > 0
  have d1_pos : 0 < p₁ + (1 - p₁) * q := by
    rw [eq1]
    have h1 : 0 < p₁ * (1 - q) := mul_pos hp1_pos h1q
    linarith
  have d2_pos : 0 < p₂ + (1 - p₂) * q := by
    rw [eq2]
    have h1 : 0 < p₂ * (1 - q) := mul_pos hp2_pos h1q
    linarith
  rw [div_lt_div_iff₀ d1_pos d2_pos]
  -- Need: p₁ · (p₂ + (1-p₂)q) < p₂ · (p₁ + (1-p₁)q)
  ring_nf
  nlinarith

/-- Theorem 3.2: Higher magnitude (smaller prior) yields lower credibility. -/
theorem magnitude_penalty (p_small p_large q : ℝ)
    (hp_small_pos : 0 < p_small) (hp_small_lt1 : p_small < 1)
    (hp_large_pos : 0 < p_large) (hp_large_lt1 : p_large < 1)
    (h : p_small < p_large) (hq : 0 < q) (hq' : q < 1) :
    cheapTalkBound p_small q < cheapTalkBound p_large q := by
  have h1 : p_small ∈ Set.Ioo 0 1 := ⟨hp_small_pos, hp_small_lt1⟩
  have h2 : p_large ∈ Set.Ioo 0 1 := ⟨hp_large_pos, hp_large_lt1⟩
  exact cheapTalkBound_strictMono_prior q hq hq' h1 h2 h

/-! ## Theorem 3.3: Emphasis Penalty -/

/-!
  CRITICAL: Adding MORE assertions DECREASES credibility past a threshold.
  
  This is counterintuitive but follows from the suspicion function:
  - Honest agents don't need to over-assert
  - Deceptive agents over-assert to compensate
  - Therefore, more assertions = higher suspicion = lower credibility
  
  This is why "Trust me" backfires - excessive emphasis signals desperation.
-/

/-- Suspicion increases with number of assertions. -/
noncomputable def suspicion (baseSuspicion : ℝ) (n : ℕ) : ℝ :=
  1 - (1 - baseSuspicion) ^ (n + 1)

/-- For 0 < r < 1, r^m ≤ r^n when n ≤ m. -/
lemma pow_le_pow_of_lt_one_nat {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {n m : ℕ} (h : n ≤ m) :
    r ^ m ≤ r ^ n := by
  have hr_nonneg : 0 ≤ r := le_of_lt hr0
  have hr_le_one : r ≤ 1 := le_of_lt hr1
  exact pow_le_pow_of_le_one hr_nonneg hr_le_one h

/-- Suspicion is monotonically increasing in n.
    Proof: suspicion(n) = 1 - (1-s)^(n+1), and (1-s)^k decreases as k increases
    when 0 < 1-s < 1, so 1 - (1-s)^k increases. -/
lemma suspicion_mono (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    Monotone (suspicion s) := by
  intro n m h
  unfold suspicion
  have h1 : 0 < 1 - s := by linarith
  have h2 : 1 - s < 1 := by linarith
  -- (1-s)^(m+1) ≤ (1-s)^(n+1) since 0 < 1-s < 1 and n ≤ m implies n+1 ≤ m+1
  have h3 : n + 1 ≤ m + 1 := Nat.succ_le_succ h
  have h4 : (1 - s) ^ (m + 1) ≤ (1 - s) ^ (n + 1) := pow_le_pow_of_lt_one_nat h1 h2 h3
  linarith

/-- Suspicion is positive for positive base suspicion. -/
lemma suspicion_pos (s : ℝ) (hs : 0 < s) (hs' : s < 1) (n : ℕ) : 0 < suspicion s n := by
  unfold suspicion
  have h_base_pos : 0 < 1 - s := by linarith
  have h_base_lt_one : 1 - s < 1 := by linarith
  -- (1-s)^(n+1) < 1 when 0 < 1-s < 1 and n+1 ≥ 1
  have h1 : (1 - s) ^ (n + 1) < 1 := by
    have h_le_one : (1 - s) ^ (n + 1) ≤ (1 - s) ^ 1 := by
      apply pow_le_pow_of_le_one (le_of_lt h_base_pos) (le_of_lt h_base_lt_one)
      omega
    simp at h_le_one
    linarith
  linarith

/-- Suspicion is nonnegative for positive base suspicion. -/
lemma suspicion_nonneg (s : ℝ) (hs : 0 < s) (hs' : s < 1) (n : ℕ) : 0 ≤ suspicion s n :=
  le_of_lt (suspicion_pos s hs hs' n)

/-- Credibility with n emphasis signals. -/
noncomputable def credibilityWithEmphasis (prior baseSuspicion : ℝ) (n : ℕ) : ℝ :=
  cheapTalkBound prior (suspicion baseSuspicion n)

/-- The cheap talk bound is antitone (decreasing) in q for fixed p ∈ (0,1) on nonnegative q.
    Proof: f(q) = p/(p + (1-p)q). As q increases, denominator increases, so f decreases. -/
lemma cheapTalkBound_antitone_mimicability (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    AntitoneOn (fun q => cheapTalkBound p q) (Set.Ici 0) := by
  intro q₁ hq1 q₂ hq2 h12
  simp only [Set.mem_Ici] at hq1 hq2
  simp only [cheapTalkBound]
  have h1_minus_p : 0 < 1 - p := by linarith
  -- Need: p/(p + (1-p)q₂) ≤ p/(p + (1-p)q₁)
  -- Since 1-p > 0 and q₂ ≥ q₁, we have (1-p)q₂ ≥ (1-p)q₁
  -- So denom₂ ≥ denom₁, and since p > 0, p/denom₂ ≤ p/denom₁
  have h_q_mono : (1 - p) * q₁ ≤ (1 - p) * q₂ := by
    apply mul_le_mul_of_nonneg_left h12
    linarith
  have h_denom_mono : p + (1 - p) * q₁ ≤ p + (1 - p) * q₂ := by linarith
  -- d1 > 0 since p > 0 and (1-p)*q₁ ≥ 0
  have d1_pos : 0 < p + (1 - p) * q₁ := by
    have h1 : 0 ≤ (1 - p) * q₁ := mul_nonneg (le_of_lt h1_minus_p) hq1
    linarith
  have d2_pos : 0 < p + (1 - p) * q₂ := by
    have h1 : 0 ≤ (1 - p) * q₂ := mul_nonneg (le_of_lt h1_minus_p) hq2
    linarith
  -- For 0 < p and d1 ≤ d2 with d1, d2 > 0, p/d2 ≤ p/d1
  rw [div_le_div_iff₀ d2_pos d1_pos]
  -- Need: p * (p + (1-p)*q₁) ≤ p * (p + (1-p)*q₂)
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  exact mul_le_mul_of_nonneg_left h_denom_mono hp_nonneg

/-- The cheap talk bound is strictly decreasing in q on (0,1) for fixed p ∈ (0,1). -/
lemma cheapTalkBound_strict_antitone_mimicability (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    StrictAntiOn (fun q => cheapTalkBound p q) (Set.Icc 0 1) := by
  intro q1 hq1 q2 hq2 hlt
  -- unpack bounds
  have hq1_nonneg : 0 ≤ q1 := hq1.left
  have hq2_nonneg : 0 ≤ q2 := hq2.left
  have hq1_le_one : q1 ≤ 1 := hq1.right
  have hq2_le_one : q2 ≤ 1 := hq2.right
  have hq1_lt_q2 : q1 < q2 := hlt
  have h1_minus_p : 0 < 1 - p := by linarith
  -- denominators
  have d1_pos : 0 < p + (1 - p) * q1 := by
    have h : 0 ≤ (1 - p) * q1 := mul_nonneg (le_of_lt h1_minus_p) hq1_nonneg
    linarith
  have d2_pos : 0 < p + (1 - p) * q2 := by
    have h : 0 ≤ (1 - p) * q2 := mul_nonneg (le_of_lt h1_minus_p) hq2_nonneg
    linarith
  have d_lt : p + (1 - p) * q1 < p + (1 - p) * q2 := by
    have h : 0 < (1 - p) * (q2 - q1) := by
      have hfac : 0 < 1 - p := h1_minus_p
      have hdiff : q2 - q1 > 0 := sub_pos.mpr hq1_lt_q2
      nlinarith
    nlinarith
  -- with equal numerators p > 0 and larger denominator, the fraction decreases
  have hp_pos : 0 < p := hp
  have hfrac : p / (p + (1 - p) * q2) < p / (p + (1 - p) * q1) := by
    have h_inv : 1 / (p + (1 - p) * q2) < 1 / (p + (1 - p) * q1) :=
      one_div_lt_one_div_of_lt d1_pos d_lt
    have h_mul := mul_lt_mul_of_pos_left h_inv hp_pos
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using h_mul
  simpa [cheapTalkBound] using hfrac

/-- Theorem 3.3: Adding emphasis eventually decreases credibility.
    As n increases, suspicion increases, so credibility decreases. -/
theorem emphasis_penalty (prior baseSuspicion : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hs : 0 < baseSuspicion) (hs' : baseSuspicion < 1) :
    ∃ k : ℕ, ∀ n ≥ k,
      credibilityWithEmphasis prior baseSuspicion (n + 1) ≤
      credibilityWithEmphasis prior baseSuspicion n := by
  use 0
  intro n _
  unfold credibilityWithEmphasis
  -- suspicion is monotone, so suspicion(n+1) ≥ suspicion(n)
  have h_susp : suspicion baseSuspicion n ≤ suspicion baseSuspicion (n + 1) :=
    suspicion_mono baseSuspicion hs hs' (Nat.le_succ n)
  -- suspicion values are nonnegative
  have h_susp_n_nonneg : 0 ≤ suspicion baseSuspicion n := le_of_lt (suspicion_pos baseSuspicion hs hs' n)
  have h_susp_n1_nonneg : 0 ≤ suspicion baseSuspicion (n + 1) := le_of_lt (suspicion_pos baseSuspicion hs hs' (n + 1))
  -- cheapTalkBound is antitone in q on nonnegative q, so larger q means smaller bound
  exact cheapTalkBound_antitone_mimicability prior hp hp' h_susp_n_nonneg h_susp_n1_nonneg h_susp

/-! ## Theorem 3.4: Meta-Assertion Trap -/

/-!
  CRITICAL: Meta-assertions about credibility are themselves cheap talk.
  
  "My claim is credible" has the same cost regardless of whether it's true.
  Therefore, meta-assertions cannot escape the cheap talk bound.
  
  IMPORTANT: This is recursive - asserting that your assertion is credible
  is itself a cheap talk assertion that is bounded.
  
  This is why you can't solve credibility problems by adding more assertions.
  See Impossibility.lean for the formal proof.
-/

/-- Theorem 3.4 (strengthened): Meta-assertions cannot exceed base credibility.
    
    CRITICAL: A meta-assertion about claim c has mimicability at least as high
    as the base assertion. Therefore, the credibility with meta-assertion
    cannot exceed the credibility without it.
    
    Formally: if q_meta ≥ q_base (meta is at least as mimickable), 
    then C(c, a ∪ m) ≤ C(c, a) -/
theorem meta_assertion_trap (prior q_base q_meta : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hq_base : 0 ≤ q_base) (hq_meta : 0 ≤ q_meta)
    (h_q_ge : q_meta ≥ q_base) :
    cheapTalkBound prior q_meta ≤ cheapTalkBound prior q_base :=
  cheapTalkBound_antitone_mimicability prior hp hp' hq_base hq_meta h_q_ge

/-- Corollary: Meta-assertions strictly decrease credibility when mimicability increases.
    If meta-assertion is more mimickable than base assertion, credibility drops. -/
theorem meta_assertion_decreases (prior q_base q_meta : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hq_base : 0 < q_base) (hq_base' : q_base ≤ 1)
    (hq_meta : 0 < q_meta) (hq_meta' : q_meta ≤ 1)
    (h_q_strict : q_meta > q_base) :
    cheapTalkBound prior q_meta < cheapTalkBound prior q_base :=
  cheapTalkBound_strict_antitone_mimicability prior hp hp' 
    ⟨hq_base, hq_base'⟩ ⟨hq_meta, hq_meta'⟩ h_q_strict

/-- Meta-assertion boost is nonpositive: C(c, a ∪ m) - C(c, a) ≤ 0 -/
theorem meta_assertion_boost_nonpositive (prior q_base q_meta : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hq_base : 0 ≤ q_base) (hq_meta : 0 ≤ q_meta)
    (h_q_ge : q_meta ≥ q_base) :
    cheapTalkBound prior q_meta - cheapTalkBound prior q_base ≤ 0 :=
  sub_nonpos.mpr (meta_assertion_trap prior q_base q_meta hp hp' hq_base hq_meta h_q_ge)

/-- Stronger form: meta-assertions are subject to the same bound recursively.
    Higher mimicability q means lower credibility. -/
theorem meta_assertion_bounded (prior q_base q_meta : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hq_base_nonneg : 0 ≤ q_base) (hq_meta_nonneg : 0 ≤ q_meta)
    (hq_meta : q_meta ≥ q_base) :
    cheapTalkBound prior q_meta ≤ cheapTalkBound prior q_base :=
  meta_assertion_trap prior q_base q_meta hp hp' hq_base_nonneg hq_meta_nonneg hq_meta

end Credibility
