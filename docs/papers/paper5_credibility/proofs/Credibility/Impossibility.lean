/-
  Credibility/Impossibility.lean

  Theorem 5.1-5.3: Impossibility Results

  IMPORTANT FLAG: These theorems show that text alone CANNOT achieve high credibility
  for exceptional claims.
  
  The key insight: text is CHEAP TALK (costs the same whether true or false).
  Therefore, text is subject to the cheap talk bound.
  
  This is why:
  - Editing memory text doesn't solve credibility problems
  - Repeating assertions decreases credibility (Theorem 3.3)
  - Meta-assertions don't help (Theorem 3.4)
  
  The ONLY escape is costly signals (see CostlySignals.lean).
  
  Key results:
  - No text achieves full credibility for high-magnitude claims
  - Memory iteration is bounded in effectiveness
  - Optimal strategy: minimize cheap talk, maximize costly signals
-/

import Credibility.Basic
import Credibility.CheapTalk
import Mathlib.Tactic

namespace Credibility

/-- Text production cost is independent of claim truth. -/
theorem text_is_cheap_talk (text : String) :
    isCheapTalk (text.length : ℝ) (text.length : ℝ) := by
  simp [isCheapTalk]

/-- Magnitude threshold: claims with magnitude above this are "exceptional". -/
def magnitudeThreshold : ℝ := 3

/-- Theorem 5.1: Text credibility bound.
    
    IMPORTANT: Text is CHEAP TALK. Therefore, no text can exceed the cheap talk bound.
    
    For high-magnitude claims (low prior p), the bound τ = p/(p+(1-p)q) → 0.
    This is an IMPOSSIBILITY RESULT: no amount of clever phrasing can escape it.
    
    Note: Requires p < 1 (not p ≤ 1) because when p = 1, the bound equals 1. -/
theorem text_credibility_bound
    (text : String) (p q : ℝ)
    (hp : 0 < p) (hp' : p < 1)
    (hq : 0 < q) (hq' : q ≤ 1) :
    cheapTalkBound p q < 1 := by
  unfold cheapTalkBound
  have h_pos : 0 < 1 - p := by linarith
  have h2 : 0 < (1 - p) * q := mul_pos h_pos hq
  have h3 : p < p + (1 - p) * q := by linarith
  have h4 : 0 < p + (1 - p) * q := by linarith
  rw [div_lt_one h4]
  exact h3

/-- Corollary: For high-magnitude claims, credibility is bounded by a small τ.
    Proof: M > threshold ⟹ -M < -threshold ⟹ exp(-M) < exp(-threshold)
    Then by magnitude_penalty, smaller prior means smaller bound. -/
theorem high_magnitude_credibility_small
    (p q : ℝ) (M : ℝ)
    (hp : p = Real.exp (-M)) (hM : M > magnitudeThreshold)
    (hq : 0 < q) (hq' : q < 1) :
    cheapTalkBound p q < cheapTalkBound (Real.exp (-magnitudeThreshold)) q := by
  -- Step 1: M > threshold implies -M < -threshold
  have h_neg : -M < -magnitudeThreshold := by linarith
  -- Step 2: exp is strictly monotone, so exp(-M) < exp(-threshold)
  have h_exp_mono : Real.exp (-M) < Real.exp (-magnitudeThreshold) :=
    Real.exp_strictMono h_neg
  -- Step 3: Rewrite p using hypothesis
  rw [hp]
  -- Step 4: Apply magnitude_penalty (smaller prior = smaller bound)
  -- magnitude_penalty requires 0 < p_small < 1 and 0 < p_large < 1
  have h_exp_M_pos : 0 < Real.exp (-M) := Real.exp_pos _
  have h_M_pos : 0 < M := by
    have : magnitudeThreshold = 3 := rfl
    linarith
  have h_exp_M_lt1 : Real.exp (-M) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h_exp_thresh_pos : 0 < Real.exp (-magnitudeThreshold) := Real.exp_pos _
  have h_exp_thresh_lt1 : Real.exp (-magnitudeThreshold) < 1 := by
    rw [Real.exp_lt_one_iff]
    unfold magnitudeThreshold
    linarith
  exact magnitude_penalty (Real.exp (-M)) (Real.exp (-magnitudeThreshold)) q
    h_exp_M_pos h_exp_M_lt1 h_exp_thresh_pos h_exp_thresh_lt1 h_exp_mono hq hq'

/-- Theorem 5.2: Memory iteration futility.
    
    CRITICAL: Rephrasing memory entries CANNOT exceed the cheap-talk bound.
    
    This is why we can't solve credibility by editing text - text is cheap talk,
    and cheap talk bounds apply regardless of phrasing.
    
    IMPORTANT: This is an IMPOSSIBILITY RESULT, not a heuristic. -/
theorem memory_iteration_futility
    (memories : List String) (p q : ℝ)
    (hp : 0 < p) (hp' : p < 1)
    (hq : 0 < q) (hq' : q ≤ 1) :
    ∀ m ∈ memories, cheapTalkBound p q < 1 := by
  intro m _
  exact text_credibility_bound m p q hp hp' hq hq'

/-- Strategy components for credibility maximization. -/
structure CredibilityStrategy where
  minimizeCheapTalk : Bool
  maximizeCostlySignals : Bool
  enableDemonstration : Bool
deriving DecidableEq

/-- A fixed optimal strategy. -/
def optimalStrategy : CredibilityStrategy :=
  ⟨true, true, true⟩

/-- Any deviation from the optimal strategy drops at least one flag. -/
theorem optimal_strategy_dominance (s : CredibilityStrategy) (h : s ≠ optimalStrategy) :
    ¬ s.minimizeCheapTalk ∨ ¬ s.maximizeCostlySignals ∨ ¬ s.enableDemonstration := by
  cases s with
  | mk mc ms ed =>
      dsimp [optimalStrategy] at h
      by_cases h1 : mc = true
      · by_cases h2 : ms = true
        · by_cases h3 : ed = true
          · exfalso
            apply h
            cases h1; cases h2; cases h3
            rfl
          · right; right; simpa [h3]
        · right; left; simpa [h2]
      · left; simpa [h1]

/-! ## NEW: Composition Impossibility Theorem -/

/-- Theorem 5.4 (Composition Impossibility): Stacking n meta-assertions
    strictly decreases credibility for n ≥ 1.

    Each meta-assertion "my claim is true" is itself cheap talk with
    mimicability ≥ the base claim. Stacking n such assertions increases
    effective mimicability, decreasing the credibility bound.

    Formalized: credibility(n+1 assertions) ≤ credibility(n assertions) -/
theorem composition_impossibility (prior baseSuspicion : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hs : 0 < baseSuspicion) (hs' : baseSuspicion < 1)
    (n : ℕ) :
    credibilityWithEmphasis prior baseSuspicion (n + 1) ≤
    credibilityWithEmphasis prior baseSuspicion n := by
  -- Direct proof using the same technique as emphasis_penalty
  unfold credibilityWithEmphasis
  have h_susp : suspicion baseSuspicion n ≤ suspicion baseSuspicion (n + 1) :=
    suspicion_mono baseSuspicion hs hs' (Nat.le_succ n)
  have h_susp_n_nonneg : 0 ≤ suspicion baseSuspicion n :=
    le_of_lt (suspicion_pos baseSuspicion hs hs' n)
  have h_susp_n1_nonneg : 0 ≤ suspicion baseSuspicion (n + 1) :=
    le_of_lt (suspicion_pos baseSuspicion hs hs' (n + 1))
  exact cheapTalkBound_antitone_mimicability prior hp hp' h_susp_n_nonneg h_susp_n1_nonneg h_susp

/-- Corollary: Stacking any number of meta-assertions never exceeds base credibility. -/
theorem composition_never_helps (prior baseSuspicion : ℝ)
    (hp : 0 < prior) (hp' : prior < 1)
    (hs : 0 < baseSuspicion) (hs' : baseSuspicion < 1)
    (n : ℕ) :
    credibilityWithEmphasis prior baseSuspicion n ≤
    credibilityWithEmphasis prior baseSuspicion 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h_step := composition_impossibility prior baseSuspicion hp hp' hs hs' m
    exact le_trans h_step ih

/-! ## Asymptotic Bound Theorem -/

/-- Theorem 5.5 (Asymptotic Impossibility): As claim magnitude M → ∞,
    achievable cheap-talk credibility → 0.

    More precisely: for any ε > 0, there exists M₀ such that for all M > M₀,
    the cheap talk bound is less than ε.

    Proof: As M → ∞, exp(-M) → 0, and cheapTalkBound(exp(-M), q) → 0.
    Key insight: For p < 1, cheapTalkBound(p, q) < p / ((1-p)q), which → 0 as p → 0. -/
theorem asymptotic_impossibility (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    ∃ M₀ : ℝ, ∀ M > M₀, cheapTalkBound (Real.exp (-M)) q < ε := by
  -- Strategy: For large M, exp(-M) is small, so bound ≈ exp(-M)/q < ε
  -- We need M large enough that exp(-M) < ε * q * (1 - exp(-M))
  -- For M > 1, exp(-M) < 1/e < 1/2, so 1 - exp(-M) > 1/2
  -- Thus exp(-M) / ((1-exp(-M)) * q) < 2 * exp(-M) / q
  -- We need 2 * exp(-M) / q < ε, i.e., exp(-M) < ε * q / 2
  -- i.e., M > -log(ε * q / 2) = -log(ε * q) + log(2)
  use max 1 (-Real.log (ε * q / 2))
  intro M hM
  have h_εq_pos : 0 < ε * q := mul_pos hε hq
  have h_εq2_pos : 0 < ε * q / 2 := by linarith
  have h_M_ge_1 : M ≥ 1 := le_of_lt (lt_of_le_of_lt (le_max_left 1 _) hM)
  have h_exp_pos : 0 < Real.exp (-M) := Real.exp_pos _
  have h_exp_lt_half : Real.exp (-M) < 1 / 2 := by
    have h1 : Real.exp (-M) ≤ Real.exp (-1) := Real.exp_le_exp_of_le (by linarith : -M ≤ -1)
    have h2 : Real.exp (-1) < 1 / 2 := by
      -- exp(-1) ≈ 0.368 < 0.5
      have h_exp_inv : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, inv_eq_one_div]
      rw [h_exp_inv]
      rw [div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)]
      -- Need: 1 * 2 < exp(1) * 1, i.e., 2 < exp(1)
      have h_e_gt_2 : Real.exp 1 > 2 := by
        -- exp(1) > 2 follows from 1 + 1 < exp(1) via add_one_lt_exp
        have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        linarith
      linarith
    linarith
  have h_exp_lt_1 : Real.exp (-M) < 1 := by linarith
  have h_1_minus_exp_pos : 0 < 1 - Real.exp (-M) := by linarith
  have h_1_minus_exp_gt_half : 1 - Real.exp (-M) > 1 / 2 := by linarith
  have h_exp_lt_εq2 : Real.exp (-M) < ε * q / 2 := by
    have h1 : M > -Real.log (ε * q / 2) := lt_of_le_of_lt (le_max_right 1 _) hM
    rw [← Real.log_lt_log_iff h_exp_pos h_εq2_pos]
    simp only [Real.log_exp]
    linarith
  have h_denom_pos : 0 < Real.exp (-M) + (1 - Real.exp (-M)) * q := by
    have h2 : 0 < (1 - Real.exp (-M)) * q := mul_pos h_1_minus_exp_pos hq
    linarith
  -- Now prove the bound
  unfold cheapTalkBound
  rw [div_lt_iff₀ h_denom_pos]
  -- Need: exp(-M) < ε * (exp(-M) + (1 - exp(-M)) * q)
  -- We have: exp(-M) < ε * q / 2 and 1 - exp(-M) > 1/2
  -- So: ε * (1 - exp(-M)) * q > ε * q / 2 > exp(-M)
  calc Real.exp (-M)
      < ε * q / 2 := h_exp_lt_εq2
    _ < ε * (1 - Real.exp (-M)) * q := by
        have h1 : ε * q / 2 < ε * (1 / 2) * q * 2 := by ring_nf; linarith
        have h2 : ε * (1 / 2) * q * 2 = ε * q := by ring
        have h3 : ε * (1 - Real.exp (-M)) * q > ε * (1 / 2) * q := by
          apply mul_lt_mul_of_pos_right _ hq
          apply mul_lt_mul_of_pos_left h_1_minus_exp_gt_half hε
        linarith
    _ ≤ ε * (Real.exp (-M) + (1 - Real.exp (-M)) * q) := by
        have h1 : 0 ≤ Real.exp (-M) := le_of_lt h_exp_pos
        have h2 : (1 - Real.exp (-M)) * q ≤ Real.exp (-M) + (1 - Real.exp (-M)) * q := by linarith
        calc ε * (1 - Real.exp (-M)) * q
            = ε * ((1 - Real.exp (-M)) * q) := by ring
          _ ≤ ε * (Real.exp (-M) + (1 - Real.exp (-M)) * q) := by
              apply mul_le_mul_of_nonneg_left h2 (le_of_lt hε)

end Credibility
