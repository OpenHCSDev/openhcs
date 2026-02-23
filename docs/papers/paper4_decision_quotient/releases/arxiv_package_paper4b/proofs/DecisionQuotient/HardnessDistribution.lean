/-
  Paper 4: Decision Quotient

  HardnessDistribution.lean - Hardness distribution grounded in Papers 2-4

  GROUNDING:
  - Hardness := DOF (Paper 2) - the minimal independent encoding count
  - Error sites := DOF (Paper 2) - where inconsistencies can occur
  - Centralization := moving DOF to shared component
  - Conservation := information-theoretic: you can't encode less than the fact requires
  - Leverage connection := capabilities / DOF (Paper 3)

  Key insight: "Hardness" is not abstract - it IS the DOF count.
  A fact requires k independent bits to encode. You either:
  1. Pay k once (central: type system encodes it)
  2. Pay k × n times (distributed: each site re-encodes it)

  LaTeX reference: Section 6.4 (Hardness Distribution: Right Place vs Wrong Place)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace DecisionQuotient.HardnessDistribution

/-! ## Grounding in Paper 2: DOF as Hardness

From Paper 2 (Dof.lean):
- An Encoding is a (fact, location, value) tuple
- DOF = |minimalIndependentCore(encodings)|
- DOF is the count of encodings not derivable from others

Hardness IS DOF: the minimum number of independent specifications required.
-/

/-- A specification problem: something that must be encoded at use sites.
    intrinsicDOF is the minimum independent encodings required (from Paper 2). -/
structure SpecificationProblem where
  /-- Minimum independent encodings required (Paper 2: size of minimal independent core) -/
  intrinsicDOF : ℕ
  /-- Must specify at least one thing -/
  dof_pos : intrinsicDOF > 0

/-- A solution architecture partitions DOF between central and per-site.

    Central: encoded once in shared component (type system, library, framework)
    Distributed: encoded at each use site

    Conservation: central + distributed ≥ intrinsic (you can't compress below DOF) -/
structure SolutionArchitecture (P : SpecificationProblem) where
  /-- DOF handled centrally (paid once) -/
  centralDOF : ℕ
  /-- DOF handled per-site (paid n times) -/
  distributedDOF : ℕ
  /-- Conservation: must cover the intrinsic DOF -/
  conservation : centralDOF + distributedDOF ≥ P.intrinsicDOF

/-! ## Error Sites = DOF (Paper 2 Connection)

From Paper 2: each independent encoding is a site where inconsistency can occur.
Error sites for a solution = 1 (central component) + n × distributedDOF (per-site encodings).
-/

/-- Total error sites: central component (1 if any central DOF) + per-site encodings -/
def errorSites (S : SolutionArchitecture P) (n : ℕ) : ℕ :=
  (if S.centralDOF > 0 then 1 else 0) + n * S.distributedDOF

/-- Total specification effort: DOF paid once centrally + DOF paid n times distributed -/
def totalDOF (S : SolutionArchitecture P) (n : ℕ) : ℕ :=
  S.centralDOF + n * S.distributedDOF

def hardnessEfficiency (S : SolutionArchitecture P) (n : ℕ) : ℚ :=
  if _ : totalDOF S n = 0 then 0 else (S.centralDOF : ℚ) / (totalDOF S n : ℚ)

/-- For positive total DOF, hardness efficiency is exactly the central share ratio. -/
theorem hardnessEfficiency_eq_central_share (S : SolutionArchitecture P) (n : ℕ)
    (hpos : totalDOF S n > 0) :
    hardnessEfficiency S n = (S.centralDOF : ℚ) / (totalDOF S n : ℚ) := by
  unfold hardnessEfficiency
  simp [Nat.ne_of_gt hpos]

/-! ## Baseline Conservation Across Use Sites -/

/-- For any nonzero use-site count, total realized DOF cannot drop below intrinsic DOF. -/
theorem totalDOF_ge_intrinsic (S : SolutionArchitecture P) (n : ℕ) (hn : n ≥ 1) :
    totalDOF S n ≥ P.intrinsicDOF := by
  have hdist : S.distributedDOF ≤ n * S.distributedDOF := by
    calc
      S.distributedDOF = 1 * S.distributedDOF := by simp
      _ ≤ n * S.distributedDOF := Nat.mul_le_mul_right _ hn
  have hcover : S.centralDOF + S.distributedDOF ≤ S.centralDOF + n * S.distributedDOF :=
    Nat.add_le_add_left hdist S.centralDOF
  exact le_trans S.conservation hcover

/-! ## Hardness Conservation (Information-Theoretic)

You cannot encode k independent facts with fewer than k independent specifications.
This is not an axiom - it follows from the definition of independence in Paper 2.
-/

/-- Theorem: Conservation is a structure invariant -/
theorem dof_conservation (P : SpecificationProblem) (S : SolutionArchitecture P) :
    S.centralDOF + S.distributedDOF ≥ P.intrinsicDOF :=
  S.conservation

/-! ## Centralization Dominance

Core theorem: for n > 1, centralizing DOF reduces both total effort and error sites.
-/

/-- Distributed DOF multiplies with use sites -/
theorem distributed_multiplies (S : SolutionArchitecture P) (n₁ n₂ : ℕ)
    (hn : n₁ < n₂) (hd : S.distributedDOF > 0) :
    totalDOF S n₁ < totalDOF S n₂ := by
  unfold totalDOF
  have h : n₁ * S.distributedDOF < n₂ * S.distributedDOF := Nat.mul_lt_mul_of_pos_right hn hd
  omega

/-- Lower distributed DOF means lower total DOF for any n ≥ 1 -/
theorem less_distributed_less_total (P : SpecificationProblem)
    (S₁ S₂ : SolutionArchitecture P) (n : ℕ) (hn : n ≥ 1)
    (hc : S₁.centralDOF = S₂.centralDOF)
    (hd : S₁.distributedDOF < S₂.distributedDOF) :
    totalDOF S₁ n < totalDOF S₂ n := by
  unfold totalDOF
  have h : n * S₁.distributedDOF < n * S₂.distributedDOF := by
    apply Nat.mul_lt_mul_of_pos_left hd
    omega
  omega

/-- Zero distributed DOF means constant total DOF (independent of n) -/
theorem centralized_constant (S : SolutionArchitecture P) (n₁ n₂ : ℕ)
    (h : S.distributedDOF = 0) :
    totalDOF S n₁ = totalDOF S n₂ := by
  unfold totalDOF
  simp [h]

/-- Zero distributed DOF means minimal error sites (just 1 for central component) -/
theorem centralized_minimal_errors (S : SolutionArchitecture P) (n : ℕ)
    (hc : S.centralDOF > 0) (hd : S.distributedDOF = 0) :
    errorSites S n = 1 := by
  unfold errorSites
  simp [hc, hd]

/-- Positive distributed DOF means error sites grow with n -/
theorem distributed_errors_grow (S : SolutionArchitecture P) (n : ℕ) (_hn : n > 0)
    (hd : S.distributedDOF > 0) :
    errorSites S n ≥ n := by
  unfold errorSites
  have h : n * S.distributedDOF ≥ n := Nat.le_mul_of_pos_right n hd
  omega

/-! ## Right vs Wrong Hardness -/

/-- Hardness is in the right place if distributed DOF is zero -/
def isRightHardness (S : SolutionArchitecture P) : Prop :=
  S.distributedDOF = 0

/-- Hardness is in the wrong place if distributed DOF is positive -/
def isWrongHardness (S : SolutionArchitecture P) : Prop :=
  S.distributedDOF > 0

/-- Right hardness dominates wrong hardness for large n -/
theorem right_dominates_wrong (P : SpecificationProblem)
    (S_right S_wrong : SolutionArchitecture P)
    (hr : isRightHardness S_right)
    (hw : isWrongHardness S_wrong)
    (n : ℕ) (hn : n > S_right.centralDOF) :
    totalDOF S_right n < totalDOF S_wrong n := by
  unfold isRightHardness at hr
  unfold isWrongHardness at hw
  unfold totalDOF
  simp [hr]
  -- S_right.centralDOF < n * S_wrong.distributedDOF + S_wrong.centralDOF
  have h1 : n * S_wrong.distributedDOF ≥ n := Nat.le_mul_of_pos_right n hw
  omega

/-- Right-hardness architectures have strictly fewer error sites than wrong-hardness
    architectures once there is more than one use site. -/
theorem right_fewer_error_sites (P : SpecificationProblem)
    (S_right S_wrong : SolutionArchitecture P)
    (hr : isRightHardness S_right) (hcentral : S_right.centralDOF > 0)
    (hw : isWrongHardness S_wrong) (n : ℕ) (hn : n > 1) :
    errorSites S_right n < errorSites S_wrong n := by
  have hright : errorSites S_right n = 1 :=
    centralized_minimal_errors S_right n hcentral hr
  have hn_pos : n > 0 := lt_trans (by decide : (0 : ℕ) < 1) hn
  have hwrong_ge_n : errorSites S_wrong n ≥ n :=
    distributed_errors_grow S_wrong n hn_pos hw
  have hone_lt_err : 1 < errorSites S_wrong n := lt_of_lt_of_le hn hwrong_ge_n
  rw [hright]
  exact hone_lt_err

/-- Moving one unit of work from distributed to central saves exactly n-1 total units. -/
theorem centralization_step_saves_n_minus_one (central distributed n : ℕ)
    (hd : distributed > 0) :
    (central + n * distributed) - ((central + 1) + n * (distributed - 1)) = n - 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd) with ⟨d, rfl⟩
  cases n with
  | zero =>
      simp [Nat.succ_sub_one]
  | succ n' =>
      let x : ℕ := (n' + 1) * d
      have hBA : central + 1 + x ≤ central + (x + (n' + 1)) := by
        omega
      have hsub : central + (x + (n' + 1)) - (central + 1 + x) = n' := by
        apply (Nat.sub_eq_iff_eq_add hBA).2
        omega
      simpa [x, Nat.succ_sub_one, Nat.succ_mul, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsub

/-- Therefore, when n > 1, centralizing one unit of distributed work strictly lowers total DOF. -/
theorem centralization_step_reduces_total (central distributed n : ℕ)
    (hd : distributed > 0) (hn : n > 1) :
    (central + 1) + n * (distributed - 1) < central + n * distributed := by
  let A := central + n * distributed
  let B := (central + 1) + n * (distributed - 1)
  have hs : A - B = n - 1 := by
    unfold A B
    exact centralization_step_saves_n_minus_one central distributed n hd
  have hpos : 0 < A - B := by
    rw [hs]
    omega
  have hnotle : ¬ A ≤ B := by
    intro hle
    exact (Nat.ne_of_gt hpos) (Nat.sub_eq_zero_of_le hle)
  have hlt : B < A := lt_of_not_ge hnotle
  simpa [A, B] using hlt

/-- Bundled centralization dominance: lower total and fewer error sites. -/
theorem centralization_dominance_bundle (P : SpecificationProblem)
    (S_right S_wrong : SolutionArchitecture P)
    (hr : isRightHardness S_right) (hcentral : S_right.centralDOF > 0)
    (hw : isWrongHardness S_wrong) (n : ℕ)
    (hn_total : n > S_right.centralDOF) (hn_sites : n > 1) :
    totalDOF S_right n < totalDOF S_wrong n ∧
    errorSites S_right n < errorSites S_wrong n := by
  constructor
  · exact right_dominates_wrong P S_right S_wrong hr hw n hn_total
  · exact right_fewer_error_sites P S_right S_wrong hr hcentral hw n hn_sites

/-! ## Leverage Connection (Paper 3)

From Paper 3: Leverage = capabilities / DOF
Centralization increases leverage by reducing per-site DOF.
-/

/-- Leverage of a solution: capabilities per unit of total DOF -/
def leverageRatio (capabilities : ℕ) (S : SolutionArchitecture P) (n : ℕ) : ℕ × ℕ :=
  (capabilities, totalDOF S n)

/-- Centralized solutions have higher leverage (same capabilities, lower DOF) -/
theorem centralized_higher_leverage (P : SpecificationProblem)
    (S_central S_distrib : SolutionArchitecture P)
    (_caps : ℕ) (n : ℕ) (hn : n ≥ 1)
    (hc_eq : S_central.centralDOF = S_distrib.centralDOF + S_distrib.distributedDOF)
    (hd_zero : S_central.distributedDOF = 0)
    (_hd_pos : S_distrib.distributedDOF > 0) :
    totalDOF S_central n ≤ totalDOF S_distrib n := by
  unfold totalDOF
  simp [hd_zero]
  have h : n * S_distrib.distributedDOF ≥ S_distrib.distributedDOF := by
    apply Nat.le_mul_of_pos_left
    omega
  omega

/-! ## Type System Instantiation -/

/-- Native type system: all DOF centralized -/
def nativeTypeSystem (P : SpecificationProblem) : SolutionArchitecture P where
  centralDOF := P.intrinsicDOF
  distributedDOF := 0
  conservation := by omega

/-- Manual approach: all DOF distributed -/
def manualApproach (P : SpecificationProblem) : SolutionArchitecture P where
  centralDOF := 0
  distributedDOF := P.intrinsicDOF
  conservation := by omega

/-- Native type system has right hardness -/
theorem native_is_right (P : SpecificationProblem) :
    isRightHardness (nativeTypeSystem P) := by
  unfold isRightHardness nativeTypeSystem
  rfl

/-- Manual approach has wrong hardness (when DOF > 0) -/
theorem manual_is_wrong (P : SpecificationProblem) :
    isWrongHardness (manualApproach P) := by
  unfold isWrongHardness manualApproach
  exact P.dof_pos

/-- For n > intrinsicDOF, native dominates manual -/
theorem native_dominates_manual (P : SpecificationProblem) (n : ℕ)
    (hn : n > P.intrinsicDOF) :
    totalDOF (nativeTypeSystem P) n < totalDOF (manualApproach P) n := by
  apply right_dominates_wrong
  · exact native_is_right P
  · exact manual_is_wrong P
  · unfold nativeTypeSystem; exact hn

/-- Error sites: native has 1, manual has n × intrinsicDOF -/
theorem native_minimal_errors (P : SpecificationProblem) (n : ℕ) :
    errorSites (nativeTypeSystem P) n = 1 := by
  apply centralized_minimal_errors
  · unfold nativeTypeSystem; exact P.dof_pos
  · unfold nativeTypeSystem; rfl

theorem manual_errors_grow (P : SpecificationProblem) (n : ℕ) (hn : n > 0) :
    errorSites (manualApproach P) n ≥ n := by
  apply distributed_errors_grow
  · exact hn
  · exact manual_is_wrong P

/-! ## Simplicity-Tax Named Corollaries (LaTeX Section 8 Handles) -/

/-- Simplicity tax in this model is exactly distributed DOF. -/
def simplicityTax (P : SpecificationProblem) (S : SolutionArchitecture P) : ℕ :=
  S.distributedDOF

/-- Set-based gap cardinality: |R \ A|. -/
def gapCard {α : Type*} [DecidableEq α] (required native : Finset α) : ℕ :=
  (required \ native).card

/-- Exact set conservation for required dimensions:
    |R \ A| + |R ∩ A| = |R|. -/
theorem gap_conservation_card {α : Type*} [DecidableEq α] (required native : Finset α) :
    gapCard required native + (required ∩ native).card = required.card := by
  unfold gapCard
  exact Finset.card_sdiff_add_card_inter required native

/-- Total external work under per-site externalization. -/
def totalExternalWork {α : Type*} [DecidableEq α] (required native : Finset α) (n : ℕ) : ℕ :=
  n * gapCard required native

/-- Linear-growth identity used in the Simplicity Tax section. -/
theorem totalExternalWork_eq_n_mul_gapCard {α : Type*}
    [DecidableEq α]
    (required native : Finset α) (n : ℕ) :
    totalExternalWork required native n = n * gapCard required native := by
  rfl

/-- Amortization threshold n* = floor(Hc / t). -/
def amortizationThreshold (centralCost taxPerSite : ℕ) : ℕ :=
  centralCost / taxPerSite

/-- If per-site tax is positive, crossing n* makes complete-model total lower. -/
theorem complete_model_dominates_after_threshold
    (centralCost taxPerSite n : ℕ)
    (htax : taxPerSite > 0)
    (hn : n > amortizationThreshold centralCost taxPerSite) :
    centralCost < n * taxPerSite := by
  have hdiv : centralCost / taxPerSite < n := hn
  exact (Nat.div_lt_iff_lt_mul htax).1 hdiv

/-- Linear maintenance costs are eventually dominated by exponential search costs. -/
theorem linear_lt_exponential_eventually (k : ℕ) :
    ∃ n0, ∀ n ≥ n0, k < 2 ^ n := by
  refine ⟨k, ?_⟩
  intro n hn
  exact lt_of_le_of_lt hn Nat.lt_two_pow_self

/-- Linear maintenance remains eventually dominated even with an additive constant term. -/
theorem linear_lt_exponential_plus_constant_eventually (k c : ℕ) :
    ∃ n0, ∀ n ≥ n0, k < 2 ^ n + c := by
  rcases linear_lt_exponential_eventually k with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n hn
  have hk : k < 2 ^ n := hn0 n hn
  exact lt_of_lt_of_le hk (Nat.le_add_right _ _)

/-- Conservation restated with SimplicityTax notation. -/
theorem simplicityTax_conservation (P : SpecificationProblem) (S : SolutionArchitecture P) :
    S.centralDOF + simplicityTax P S ≥ P.intrinsicDOF := by
  simpa [simplicityTax] using dof_conservation P S

/-- Positive simplicity tax implies total work grows with use-site count. -/
theorem simplicityTax_grows (P : SpecificationProblem) (S : SolutionArchitecture P)
    (n₁ n₂ : ℕ) (hn : n₁ < n₂) (htax : simplicityTax P S > 0) :
    totalDOF S n₁ < totalDOF S n₂ := by
  have hd : S.distributedDOF > 0 := by
    simpa [simplicityTax] using htax
  exact distributed_multiplies S n₁ n₂ hn hd

/-- Amortization threshold instantiated by native-vs-manual architecture. -/
theorem amortization_threshold_native_manual (P : SpecificationProblem) (n : ℕ)
    (hn : n > P.intrinsicDOF) :
    totalDOF (nativeTypeSystem P) n < totalDOF (manualApproach P) n := by
  exact native_dominates_manual P n hn

/-! ## Extension: Non-Additive Site-Cost Models -/

/-- A cost function is eventually constant if it stabilizes after some index. -/
def IsEventuallyConstant (f : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, f n = f N

/-- In the linear model, distributedDOF = 0 implies eventual constancy. -/
theorem totalDOF_eventually_constant_of_zero_distributed (S : SolutionArchitecture P)
    (h0 : S.distributedDOF = 0) :
    IsEventuallyConstant (fun n => totalDOF S n) := by
  refine ⟨0, ?_⟩
  intro n _
  simpa using (centralized_constant S n 0 h0)

/-- In the linear model, eventual constancy forces distributedDOF = 0. -/
theorem zero_distributed_of_totalDOF_eventually_constant (S : SolutionArchitecture P)
    (hconst : IsEventuallyConstant (fun n => totalDOF S n)) :
    S.distributedDOF = 0 := by
  by_contra hne
  have hd : S.distributedDOF > 0 := Nat.pos_of_ne_zero hne
  rcases hconst with ⟨N, hN⟩
  have hEq : totalDOF S (N + 1) = totalDOF S N := by
    exact hN (N + 1) (Nat.le_succ N)
  have hLt : totalDOF S N < totalDOF S (N + 1) :=
    distributed_multiplies S N (N + 1) (Nat.lt_succ_self N) hd
  exact (ne_of_lt hLt) hEq.symm

/-- Saturation criterion for the linear model: iff distributedDOF = 0. -/
theorem totalDOF_eventually_constant_iff_zero_distributed (S : SolutionArchitecture P) :
    IsEventuallyConstant (fun n => totalDOF S n) ↔ S.distributedDOF = 0 := by
  constructor
  · exact zero_distributed_of_totalDOF_eventually_constant S
  · exact totalDOF_eventually_constant_of_zero_distributed S

/-- A canonical saturating site-cost function in the generalized model. -/
def saturatingSiteCost (K : ℕ) (n : ℕ) : ℕ :=
  if n ≤ K then n else K

/-- Generalized total cost with arbitrary per-site accumulation. -/
def generalizedTotalDOF (central : ℕ) (siteCost : ℕ → ℕ) (n : ℕ) : ℕ :=
  central + siteCost n

/-- Pointwise nonlinear dominance:
    if right-site accumulation at n is bounded by B and wrong-site accumulation
    at n is at least n, then crossing centralRight + B yields strict dominance. -/
theorem generalized_right_dominates_wrong_pointwise
    (centralRight centralWrong B n : ℕ)
    (siteRight siteWrong : ℕ → ℕ)
    (hRightBound : siteRight n ≤ B)
    (hWrongLower : n ≤ siteWrong n)
    (hn : n > centralRight + B) :
    generalizedTotalDOF centralRight siteRight n <
      generalizedTotalDOF centralWrong siteWrong n := by
  unfold generalizedTotalDOF
  have hRightLe : centralRight + siteRight n ≤ centralRight + B :=
    Nat.add_le_add_left hRightBound centralRight
  have hRightLt : centralRight + siteRight n < n := lt_of_le_of_lt hRightLe hn
  have hWrongGe : n ≤ centralWrong + siteWrong n := by
    exact le_trans hWrongLower (Nat.le_add_left _ _)
  exact lt_of_lt_of_le hRightLt hWrongGe

/-- Nonlinear dominance by growth separation:
    bounded right-site accumulation versus identity-lower-bounded wrong-site accumulation. -/
theorem generalized_right_dominates_wrong_of_bounded_vs_identity_lower
    (centralRight centralWrong B n : ℕ)
    (siteRight siteWrong : ℕ → ℕ)
    (hRightBound : ∀ m, siteRight m ≤ B)
    (hWrongLower : ∀ m, m ≤ siteWrong m)
    (hn : n > centralRight + B) :
    generalizedTotalDOF centralRight siteRight n <
      generalizedTotalDOF centralWrong siteWrong n := by
  exact generalized_right_dominates_wrong_pointwise
    centralRight centralWrong B n siteRight siteWrong
    (hRightBound n) (hWrongLower n) hn

/-- Eventual nonlinear dominance:
    if right-site accumulation is globally bounded and wrong-site accumulation
    eventually dominates identity, right architecture eventually dominates. -/
theorem generalized_right_eventually_dominates_wrong
    (centralRight centralWrong B N : ℕ)
    (siteRight siteWrong : ℕ → ℕ)
    (hRightBound : ∀ m, siteRight m ≤ B)
    (hWrongLowerFrom : ∀ m, m ≥ N → m ≤ siteWrong m) :
    ∃ N0, ∀ n ≥ N0,
      generalizedTotalDOF centralRight siteRight n <
        generalizedTotalDOF centralWrong siteWrong n := by
  refine ⟨max N (centralRight + B + 1), ?_⟩
  intro n hn
  have hN : n ≥ N := le_trans (Nat.le_max_left _ _) hn
  have hBound : centralRight + B + 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnStrict : n > centralRight + B := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (centralRight + B)) hBound
  exact generalized_right_dominates_wrong_pointwise
    centralRight centralWrong B n siteRight siteWrong
    (hRightBound n) (hWrongLowerFrom n hN) hnStrict

/-- Boundary theorem: without wrong-side growth lower bounds, strict dominance is not guaranteed. -/
theorem generalized_dominance_can_fail_without_wrong_growth :
    ∃ (centralRight centralWrong : ℕ) (siteRight siteWrong : ℕ → ℕ),
      (¬ ∀ m, m ≤ siteWrong m) ∧
      (∀ n, ¬ generalizedTotalDOF centralRight siteRight n <
        generalizedTotalDOF centralWrong siteWrong n) := by
  refine ⟨1, 0, (fun _ => 0), (fun _ => 0), ?_, ?_⟩
  · intro h
    exact (Nat.not_succ_le_zero 0) (h 1)
  · intro n
    simp [generalizedTotalDOF]

/-- Boundary theorem: without a right-side boundedness assumption,
    strict dominance is not guaranteed even when wrong-side growth is linear. -/
theorem generalized_dominance_can_fail_without_right_boundedness :
    ∃ (centralRight centralWrong : ℕ) (siteRight siteWrong : ℕ → ℕ),
      (¬ ∃ B, ∀ m, siteRight m ≤ B) ∧
      (∀ m, m ≤ siteWrong m) ∧
      (∀ n, ¬ generalizedTotalDOF centralRight siteRight n <
        generalizedTotalDOF centralWrong siteWrong n) := by
  refine ⟨0, 0, (fun m => m + 1), (fun m => m), ?_, ?_, ?_⟩
  · intro hBound
    rcases hBound with ⟨B, hB⟩
    have h : B + 1 + 1 ≤ B := hB (B + 1)
    omega
  · intro m
    exact le_rfl
  · intro n
    simp [generalizedTotalDOF]

/-- Saturating site cost is eventually constant. -/
theorem saturatingSiteCost_eventually_constant (K : ℕ) :
    IsEventuallyConstant (saturatingSiteCost K) := by
  refine ⟨K, ?_⟩
  intro n hn
  unfold saturatingSiteCost
  by_cases hle : n ≤ K
  · have hEq : n = K := Nat.le_antisymm hle hn
    simp [hle, hEq]
  · simp [hle]

/-- Generalized total with saturating site cost is eventually constant. -/
theorem generalizedTotal_with_saturation_eventually_constant (central K : ℕ) :
    IsEventuallyConstant (fun n => generalizedTotalDOF central (saturatingSiteCost K) n) := by
  refine ⟨K, ?_⟩
  intro n hn
  unfold generalizedTotalDOF saturatingSiteCost
  by_cases hle : n ≤ K
  · have hEq : n = K := Nat.le_antisymm hle hn
    simp [hle, hEq]
  · simp [hle]

/-- Any linear representation of a saturating cost must have zero slope. -/
theorem linear_represents_saturating_only_zero_slope (c d K : ℕ)
    (hrep : ∀ n, c + n * d = generalizedTotalDOF c (saturatingSiteCost K) n) :
    d = 0 := by
  have hK : c + K * d = generalizedTotalDOF c (saturatingSiteCost K) K := hrep K
  have hK1 : c + (K + 1) * d = generalizedTotalDOF c (saturatingSiteCost K) (K + 1) := hrep (K + 1)
  unfold generalizedTotalDOF saturatingSiteCost at hK hK1
  have hEq : c + K * d = c + (K + 1) * d := by
    calc
      c + K * d = c + K := by simpa using hK
      _ = c + (K + 1) * d := by
        have hk : ¬ (K + 1 ≤ K) := Nat.not_succ_le_self K
        simpa [hk] using hK1.symm
  have hEq' : c + K * d = c + K * d + d := by
    simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEq
  omega

/-- Therefore positive-slope linear models cannot realize saturation for all n. -/
theorem no_positive_slope_linear_represents_saturating (c d K : ℕ)
    (hd : d > 0) :
    ¬ (∀ n, c + n * d = generalizedTotalDOF c (saturatingSiteCost K) n) := by
  intro hrep
  have hzero : d = 0 := linear_represents_saturating_only_zero_slope c d K hrep
  exact (Nat.ne_of_gt hd) hzero

end DecisionQuotient.HardnessDistribution
