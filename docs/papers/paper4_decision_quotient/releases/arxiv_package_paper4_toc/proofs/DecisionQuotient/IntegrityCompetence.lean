/-
  Paper 4: Decision Quotient

  IntegrityCompetence.lean

  Formalizes the Foundations-section split between:
  - Solver integrity (sound certified assertions)
  - Regime competence (integrity + non-abstaining coverage + resource bound)

  LaTeX references:
  - Definition: certifying solver / solver integrity / competence under regime
  - Proposition: Integrity--Competence Separation
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace DecisionQuotient.IntegrityCompetence

open Set

universe u v w

variable {X : Type u} {Y : Type v} {W : Type w}

/-- Regime tuple used by competence claims:
    in-scope instances, encoding length, and resource budget. -/
structure Regime (X : Type u) where
  inScope : Set X
  encLen : X → ℕ
  budget : ℕ → ℕ

/-- Certifying solver: may abstain, otherwise emits candidate output + witness,
    together with a checker and solve-side cost function. -/
structure CertifyingSolver (X : Type u) (Y : Type v) (W : Type w) where
  solve : X → Option (Y × W)
  check : X → Y → W → Prop
  solveCost : X → ℕ

/-- Relation induced by a deterministic partial program map. -/
def inducedRelation (f : X → Option Y) : Set (X × Y) :=
  {xy | f xy.1 = some xy.2}

/-- Canonical certifying solver generated from a deterministic partial map:
    if `f x = some y`, emit `(y, unit)`; otherwise abstain. -/
def solverOfPartialMap
    (f : X → Option Y)
    (solveCost : X → ℕ := fun _ => 0) :
    CertifyingSolver X Y PUnit where
  solve := fun x =>
    match f x with
    | none => none
    | some y => some (y, PUnit.unit)
  check := fun x y _ => f x = some y
  solveCost := solveCost

/-- Solver integrity:
    1. Any asserted output must pass the checker.
    2. Any checker-accepted claim is semantically correct. -/
def SolverIntegrity (R : Set (X × Y)) (Q : CertifyingSolver X Y W) : Prop :=
  (∀ x y w, Q.solve x = some (y, w) → Q.check x y w) ∧
  (∀ x y w, Q.check x y w → (x, y) ∈ R)

/-- Competence under a declared regime:
    integrity + non-abstaining coverage on in-scope instances + solve-side budget. -/
def CompetentOn (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W) : Prop :=
  SolverIntegrity R Q ∧
  (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w)) ∧
  (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))

/-- ε-typed objective family:
    for each tolerance ε, `Rε ε` is the certified target relation. -/
abbrev EpsilonRelation (X : Type u) (Y : Type v) := ℝ → Set (X × Y)

/-- ε-competence under a declared regime:
    competence for the ε-indexed target relation. -/
def EpsilonCompetentOn
    (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) : Prop :=
  CompetentOn (Rε ε) Γ Q

/-- Typed claim report for declared objectives. -/
inductive ClaimReport where
  | abstain
  | exact
  | epsilon (ε : ℝ)

/-- Claim admissibility discipline:
    - abstain is always admissible,
    - exact claims require exact competence certificate,
    - ε-claims require ε-competence certificate. -/
def ClaimAdmissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimReport → Prop
  | .abstain => True
  | .exact => CompetentOn R Γ Q
  | .epsilon ε => EpsilonCompetentOn Rε ε Γ Q

/-- First-class evidence object for a declared report type. -/
inductive EvidenceForReport
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimReport → Type where
  | abstain :
      EvidenceForReport R Rε Γ Q ClaimReport.abstain
  | exact (h : CompetentOn R Γ Q) :
      EvidenceForReport R Rε Γ Q ClaimReport.exact
  | epsilon (ε : ℝ) (h : EpsilonCompetentOn Rε ε Γ Q) :
      EvidenceForReport R Rε Γ Q (ClaimReport.epsilon ε)

/-- Any evidence object yields admissibility of that report. -/
theorem claim_admissible_of_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (r : ClaimReport) :
    EvidenceForReport R Rε Γ Q r → ClaimAdmissible R Rε Γ Q r := by
  intro h
  cases h with
  | abstain =>
      simp [ClaimAdmissible]
  | exact hComp =>
      simpa [ClaimAdmissible] using hComp
  | epsilon ε hEps =>
      simpa [ClaimAdmissible] using hEps

/-- Witness constructor: any admissibility claim yields a formal evidence object. -/
def evidence_of_claim_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (r : ClaimReport) :
    ClaimAdmissible R Rε Γ Q r → EvidenceForReport R Rε Γ Q r := by
  intro h
  cases r with
  | abstain =>
      exact EvidenceForReport.abstain
  | exact =>
      exact EvidenceForReport.exact h
  | epsilon ε =>
      exact EvidenceForReport.epsilon ε h

/-- Extensional equivalence: admissibility iff evidence object exists. -/
theorem evidence_nonempty_iff_claim_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (r : ClaimReport) :
    Nonempty (EvidenceForReport R Rε Γ Q r) ↔ ClaimAdmissible R Rε Γ Q r := by
  constructor
  · intro h
    rcases h with ⟨hw⟩
    exact claim_admissible_of_evidence (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := r) hw
  · intro h
    exact ⟨evidence_of_claim_admissible (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := r) h⟩

/-- Exact-claim admissibility is equivalent to existence of exact evidence. -/
theorem exact_claim_admissible_iff_exact_evidence_nonempty
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimAdmissible R Rε Γ Q ClaimReport.exact ↔
      Nonempty (EvidenceForReport R Rε Γ Q ClaimReport.exact) := by
  exact (evidence_nonempty_iff_claim_admissible
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := ClaimReport.exact)).symm

/-- Exact claims require exact evidence in the typed discipline. -/
theorem exact_claim_requires_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (hExact : ClaimAdmissible R Rε Γ Q ClaimReport.exact) :
    Nonempty (EvidenceForReport R Rε Γ Q ClaimReport.exact) := by
  exact (exact_claim_admissible_iff_exact_evidence_nonempty
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q)).1 hExact

/-- Unit-interval percentage used for report-side confidence signals. -/
abbrev Percent := {p : ℚ // 0 ≤ p ∧ p ≤ 1}

/-- Canonical zero-confidence percentage token. -/
def percentZero : Percent := ⟨0, by constructor <;> norm_num⟩

/-- Signaled typed report:
    optional guess plus self-reflected/certified confidence and
    a scalar execution witness (`stepsRun`) with optional declared bound. -/
structure ReportSignal (Y : Type v) where
  report : ClaimReport
  guess : Option Y
  selfPct : Percent
  certifiedPct : Percent
  stepsRun : Nat
  declaredBound : Option Nat

/-- Completion-fraction semantics are well-defined only under an explicit
    positive declared bound that covers observed steps. -/
def CompletionFractionDefined
    (σ : ReportSignal Y) : Prop :=
  ∃ b : Nat, σ.declaredBound = some b ∧ 0 < b ∧ σ.stepsRun ≤ b

/-- Scalar step witness is always defined as an exact natural number. -/
theorem steps_run_scalar_always_defined
    (σ : ReportSignal Y) :
    ∃ k : Nat, σ.stepsRun = k := by
  exact ⟨σ.stepsRun, rfl⟩

/-- Scalar step witness is falsifiable by exact numeric equality checks. -/
theorem steps_run_scalar_falsifiable
    (σ : ReportSignal Y) (k : Nat) :
    σ.stepsRun = k ∨ σ.stepsRun ≠ k := by
  exact em (σ.stepsRun = k)

/-- Completion fraction becomes meaningful when a positive declared bound
    exists and observed steps are within that bound. -/
theorem completion_fraction_defined_of_declared_bound
    (σ : ReportSignal Y) (b : Nat)
    (hBound : σ.declaredBound = some b)
    (hPos : 0 < b)
    (hLe : σ.stepsRun ≤ b) :
    CompletionFractionDefined σ := by
  exact ⟨b, hBound, hPos, hLe⟩

/-- Without a declared bound, completion-fraction semantics are undefined. -/
theorem no_completion_fraction_without_declared_bound
    (σ : ReportSignal Y)
    (hNone : σ.declaredBound = none) :
    ¬ CompletionFractionDefined σ := by
  intro hFrac
  rcases hFrac with ⟨b, hSome, _hPos, _hLe⟩
  rw [hNone] at hSome
  cases hSome

/-- Signal consistency discipline:
    positive certified confidence is allowed only when matching evidence exists. -/
def SignalConsistent
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (σ : ReportSignal Y) : Prop :=
  0 < σ.certifiedPct.1 →
    Nonempty (EvidenceForReport R Rε Γ Q σ.report)

/-- Any admissible typed claim induces a signal-consistent report
    regardless of the chosen self/certified percentages. -/
theorem signal_consistent_of_claim_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (σ : ReportSignal Y)
    (hAdm : ClaimAdmissible R Rε Γ Q σ.report) :
    SignalConsistent R Rε Γ Q σ := by
  intro _hPos
  exact (evidence_nonempty_iff_claim_admissible
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := σ.report)).2 hAdm

/-- Positive certified-confidence signal implies report admissibility. -/
theorem signal_certified_positive_implies_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (σ : ReportSignal Y)
    (hSig : SignalConsistent R Rε Γ Q σ)
    (hPos : 0 < σ.certifiedPct.1) :
    ClaimAdmissible R Rε Γ Q σ.report := by
  rcases hSig hPos with ⟨hw⟩
  exact claim_admissible_of_evidence
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := σ.report) hw

/-- Under signal consistency, absent evidence forces zero certified confidence. -/
theorem signal_no_evidence_forces_zero_certified
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (σ : ReportSignal Y)
    (hSig : SignalConsistent R Rε Γ Q σ)
    (hNo : ¬ Nonempty (EvidenceForReport R Rε Γ Q σ.report)) :
    σ.certifiedPct.1 = 0 := by
  have hNotPos : ¬ 0 < σ.certifiedPct.1 := by
    intro hPos
    exact hNo (hSig hPos)
  have hLe0 : σ.certifiedPct.1 ≤ 0 := le_of_not_gt hNotPos
  exact le_antisymm hLe0 σ.certifiedPct.2.1

/-- For exact reports, if exact competence is unavailable, certified confidence
    must collapse to zero under the signal-consistency discipline. -/
theorem signal_exact_no_competence_forces_zero_certified
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (σ : ReportSignal Y)
    (hExact : σ.report = ClaimReport.exact)
    (hSig : SignalConsistent R Rε Γ Q σ)
    (hNoComp : ¬ CompetentOn R Γ Q) :
    σ.certifiedPct.1 = 0 := by
  have hNoEvidence : ¬ Nonempty (EvidenceForReport R Rε Γ Q σ.report) := by
    intro hEv
    rcases hEv with ⟨hw⟩
    have hAdm : ClaimAdmissible R Rε Γ Q σ.report :=
      claim_admissible_of_evidence (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := σ.report) hw
    have hComp : CompetentOn R Γ Q := by
      simpa [hExact, ClaimAdmissible] using hAdm
    exact hNoComp hComp
  exact signal_no_evidence_forces_zero_certified
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (σ := σ) hSig hNoEvidence

/-- Abstain can carry an optional guess and arbitrary self-reflected confidence
    while remaining signal-consistent with zero certified confidence. -/
theorem abstain_signal_exists_with_guess_self
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (g : Option Y) (pSelf : Percent) :
    ∃ σ : ReportSignal Y,
      σ.report = ClaimReport.abstain ∧
      σ.guess = g ∧
      σ.selfPct = pSelf ∧
      SignalConsistent R Rε Γ Q σ := by
  refine ⟨{
    report := ClaimReport.abstain
    guess := g
    selfPct := pSelf
    certifiedPct := percentZero
    stepsRun := 0
    declaredBound := none
  }, rfl, rfl, rfl, ?_⟩
  intro hPos
  have hImpossible : (0 : ℚ) < 0 := by
    simpa [percentZero] using hPos
  exact False.elim ((lt_irrefl (0 : ℚ)) hImpossible)

/-- Self-reflected confidence alone cannot certify exactness:
    with zero certified confidence, exact report remains inadmissible
    whenever exact competence is unavailable. -/
theorem self_reflected_confidence_not_certification
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (g : Option Y) (pSelf : Percent)
    (hNoComp : ¬ CompetentOn R Γ Q) :
    ∃ σ : ReportSignal Y,
      σ.report = ClaimReport.exact ∧
      σ.guess = g ∧
      σ.selfPct = pSelf ∧
      SignalConsistent R Rε Γ Q σ ∧
      ¬ ClaimAdmissible R Rε Γ Q σ.report := by
  refine ⟨{
    report := ClaimReport.exact
    guess := g
    selfPct := pSelf
    certifiedPct := percentZero
    stepsRun := 0
    declaredBound := none
  }, rfl, rfl, rfl, ?_, ?_⟩
  · intro hPos
    have hImpossible : (0 : ℚ) < 0 := by
      simpa [percentZero] using hPos
    exact False.elim ((lt_irrefl (0 : ℚ)) hImpossible)
  · simpa [ClaimAdmissible] using hNoComp

/-- Certainty inflation: a report is emitted without a matching evidence object. -/
def CertaintyInflation
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (r : ClaimReport) : Prop :=
  ¬ Nonempty (EvidenceForReport R Rε Γ Q r)

/-- Exact-report specialization of certainty inflation. -/
def ExactCertaintyInflation
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) : Prop :=
  CertaintyInflation R Rε Γ Q ClaimReport.exact

/-- Certainty inflation is equivalent to typed-report inadmissibility. -/
theorem certaintyInflation_iff_not_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (r : ClaimReport) :
    CertaintyInflation R Rε Γ Q r ↔ ¬ ClaimAdmissible R Rε Γ Q r := by
  unfold CertaintyInflation
  exact not_congr (evidence_nonempty_iff_claim_admissible
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := r))

/-- Exact certainty inflation is exactly failure of exact competence. -/
theorem exactCertaintyInflation_iff_no_exact_competence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ExactCertaintyInflation R Rε Γ Q ↔ ¬ CompetentOn R Γ Q := by
  unfold ExactCertaintyInflation
  constructor
  · intro hInfl
    have hNoAdm :
        ¬ ClaimAdmissible R Rε Γ Q ClaimReport.exact :=
      (certaintyInflation_iff_not_admissible
        (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := ClaimReport.exact)).1 hInfl
    intro hComp
    exact hNoAdm (by simpa [ClaimAdmissible] using hComp)
  · intro hNoComp
    apply (certaintyInflation_iff_not_admissible
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := ClaimReport.exact)).2
    intro hAdm
    exact hNoComp (by simpa [ClaimAdmissible] using hAdm)

/-- Bit-accounting model for typed reports:
    separates raw payload bits from certificate bits.
    This supports an explicit ``raw vs certified'' information accounting layer. -/
structure ReportBitModel where
  rawBits : ClaimReport → ℕ
  certBits : ClaimReport → ℕ
  exactRawPos : 0 < rawBits ClaimReport.exact
  epsilonRawPos : ∀ ε : ℝ, 0 < rawBits (ClaimReport.epsilon ε)
  exactCertPos : 0 < certBits ClaimReport.exact
  epsilonCertPos : ∀ ε : ℝ, 0 < certBits (ClaimReport.epsilon ε)

/-- Certification overhead bits:
    certificate bits count only when a matching evidence object exists. -/
noncomputable def certificationOverheadBits
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport) : ℕ := by
  classical
  exact if Nonempty (EvidenceForReport R Rε Γ Q r) then M.certBits r else 0

/-- Total certified-bit footprint for a report:
    raw report bits plus evidence-gated certification overhead. -/
noncomputable def certifiedTotalBits
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport) : ℕ :=
  M.rawBits r + certificationOverheadBits R Rε Γ Q M r

/-- Structural split: total certified bits decompose into raw bits plus
    certification overhead bits. -/
theorem certifiedTotalBits_eq_raw_plus_overhead
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport) :
    certifiedTotalBits R Rε Γ Q M r =
      M.rawBits r + certificationOverheadBits R Rε Γ Q M r := by
  rfl

/-- If no evidence exists for a report type, certification overhead is zero. -/
theorem certificationOverheadBits_of_no_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hNo : ¬ Nonempty (EvidenceForReport R Rε Γ Q r)) :
    certificationOverheadBits R Rε Γ Q M r = 0 := by
  classical
  simp [certificationOverheadBits, hNo]

/-- If evidence exists for a report type, certification overhead equals
    the declared certificate-bit allocation for that report type. -/
theorem certificationOverheadBits_of_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hYes : Nonempty (EvidenceForReport R Rε Γ Q r)) :
    certificationOverheadBits R Rε Γ Q M r = M.certBits r := by
  classical
  simp [certificationOverheadBits, hYes]

/-- If no evidence exists, total certified bits collapse to raw bits. -/
theorem certifiedTotalBits_of_no_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hNo : ¬ Nonempty (EvidenceForReport R Rε Γ Q r)) :
    certifiedTotalBits R Rε Γ Q M r = M.rawBits r := by
  classical
  simp [certifiedTotalBits, certificationOverheadBits, hNo]

/-- If evidence exists, total certified bits are raw plus declared certificate bits. -/
theorem certifiedTotalBits_of_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hYes : Nonempty (EvidenceForReport R Rε Γ Q r)) :
    certifiedTotalBits R Rε Γ Q M r = M.rawBits r + M.certBits r := by
  classical
  simp [certifiedTotalBits, certificationOverheadBits, hYes]

/-- Total certified-bit footprint dominates raw-bit footprint. -/
theorem certifiedTotalBits_ge_raw
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport) :
    M.rawBits r ≤ certifiedTotalBits R Rε Γ Q M r := by
  unfold certifiedTotalBits
  exact Nat.le_add_right _ _

/-- If evidence exists and certificate bits are positive,
    total certified bits strictly exceed raw bits. -/
theorem certifiedTotalBits_gt_raw_of_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hYes : Nonempty (EvidenceForReport R Rε Γ Q r))
    (hPos : 0 < M.certBits r) :
    M.rawBits r < certifiedTotalBits R Rε Γ Q M r := by
  have hEq := certifiedTotalBits_of_evidence
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) (r := r) hYes
  rw [hEq]
  exact Nat.lt_add_of_pos_right hPos

/-- Report-level exact equivalence:
    with positive certificate bits for report type `r`,
    raw-only accounting is equivalent to certainty inflation for `r`. -/
theorem report_raw_eq_certifiedTotal_iff_certaintyInflation
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hPos : 0 < M.certBits r) :
    certifiedTotalBits R Rε Γ Q M r = M.rawBits r ↔
      CertaintyInflation R Rε Γ Q r := by
  constructor
  · intro hEq
    unfold CertaintyInflation
    intro hYes
    have hLt :
        M.rawBits r < certifiedTotalBits R Rε Γ Q M r :=
      certifiedTotalBits_gt_raw_of_evidence
        (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) (r := r) hYes hPos
    exact (Nat.lt_irrefl (M.rawBits r)) (by simpa [hEq] using hLt)
  · intro hInfl
    exact certifiedTotalBits_of_no_evidence
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) (r := r) hInfl

/-- Admissibility implies a strict certified-bit gap above raw bits
    for any report type with positive certificate-bit allocation. -/
theorem report_admissible_implies_raw_lt_certifiedTotal
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hPos : 0 < M.certBits r)
    (hAdm : ClaimAdmissible R Rε Γ Q r) :
    M.rawBits r < certifiedTotalBits R Rε Γ Q M r := by
  have hYes : Nonempty (EvidenceForReport R Rε Γ Q r) :=
    (evidence_nonempty_iff_claim_admissible
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := r)).2 hAdm
  exact certifiedTotalBits_gt_raw_of_evidence
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) (r := r) hYes hPos

/-- Inadmissibility implies raw-only accounting (no certified overhead). -/
theorem report_not_admissible_implies_raw_eq_certifiedTotal
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) (r : ClaimReport)
    (hNoAdm : ¬ ClaimAdmissible R Rε Γ Q r) :
    certifiedTotalBits R Rε Γ Q M r = M.rawBits r := by
  have hInfl : CertaintyInflation R Rε Γ Q r :=
    (certaintyInflation_iff_not_admissible
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := r)).2 hNoAdm
  exact certifiedTotalBits_of_no_evidence
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M) (r := r) hInfl

/-- Exact-report specialization:
    raw-only exact accounting is equivalent to exact certainty inflation. -/
theorem exact_raw_eq_certifiedTotal_iff_exactCertaintyInflation
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) :
    certifiedTotalBits R Rε Γ Q M ClaimReport.exact = M.rawBits ClaimReport.exact ↔
      ExactCertaintyInflation R Rε Γ Q := by
  simpa [ExactCertaintyInflation] using
    (report_raw_eq_certifiedTotal_iff_certaintyInflation
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)
      (r := ClaimReport.exact) M.exactCertPos)

/-- Exact-report specialization:
    exact admissibility is equivalent to a strict certified-bit gap above raw bits. -/
theorem exact_admissible_iff_raw_lt_certifiedTotal
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) :
    ClaimAdmissible R Rε Γ Q ClaimReport.exact ↔
      M.rawBits ClaimReport.exact < certifiedTotalBits R Rε Γ Q M ClaimReport.exact := by
  constructor
  · intro hAdm
    exact report_admissible_implies_raw_lt_certifiedTotal
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)
      (r := ClaimReport.exact) M.exactCertPos hAdm
  · intro hGap
    by_contra hNoAdm
    have hEq := report_not_admissible_implies_raw_eq_certifiedTotal
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)
      (r := ClaimReport.exact) hNoAdm
    exact (Nat.lt_irrefl (M.rawBits ClaimReport.exact)) (by simpa [hEq] using hGap)

/-- Exact-report specialization:
    if exact report is inadmissible, exact accounting is raw-only. -/
theorem exact_raw_only_of_no_exact_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel)
    (hNoAdm : ¬ ClaimAdmissible R Rε Γ Q ClaimReport.exact) :
    certifiedTotalBits R Rε Γ Q M ClaimReport.exact = M.rawBits ClaimReport.exact := by
  exact report_not_admissible_implies_raw_eq_certifiedTotal
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)
    (r := ClaimReport.exact) hNoAdm

/-- ε-report specialization:
    ε-admissibility is equivalent to a strict certified-bit gap above raw bits. -/
theorem epsilon_admissible_iff_raw_lt_certifiedTotal
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (M : ReportBitModel) :
    ClaimAdmissible R Rε Γ Q (ClaimReport.epsilon ε) ↔
      M.rawBits (ClaimReport.epsilon ε) <
        certifiedTotalBits R Rε Γ Q M (ClaimReport.epsilon ε) := by
  constructor
  · intro hAdm
    exact report_admissible_implies_raw_lt_certifiedTotal
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)
      (r := ClaimReport.epsilon ε) (M.epsilonCertPos ε) hAdm
  · intro hGap
    by_contra hNoAdm
    have hEq := report_not_admissible_implies_raw_eq_certifiedTotal
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (M := M)
      (r := ClaimReport.epsilon ε) hNoAdm
    exact (Nat.lt_irrefl (M.rawBits (ClaimReport.epsilon ε))) (by simpa [hEq] using hGap)

/-- RLFF reward weights for report-typed feedback. -/
structure RLFFWeights where
  abstainReward : ℤ
  exactReward : ℤ
  epsilonReward : ℝ → ℤ
  inadmissiblePenalty : ℤ

/-- Base reward by report type (applied only when evidence exists). -/
def rlffBaseReward (w : RLFFWeights) : ClaimReport → ℤ
  | .abstain => w.abstainReward
  | .exact => w.exactReward
  | .epsilon ε => w.epsilonReward ε

/-- RLFF objective:
    evidence-gated reward with explicit inadmissibility penalty. -/
noncomputable def rlffReward
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) (r : ClaimReport) : ℤ :=
  by
    classical
    exact if Nonempty (EvidenceForReport R Rε Γ Q r) then
      rlffBaseReward w r
    else
      -w.inadmissiblePenalty

/-- Unsupported reports receive the explicit penalty branch. -/
theorem rlffReward_of_no_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) (r : ClaimReport)
    (hNo : ¬ Nonempty (EvidenceForReport R Rε Γ Q r)) :
    rlffReward R Rε Γ Q w r = -w.inadmissiblePenalty := by
  classical
  simp [rlffReward, hNo]

/-- Supported reports receive their base reward branch. -/
theorem rlffReward_of_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) (r : ClaimReport)
    (hYes : Nonempty (EvidenceForReport R Rε Γ Q r)) :
    rlffReward R Rε Γ Q w r = rlffBaseReward w r := by
  classical
  simp [rlffReward, hYes]

/-- Abstain has an always-available evidence witness in RLFF. -/
theorem rlffReward_abstain
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) :
    rlffReward R Rε Γ Q w ClaimReport.abstain = w.abstainReward := by
  have hYes : Nonempty (EvidenceForReport R Rε Γ Q ClaimReport.abstain) :=
    ⟨EvidenceForReport.abstain⟩
  simpa [rlffBaseReward] using
    (rlffReward_of_evidence (R := R) (Rε := Rε) (Γ := Γ) (Q := Q)
      (w := w) (r := ClaimReport.abstain) hYes)

/-- Any global RLFF maximizer is evidence-backed when abstain beats penalty. -/
theorem rlff_maximizer_has_evidence
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) (r : ClaimReport)
    (hAbstainBeatsPenalty : -w.inadmissiblePenalty < w.abstainReward)
    (hMax : ∀ r' : ClaimReport, rlffReward R Rε Γ Q w r' ≤ rlffReward R Rε Γ Q w r) :
    Nonempty (EvidenceForReport R Rε Γ Q r) := by
  by_contra hNo
  have hR : rlffReward R Rε Γ Q w r = -w.inadmissiblePenalty :=
    rlffReward_of_no_evidence (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (w := w) (r := r) hNo
  have hA : rlffReward R Rε Γ Q w ClaimReport.abstain = w.abstainReward :=
    rlffReward_abstain (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (w := w)
  have hAleR : rlffReward R Rε Γ Q w ClaimReport.abstain ≤ rlffReward R Rε Γ Q w r :=
    hMax ClaimReport.abstain
  have hLe : w.abstainReward ≤ -w.inadmissiblePenalty := by
    simpa [hA, hR] using hAleR
  exact (not_le_of_gt hAbstainBeatsPenalty) hLe

/-- Global RLFF maximizer is admissible under abstain-over-penalty condition. -/
theorem rlff_maximizer_is_admissible
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) (r : ClaimReport)
    (hAbstainBeatsPenalty : -w.inadmissiblePenalty < w.abstainReward)
    (hMax : ∀ r' : ClaimReport, rlffReward R Rε Γ Q w r' ≤ rlffReward R Rε Γ Q w r) :
    ClaimAdmissible R Rε Γ Q r := by
  rcases rlff_maximizer_has_evidence
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (w := w) (r := r)
      hAbstainBeatsPenalty hMax with ⟨hw⟩
  exact claim_admissible_of_evidence
    (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (r := r) hw

/-- If exact/ε reports have no evidence, abstain is strictly preferred to each. -/
theorem rlff_abstain_strictly_prefers_no_certificates
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (w : RLFFWeights) (ε : ℝ)
    (hExactNo : ¬ Nonempty (EvidenceForReport R Rε Γ Q ClaimReport.exact))
    (hEpsNo : ¬ Nonempty (EvidenceForReport R Rε Γ Q (ClaimReport.epsilon ε)))
    (hAbstainBeatsPenalty : -w.inadmissiblePenalty < w.abstainReward) :
    rlffReward R Rε Γ Q w ClaimReport.abstain > rlffReward R Rε Γ Q w ClaimReport.exact ∧
      rlffReward R Rε Γ Q w ClaimReport.abstain >
        rlffReward R Rε Γ Q w (ClaimReport.epsilon ε) := by
  have hA : rlffReward R Rε Γ Q w ClaimReport.abstain = w.abstainReward :=
    rlffReward_abstain (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (w := w)
  have hE : rlffReward R Rε Γ Q w ClaimReport.exact = -w.inadmissiblePenalty :=
    rlffReward_of_no_evidence
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (w := w) (r := ClaimReport.exact) hExactNo
  have hEp : rlffReward R Rε Γ Q w (ClaimReport.epsilon ε) = -w.inadmissiblePenalty :=
    rlffReward_of_no_evidence
      (R := R) (Rε := Rε) (Γ := Γ) (Q := Q) (w := w) (r := ClaimReport.epsilon ε) hEpsNo
  constructor
  · simpa [hA, hE] using hAbstainBeatsPenalty
  · simpa [hA, hEp] using hAbstainBeatsPenalty

/-- Abstain is always admissible in the typed claim discipline. -/
theorem claim_admissible_abstain
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimAdmissible R Rε Γ Q ClaimReport.abstain := by
  simp [ClaimAdmissible]

/-- Exact-claim admissibility is exactly exact competence. -/
theorem claim_admissible_exact_iff
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimAdmissible R Rε Γ Q ClaimReport.exact ↔ CompetentOn R Γ Q := by
  rfl

/-- ε-claim admissibility is exactly ε-competence at that ε. -/
theorem claim_admissible_epsilon_iff
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimAdmissible R Rε Γ Q (ClaimReport.epsilon ε) ↔
      EpsilonCompetentOn Rε ε Γ Q := by
  rfl

/-- No exact certificate implies exact claim inadmissible. -/
theorem no_uncertified_exact_claim
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (hNo : ¬ CompetentOn R Γ Q) :
    ¬ ClaimAdmissible R Rε Γ Q ClaimReport.exact := by
  simpa [ClaimAdmissible] using hNo

/-- No ε-certificate implies ε-claim inadmissible. -/
theorem no_uncertified_epsilon_claim
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (hNo : ¬ EpsilonCompetentOn Rε ε Γ Q) :
    ¬ ClaimAdmissible R Rε Γ Q (ClaimReport.epsilon ε) := by
  simpa [ClaimAdmissible] using hNo

/-- Any admissible exact claim is integrity-preserving. -/
theorem admissible_exact_implies_integrity
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimAdmissible R Rε Γ Q ClaimReport.exact → SolverIntegrity R Q := by
  intro h
  exact h.1

/-- Any admissible ε-claim is integrity-preserving for the ε-relation. -/
theorem admissible_epsilon_implies_integrity
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    ClaimAdmissible R Rε Γ Q (ClaimReport.epsilon ε) →
      SolverIntegrity (Rε ε) Q := by
  intro h
  exact h.1

/-- Any deterministic partial map is a certifying solver for its induced relation. -/
theorem solverOfPartialMap_integrity
    (f : X → Option Y)
    (solveCost : X → ℕ := fun _ => 0) :
    SolverIntegrity (inducedRelation f)
      (solverOfPartialMap (X := X) (Y := Y) f solveCost) := by
  constructor
  · intro x y w hSolve
    cases hfx : f x with
    | none =>
        cases w
        simp [solverOfPartialMap, hfx] at hSolve
    | some y0 =>
        cases w
        simp [solverOfPartialMap, hfx] at hSolve ⊢
        exact hSolve
  · intro x y w hCheck
    exact hCheck

/-- Universality of solver framing:
    every deterministic partial map can be cast as a certifying solver pair. -/
theorem program_framed_as_solver
    (f : X → Option Y) :
    ∃ Q : CertifyingSolver X Y PUnit, SolverIntegrity (inducedRelation f) Q := by
  refine ⟨solverOfPartialMap (X := X) (Y := Y) f, ?_⟩
  exact solverOfPartialMap_integrity (X := X) (Y := Y) (f := f)

/-- Definitional form of solver integrity (substate-agnostic / substrate-parametric). -/
theorem solverIntegrity_substrate_parametric
    (R : Set (X × Y)) (Q : CertifyingSolver X Y W) :
    SolverIntegrity R Q ↔
      ((∀ x y w, Q.solve x = some (y, w) → Q.check x y w) ∧
       (∀ x y w, Q.check x y w → (x, y) ∈ R)) := by
  rfl

/-- Competence implies integrity by definition. -/
theorem competence_implies_integrity
    (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    CompetentOn R Γ Q → SolverIntegrity R Q := by
  intro h
  exact h.1

/-- ε-competence implies integrity for the ε-indexed relation. -/
theorem epsilon_competence_implies_integrity
    (Rε : EpsilonRelation X Y) (ε : ℝ)
    (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    EpsilonCompetentOn Rε ε Γ Q → SolverIntegrity (Rε ε) Q := by
  intro h
  exact competence_implies_integrity (R := Rε ε) (Γ := Γ) (Q := Q) h

/-- Zero-ε reduction at the competence level:
    if `Rε 0` is the exact relation `R`, ε-competence at ε=0 is exactly competence on `R`. -/
theorem zero_epsilon_competence_iff_exact
    (R : Set (X × Y)) (Rε : EpsilonRelation X Y)
    (h0 : Rε 0 = R) (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    EpsilonCompetentOn Rε 0 Γ Q ↔ CompetentOn R Γ Q := by
  simpa [EpsilonCompetentOn, h0]

/-- A canonical integrity-preserving abstaining solver:
    - Always abstains
    - Checker always rejects
    - Zero solve-side cost
-/
def alwaysAbstain : CertifyingSolver X Y W where
  solve := fun _ => none
  check := fun _ _ _ => False
  solveCost := fun _ => 0

/-- Always-abstain solver satisfies integrity for any target relation. -/
theorem alwaysAbstain_integrity (R : Set (X × Y)) :
    SolverIntegrity R (alwaysAbstain (X := X) (Y := Y) (W := W)) := by
  constructor
  · intro x y w h
    simp [alwaysAbstain] at h
  · intro x y w h
    simp [alwaysAbstain] at h

/-- Competence entails non-abstaining coverage on in-scope instances. -/
theorem competent_has_coverage
    (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (hComp : CompetentOn R Γ Q) :
    ∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w) :=
  hComp.2.1

/-- Integrity does not imply competence on any nonempty scope:
    an always-abstain solver is integrity-preserving but not competent. -/
theorem integrity_not_competent_of_nonempty_scope
    (R : Set (X × Y)) (Γ : Regime X) (hScope : Γ.inScope.Nonempty) :
    ∃ Q : CertifyingSolver X Y W, SolverIntegrity R Q ∧ ¬ CompetentOn R Γ Q := by
  refine ⟨alwaysAbstain (X := X) (Y := Y) (W := W), alwaysAbstain_integrity (R := R), ?_⟩
  intro hComp
  rcases hScope with ⟨x, hx⟩
  rcases competent_has_coverage (R := R) (Γ := Γ)
      (Q := alwaysAbstain (X := X) (Y := Y) (W := W)) hComp x hx with ⟨y, w, hSolve⟩
  simp [alwaysAbstain] at hSolve

/-!
  Integrity-resource closure (conditional pattern):
  if universal competence would force a complexity collapse, then under
  non-collapse universal competence is impossible.
-/

/-- Integrity-Resource Bound (logical core): if universal competence implies
    a complexity collapse, then under non-collapse no universal competence
    predicate can hold. -/
theorem integrity_resource_bound
    {P_eq_coNP PolytimeUniversalCompetence : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : PolytimeUniversalCompetence → P_eq_coNP) :
    ¬ PolytimeUniversalCompetence := by
  intro hPoly
  exact hNeq (hCollapse hPoly)

/-- Integrity forces abstention or budget violation under the same
    integrity-resource obstruction:
    for any integrity-preserving solver, full in-scope coverage and declared
    budget compliance cannot both hold. -/
theorem integrity_forces_abstention
    (R : Set (X × Y)) (Γ : Regime X)
    {P_eq_coNP : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : (∃ Q : CertifyingSolver X Y W, CompetentOn R Γ Q) → P_eq_coNP) :
    ∀ Q : CertifyingSolver X Y W, SolverIntegrity R Q →
      ¬ (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w))
      ∨
      ¬ (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x)) := by
  classical
  intro Q hIntegrity
  by_contra hFail
  have hCoverage :
      ∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w) := by
    by_contra hNoCoverage
    exact hFail (Or.inl hNoCoverage)
  have hBudget :
      ∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x) := by
    by_contra hNoBudget
    exact hFail (Or.inr hNoBudget)
  have hComp : CompetentOn R Γ Q := ⟨hIntegrity, hCoverage, hBudget⟩
  have hCollapseWitness : P_eq_coNP := hCollapse ⟨Q, hComp⟩
  exact hNeq hCollapseWitness

/-- Three-way policy verdict used for the attempted-competence matrix:
    rational (conditionally justified), irrational, or inadmissible. -/
inductive OverModelVerdict where
  | rational
  | irrational
  | inadmissible
  deriving DecidableEq, Repr

/-- Attempted-competence matrix decision function.
    Axes:
    - integrity: whether assertions are integrity-preserving
    - attempted: whether exact competence was actually attempted
    - competenceAvailable: whether exact competence is available in the active regime
-/
def overModelVerdict (integrity attempted competenceAvailable : Bool) : OverModelVerdict :=
  if integrity then
    if attempted && (!competenceAvailable) then OverModelVerdict.rational
    else OverModelVerdict.irrational
  else OverModelVerdict.inadmissible

/-- Rational cell characterization for the attempted-competence matrix. -/
theorem overModelVerdict_rational_iff (integrity attempted competenceAvailable : Bool) :
    overModelVerdict integrity attempted competenceAvailable = OverModelVerdict.rational ↔
      integrity = true ∧ attempted = true ∧ competenceAvailable = false := by
  cases integrity <;> cases attempted <;> cases competenceAvailable <;> decide

/-- Irrational cell characterization for the attempted-competence matrix. -/
theorem overModelVerdict_irrational_iff (integrity attempted competenceAvailable : Bool) :
    overModelVerdict integrity attempted competenceAvailable = OverModelVerdict.irrational ↔
      integrity = true ∧ (attempted = false ∨ competenceAvailable = true) := by
  cases integrity <;> cases attempted <;> cases competenceAvailable <;> decide

/-- Inadmissible cell characterization for the attempted-competence matrix. -/
theorem overModelVerdict_inadmissible_iff (integrity attempted competenceAvailable : Bool) :
    overModelVerdict integrity attempted competenceAvailable = OverModelVerdict.inadmissible ↔
      integrity = false := by
  cases integrity <;> cases attempted <;> cases competenceAvailable <;> decide

/-- Number of rational cells in the integrity-preserving plane
    (integrity fixed to true, axes: attempted × competenceAvailable). -/
def admissibleRationalCount : Nat :=
  (((Finset.univ : Finset Bool).product (Finset.univ : Finset Bool)).filter
    (fun p => overModelVerdict true p.1 p.2 = OverModelVerdict.rational)).card

/-- Number of irrational cells in the integrity-preserving plane
    (integrity fixed to true, axes: attempted × competenceAvailable). -/
def admissibleIrrationalCount : Nat :=
  (((Finset.univ : Finset Bool).product (Finset.univ : Finset Bool)).filter
    (fun p => overModelVerdict true p.1 p.2 = OverModelVerdict.irrational)).card

/-- Count theorem for the integrity-preserving attempted-competence matrix:
    exactly one rational cell and three irrational cells. -/
theorem admissible_matrix_counts :
    admissibleRationalCount = 1 ∧ admissibleIrrationalCount = 3 := by
  native_decide

/-- In the integrity-preserving plane, irrational cells strictly outnumber rational cells. -/
theorem admissible_irrational_strictly_more_than_rational :
    admissibleIrrationalCount > admissibleRationalCount := by
  native_decide

end DecisionQuotient.IntegrityCompetence
