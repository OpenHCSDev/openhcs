# Entropy via Inflation: Comprehensive Mechanization Plan

## 1) Goal and Scope

This document lays out a full plan to formalize and publish the "entropy via inflation" line of work using the existing Paper 4 TOC machinery and Lean artifact.

Primary target:

- Prove a conditional theorem family of the form:
  - if accessible state-space grows with time,
  - and optimizer structure satisfies explicit monotonicity assumptions,
  - then optimizer-quotient entropy is nondecreasing (or strictly increasing under stronger assumptions).

Secondary target:

- Connect the above to thermodynamic lower bounds using the already-mechanized Landauer bridge, clearly separating pure-math assumptions from empirical assumptions (`k_B > 0`, `T > 0`, Landauer floor).
- Establish assumption irreducibility (minimality): each retained assumption is independently necessary for the corresponding conclusion tier.

Non-goals (for this phase):

- Claiming an unconditional cosmological proof of the Second Law from expansion alone.
- Claiming all stochastic/sequential claims are already fully mapped in current auto claim mapping.

---

## 2) Current Machinery Available (Inventory)

### 2.1 Paper and proofbase status

- Paper TOC source: `docs/papers/paper4_decision_quotient/latex_toc/decision_quotient_toc.tex`
- Core proof root: `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient`
- Build stats (auto): `docs/papers/paper4_decision_quotient/latex_toc/content/lean_stats.tex`
  - `LeanTotalLines = 33311`
  - `LeanTotalTheorems = 1378`
  - `LeanTotalSorry = 0`

### 2.2 Core module families already present

- Static decision core:
  - `Basic.lean`, `Sufficiency.lean`, `Quotient.lean`, `Information.lean`, `ThermodynamicLift.lean`
- Complexity/hardness:
  - `Hardness*.lean`, `Complexity*.lean`, `Dichotomy.lean`, `QueryComplexity.lean`
- Physics layer:
  - `Physics/LocalityPhysics.lean`, `Physics/DecisionTime.lean`, `Physics/BoundedAcquisition.lean`, `Physics/DiscreteSpacetime.lean`, `Physics/TUR.lean`, `Physics/Wolpert*.lean`, etc.
- Stochastic/sequential extension:
  - `StochasticSequential/*.lean` (hierarchy, hardness, tractability, cross-regime, info, thermo)
- Existing cosmology-expansion-focused file:
  - `Physics/TemporalCountingGap.lean`

### 2.3 Build inclusion note

- `lakefile.lean` uses `globs := #[.submodules `DecisionQuotient]`, so submodules under `DecisionQuotient/` are build-visible.
- `TemporalCountingGap.lean` is imported by export tools (`DeclInfoExport.lean`, `GraphExport.lean`) but not currently surfaced in TOC handle mapping.

---

## 3) Relevant Theorems Already Proven (for this project)

## 3.1 Decision semantics and sufficiency (set-valued)

From TOC foundations and Lean:

- `Opt(s)` is set-valued (`argmax` set), not single-action
  - LaTeX: `content/02_formal_foundations.tex` (Def. optimizer)
  - Lean: `DecisionQuotient/Basic.lean` (`DecisionProblem.Opt`)
- Sufficiency preserves full optimal-action correspondence
  - LaTeX: `content/02_formal_foundations.tex` (Def. sufficient)
  - Lean: `DecisionQuotient/Sufficiency.lean` (`isSufficient`)
- Selector-level is weaker than set-level
  - Lean witness: `DecisionQuotient/ClaimClosure.lean`
    - `selectorSufficient_not_implies_setSufficient`

Implication for inflation project:

- Your "multiple valid actions can remain under sufficiency" intuition is already compatible with the static core semantics.

## 3.2 Entropy and structural rank machinery

- Optimizer class count:
  - `DecisionProblem.numOptClasses` in `DecisionQuotient/Information.lean`
- Quotient entropy:
  - `DecisionProblem.quotientEntropy = log(numOptClasses)/log(2)` in `Information.lean`
- Entropy-rank bounds (binary coordinate case):
  - `numOptClasses_le_pow_srank_binary`
  - `quotientEntropy_le_srank_binary`

Implication:

- Entropy is already tied to optimizer image cardinality and rank support; this is the right insertion point for time-indexed growth theorems.

## 3.3 Thermodynamic bridge (Landauer-conditional)

- `ThermodynamicLift.energy_ge_kbt_nat_entropy` in `DecisionQuotient/ThermodynamicLift.lean`
  - Assumes: positive constants and lower-bound premises
  - Concludes energy lower bound tracks decision entropy in nats

Implication:

- Once entropy monotonicity is proved (under explicit assumptions), you can immediately derive monotone lower-bound consequences for energy.

## 3.4 Time, locality, and light-cone scaffolding

- Discrete unit-time event semantics:
  - `Physics/DecisionTime.lean` (`tick`, `decision_event_implies_time_unit`, run accounting)
- Light cone and causal reachability:
  - `Physics/LocalityPhysics.lean` (`lightCone`, causal past/future, locality constraints)
  - Includes `light_cone_is_time_gap`

Implication:

- The causal-access story can be formalized with existing objects rather than ad hoc new notions.

## 3.5 Existing inflation/state-growth formalization

`Physics/TemporalCountingGap.lean` already includes:

- time-indexed scale factor model (`PhysicalScaleFactor`)
- strict state-cardinality growth:
  - `state_space_strictly_increasing`
  - `states_increase_with_time`
- cost inflation and immediate-action optimality:
  - `cost_strictly_increases`, `cost_inflation`, `optimal_strategy_is_immediate`
- master theorem bundling growth/noise/logical invariance:
  - `temporal_counting_gap_master`

Implication:

- You are not starting from zero. Expansion-growth machinery exists; the missing bridge is from cardinality growth to optimizer-quotient growth.

## 3.6 Stochastic/sequential regime scaffolding

- Regime hierarchy modules exist and are mechanized.
- Important nuance: in `StochasticSequential/Basic.lean`, `StochasticSufficient` is singleton-fiber-optimal oriented (`exists a, fiberOpt = {a}`), which is stricter than static set-valued sufficiency.

Implication:

- For tie-permissive development, the static set-valued branch is currently cleaner. A later stochastic branch should add a set-valued stochastic sufficiency definition parallel to static semantics.

## 3.7 Time-indexed families: what already exists vs what is missing

There are already two time-indexed strands in the repo:

- Sequential regime (`StochasticSequential/*`): time-indexed evolution of states/policies over a fixed underlying state type per problem instance.
- Temporal counting-gap regime (`Physics/TemporalCountingGap.lean`): explicit state-cardinality growth with cosmic time (`StateSpaceCardinality`, `states_increase_with_time`).

What is still missing is not "time" itself, but an integrated optimizer-quotient bridge:

- a single dynamic object that links time-indexed accessibility/state growth to time-indexed `DecisionProblem` optimizer images,
- then proves monotonicity (or strict growth conditions) for `numOptClasses` and entropy.

---

## 4) What Is Still Missing (Exact Gap Analysis)

Despite strong machinery, there is currently no theorem in TOC or mapped handles of this form:

- `S_access(t1) <= S_access(t2)` plus decision-map assumptions
  - implies `numOptClasses(t1) <= numOptClasses(t2)`
  - implies `H(t1) <= H(t2)`.

Current blockers:

1. No canonical integrated bridge object combining:
   - sequential time semantics,
   - temporal state-space growth semantics, and
   - optimizer-quotient/entropy semantics.
2. No mechanized relation connecting expansion/access growth to optimizer-image growth.
3. No TOC-integrated handles for `TemporalCountingGap` claims (currently not surfaced in `lean_handle_ids_auto.tex` as temporal-counting handles).
4. Mixed semantics across regimes (set-valued static vs singleton-oriented stochastic definition).

---

## 5) Formal Target Theorem Stack

Define theorem stack in four layers:

### Layer A: Dynamic model definitions

- Define `DynamicDecisionModel` with:
  - `t : Nat`
  - `D t : DecisionProblem A (S t)`
  - embedding/restriction maps between `S t1` and `S t2`
  - optional "accessible slice" object `Sacc t` (for infinite-global settings)

### Layer B: Structural monotonicity assumptions

Add explicit assumptions; do not hide any:

- `A1` (state inclusion): `Sacc t1` embeds into `Sacc t2` for `t1 <= t2`
- `A2` (optimizer extension consistency): old states preserve old optimal sets under embedding
- `A3` (non-collapse of new distinctions, optional for strictness): at some later time, at least one new optimizer class appears

### Layer C: Entropy monotonicity theorems

- `T_mono_classes`: `numOptClasses(t1) <= numOptClasses(t2)` under `A1+A2`
- `T_mono_entropy`: `H(t1) <= H(t2)` from log monotonicity
- `T_strict_entropy` (conditional): strict inequality under `A3`

### Layer D: Thermodynamic corollaries

Compose with existing theorem:

- from `H(t1) <= H(t2)` and `energy_ge_kbt_nat_entropy`, derive monotone lower-bound consequences on required energy floor (with declared assumptions).

### Layer E: Assumption irreducibility (minimality)

For each theorem tier, prove assumption-set minimality via independence witnesses:

- `M1` (weak monotonicity minimality): dropping any required structural assumption can break `numOptClasses`/entropy nondecrease.
- `M2` (strict growth minimality): strict-growth witness assumptions are necessary for strict entropy increase.
- `M3` (thermo corollary minimality): dropping physical positivity/floor assumptions can break nontrivial energy lower-bound conclusions.

---

## 6) Implementation Plan (Lean + Paper)

## Phase 0: Branch and document assumptions

Deliverables:

- Create a short assumptions ledger specific to inflation-entropy bridge.
- Split assumptions into:
  - pure structural (set maps, monotonicity)
  - empirical (`k_B > 0`, `T > 0`, Landauer floor)

## Phase 0.5: Irreducibility target matrix

Deliverables:

- Create an assumption-to-conclusion matrix for three tiers:
  - entropy nondecrease,
  - strict entropy increase,
  - thermodynamic lower-bound corollaries.
- Mark each assumption as:
  - required for theorem statement,
  - candidate removable,
  - to-be-tested by countermodel.

## Phase 1: Introduce dynamic decision object

Suggested new file:

- `proofs/DecisionQuotient/InflationEntropyBridge.lean`

Add:

- `structure DynamicDecisionModel`
- time-indexed `numOptClassesAt`, `entropyAt`
- embeddings/restrictions with compatibility lemmas

## Phase 2: Prove class monotonicity core

Prove:

- image/cardinality monotonic lemmas under embedding consistency
- theorem: `classes_monotone`.

Proof strategy:

- factor through existing `DecisionProblem.numOptClasses` definition,
- use finite image-cardinality monotonicity under injective map and consistency.

## Phase 3: Prove entropy monotonicity

Prove:

- `entropy_monotone` from `classes_monotone` and monotonicity of `Real.log` over positive reals.

Reuse:

- positivity lemmas around `numOptClasses_pos` from `Information.lean`.

## Phase 4: Strict increase criteria

Add an explicit witness condition for strict growth:

- existence of a new optimizer class at `t2` not present at `t1`.

Prove:

- `classes_strict_increase`
- `entropy_strict_increase`.

## Phase 5: Connect to existing cosmology module

Bridge `TemporalCountingGap` to dynamic decision model assumptions:

- convert state-space growth theorems (`states_increase_with_time`) into existence of larger accessible slices,
- avoid asserting optimizer-class growth from cardinality growth alone unless extra assumptions are declared.

## Phase 6: Thermodynamic composition

Prove corollaries composing new entropy monotonicity with:

- `ThermodynamicLift.energy_ge_kbt_nat_entropy`.

This yields a clean conditional statement:

- structural entropy growth + Landauer assumptions => growing lower-bound pressure on decision energy.

## Phase 6.5: Assumption minimality proofs

For each assumption `Ai`, mechanize an independence witness:

- hold all `Aj` (`j != i`), violate `Ai`, and show target conclusion fails.

Recommended proof pattern:

1. Main theorem under full bundle `A`.
2. For each `Ai`, theorem `not_redundant_Ai` with explicit countermodel.
3. Bundle theorem: no proper subset of `A` proves the same conclusion schema.

Suggested split:

- Structural minimality in the dynamic bridge module.
- Physical-premise minimality in thermo composition module.

## Phase 7: TOC integration and handle mapping

Files to update:

- `latex_toc/content/02a_physical_grounding.tex` (or a new subsection file)
- `latex_toc/content/02_formal_foundations.tex` (dynamic model defs, if needed)
- `latex_toc/content/10_lean_4_proof_listings.tex` (new handle mention)

Ensure claim mapping picks up new theorems:

- regenerate `lean_handle_ids_auto.tex`
- regenerate `claim_mapping_auto.tex`
- verify no unintended unmapped inflation claims remain.

## Phase 8: Stochastic/sequential alignment pass

Optional but recommended:

- Introduce a set-valued stochastic sufficiency variant parallel to static semantics.
- Keep singleton variant as a stricter sub-definition.
- Add bridge theorem: set-valued stochastic sufficiency implies singleton sufficiency only under uniqueness conditions.

---

## 7) Concrete Lean Theorem Skeletons (proposed)

```lean
structure DynamicDecisionModel (A : Type*) where
  T : Type
  time : T
  State : T → Type
  dp : (t : T) → DecisionProblem A (State t)
  -- plus finite/cardinality assumptions on accessible slices

theorem classes_monotone
  (M : DynamicDecisionModel A)
  (hEmbed : ...)
  (hCompat : ...) :
  numOptClassesAt M t1 ≤ numOptClassesAt M t2 := ...

theorem entropy_monotone
  (M : DynamicDecisionModel A)
  (hClasses : numOptClassesAt M t1 ≤ numOptClassesAt M t2) :
  entropyAt M t1 ≤ entropyAt M t2 := ...

theorem entropy_strict_of_new_class
  (M : DynamicDecisionModel A)
  (hNew : ∃ c, c ∈ classesAt M t2 ∧ c ∉ classesAt M t1) :
  entropyAt M t1 < entropyAt M t2 := ...
```

---

## 8) Validation and Verification Checklist

Proof checks:

- `lake build` at `docs/papers/paper4_decision_quotient/proofs`
- `CheckAxioms.lean` extended with new bridge theorems
- no `sorry`

Paper checks:

- theorem labels and `\leanmeta{}` handles compile
- new claims appear in `claim_mapping_auto.tex`
- claim statuses for new inflation bridge are `Full`, not `Unmapped`

Logical checks:

- every strict monotonicity statement has an explicit witness assumption
- no leap from "more states" to "more optimizer classes" without declared condition
- clear separation between:
  - structural claims,
  - empirical premises,
  - conjectural extensions.
- each theorem tier has an explicit irreducibility check (or an explicit reason why minimality is not claimed).

---

## 9) Risks and Mitigations

Risk 1: Over-claim from cardinality growth to entropy growth

- Mitigation: require explicit optimizer-compatibility/non-collapse assumptions.

Risk 2: Semantic drift between static and stochastic sufficiency notions

- Mitigation: define and use a clearly named set-valued stochastic notion for bridge theorems.

Risk 3: TemporalCountingGap not reflected in TOC handles

- Mitigation: add explicit handle exports and cite them in LaTeX sections.

Risk 4: Theorem explosion without integration

- Mitigation: enforce a minimal theorem chain that ends in one headline theorem plus two corollaries.

---

## 10) Definition of Done

Done means all of the following are true:

1. New dynamic decision model and monotonicity theorems are fully mechanized.
2. Entropy monotonicity theorem is proved with transparent assumptions.
3. Thermodynamic corollary is proved by composition with existing Landauer bridge.
4. New claims are integrated into TOC LaTeX and mapped in auto claim mapping.
5. `lake build` passes; `sorry = 0`; axiom audit unchanged except expected classical/kernel axioms.
6. Paper text explicitly distinguishes:
   - proved theorem,
   - conditional theorem,
   - conjectural cosmological interpretation.
7. Assumption irreducibility is addressed:
   - either fully mechanized independence/minimality theorems are present,
   - or a scoped statement declares exactly which assumptions are not yet proven minimal.

---

## 11) Recommended Execution Order (practical)

1. Implement `InflationEntropyBridge.lean` with minimal dynamic definitions.
2. Prove `classes_monotone` and `entropy_monotone` first (no strictness yet).
3. Add strictness theorem with explicit "new class appears" witness.
4. Compose with `energy_ge_kbt_nat_entropy`.
5. Only then wire to `TemporalCountingGap` and causal-access language.
6. Update LaTeX and regenerate auto mapping.

This order keeps the core theorem mathematically clean and avoids cosmology-specific complexity until the bridge is already stable.

---

## 12) Assumption Irreducibility Matrix (working draft)

This matrix is the concrete Phase 0.5 artifact. It separates theorem tiers from assumptions and pre-commits the minimality checks.

### 12.1 Assumption IDs

- `A1` (state embedding monotonicity): for `t1 <= t2`, accessible states at `t1` embed into accessible states at `t2`.
- `A2` (optimizer compatibility on embedded states): old states preserve `Opt` under embedding.
- `A3` (new optimizer class witness): some class appears at later time not present earlier.
- `F1` (finite accessible slice): each `Sacc t` is finite (`Fintype`) so `numOptClasses` is defined.
- `F2` (nonempty accessible slice): each `Sacc t` is nonempty when entropy positivity lemmas are used.
- `P1` (`k_B > 0`): Boltzmann positivity premise.
- `P2` (`T > 0`): positive temperature regime premise.
- `P3` (Landauer floor): per-bit energetic lower-bound premise.

### 12.2 Assumption-to-theorem matrix

Legend: `Req` = required, `Cond` = only for strict version, `-` = not needed.

| Assumption | `T_mono_classes` | `T_mono_entropy` | `T_strict_entropy` | `T_energy_floor_mono` | `T_energy_floor_strict` |
|---|---|---|---|---|---|
| `A1` | Req | Req | Req | Req | Req |
| `A2` | Req | Req | Req | Req | Req |
| `A3` | - | - | Cond | - | Cond |
| `F1` | Req | Req | Req | Req | Req |
| `F2` | - | Req | Req | Req | Req |
| `P1` | - | - | - | Req | Req |
| `P2` | - | - | - | Req | Req |
| `P3` | - | - | - | Req | Req |

### 12.3 Countermodel strategy matrix (for irreducibility)

Each row is the planned witness for `not_redundant_*` theorems.

| Assumption to drop | Keep | Violate | Planned countermodel idea | Expected failure |
|---|---|---|---|---|
| `A1` | `A2,F1,F2` | no embedding relation | unrelated state families at `t1,t2` | cannot prove class monotonicity (can reverse) |
| `A2` | `A1,F1,F2` | embedding exists but flips old preferences | utility perturbation on embedded old states | old class image not preserved |
| `A3` (strict only) | `A1,A2,F1,F2` | no genuinely new class | larger state set mapped into existing classes only | strict entropy increase fails (only nondecrease) |
| `F1` | `A1,A2` | infinite/untyped cardinal context | no finite card for class count object | theorem statement ill-typed or unavailable |
| `F2` (entropy lemmas) | `A1,A2,F1` | empty accessible slice | class positivity/log lemmas unavailable | entropy theorem side conditions fail |
| `P1` | `P2,P3` + structural | set `k_B = 0` | degenerate thermal scale | positive energy-floor consequence collapses |
| `P2` | `P1,P3` + structural | set `T = 0` | zero-temperature edge regime | positive lower-bound corollary collapses |
| `P3` | `P1,P2` + structural | remove per-bit floor premise | no energetic link from entropy bits | thermo corollary not derivable |

### 12.4 Minimality theorem names (planned)

- `not_redundant_A1_for_mono_classes`
- `not_redundant_A2_for_mono_classes`
- `not_redundant_A3_for_strict_entropy`
- `not_redundant_F1_for_class_entropy_statements`
- `not_redundant_F2_for_entropy_log_statements`
- `not_redundant_P1_for_positive_energy_floor`
- `not_redundant_P2_for_positive_energy_floor`
- `not_redundant_P3_for_energy_from_entropy_bridge`

### 12.5 Practical order for minimality proofs

1. Structural first: `A1`, `A2`, `A3`.
2. Typing/positivity side conditions: `F1`, `F2`.
3. Physical-premise minimality: `P1`, `P2`, `P3`.

This order keeps countermodels simple and avoids mixing algebraic and physical failure modes too early.
