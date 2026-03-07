# Entropy-via-Inflation: Dry-Run Gap Catalog

## 0) What was actually dry-run

I added and type-checked a dedicated dry-run scaffold:

- `docs/papers/paper4_decision_quotient/proofs/InflationEntropyDryRun.lean`

Validation command run:

- `lake env lean InflationEntropyDryRun.lean` (from `docs/papers/paper4_decision_quotient/proofs`)

Result:

- Type-check succeeds.

This was used to test whether the core bridge shape is mechanically reachable with current machinery.

Update (implementation started):

- Production module created and integrated:
  - `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/InflationEntropyBridge.lean`
- Core import wired into:
  - `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient.lean`
- Build checks run successfully:
  - `lake build DecisionQuotient.InflationEntropyBridge`
  - `lake env lean DecisionQuotient.lean`

So the bridge is no longer only conceptual/dry-run; first theorem layer is now mechanized in a production module.

Further implementation completed:

- Added dynamic-family production theorem stack in
  `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/InflationEntropyBridge.lean`:
  - `classes_monotone`
  - `entropy_monotone`
  - `classes_strict_increase`
  - `entropy_strict_increase`
  - `thermal_floor_monotone_of_classes`
  - `thermal_floor_strict_of_new_class`
  - `later_energy_floor_implies_earlier_floor`
  - `optCompat_of_utilityCompat`
  - `classes_monotone_of_utilityCompat`
  - `entropy_monotone_of_utilityCompat`
- Added irreducibility witness module:
  `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/InflationEntropyMinimality.lean`
  - `not_redundant_A2_for_mono_classes`
  - `not_redundant_A3_for_strict_entropy`
  - `not_redundant_P1_for_positive_floor`
  - `not_redundant_P2_for_positive_floor`
  - `not_redundant_A1_for_mono_classes_weak`
  - `not_redundant_F1_for_finite_counting_requirement`
  - `not_redundant_F2_for_numOptClasses_pos`
  - `not_redundant_P3_for_energy_from_entropy_bridge`
- Added temporal utility-family adapter in bridge module:
  - `TemporalUtilityFamily`
  - `temporal_classes_monotone_of_utilityCompat`
  - `temporal_entropy_monotone_of_utilityCompat`
- Added IEB handle aliases (`IEB1`--`IEB15`) in
  `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/HandleAliases.lean`.
- Added stochastic set-valued bridge module:
  `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/StochasticSequential/SetValued.lean`
  - `stochasticSetSufficient_universal`
  - `stochasticSufficient_implies_setSufficient`
- Wired imports into `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient.lean`.
- Extended axiom audit in `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/CheckAxioms.lean` for all new inflation/minimality theorems.

Build/audit status:

- `lake build DecisionQuotient` succeeds.
- `lake env lean DecisionQuotient/CheckAxioms.lean` succeeds and reports only existing kernel/classical axioms (`propext`, `Classical.choice`, `Quot.sound`) for new theorems.

---

## 1) Dry-run theorems that already go through

## 1.1 Optimizer-class monotonicity from embedding-compatibility

Proved in dry-run:

- `numOptClasses_mono_of_embedding`

Statement shape:

- Given `emb : S1 -> S2` and
- `hOptCompat : forall s, (dp2.Opt (emb s) = dp1.Opt s)`,
- conclude `dp1.numOptClasses <= dp2.numOptClasses`.

Interpretation:

- The image-cardinality monotonicity piece is already straightforward in Lean.

## 1.2 Entropy monotonicity from class monotonicity

Proved in dry-run:

- `quotientEntropy_mono_of_embedding`

Statement shape:

- Adds `Nonempty` assumptions for class positivity,
- uses `Real.log` monotonicity,
- concludes `dp1.quotientEntropy <= dp2.quotientEntropy`.

Interpretation:

- Once class monotonicity is in hand, entropy monotonicity is not a blocker.

## 1.3 Time-growth gives explicit state embeddings (cardinality-level)

Proved in dry-run:

- `TemporalBridge.embedState`
- `TemporalBridge.embedState_injective`

Built from existing theorem:

- `states_nondecreasing` in `Physics/TemporalCountingGap.lean`

Interpretation:

- Temporal state-cardinality growth can already be turned into concrete `Fin`-state embeddings.

---

## 2) Exact remaining gaps (hard blockers and soft blockers)

Below, each gap includes multiple strategy options.

Status legend:

- `Done` = mechanized and integrated.
- `Partial` = core theorem done; publication/mapping/generalization still open.
- `Open` = not yet mechanized.

## Gap A: No integrated dynamic decision family object (`Done`)

Current state:

- You have static decision objects (`DecisionProblem A S`) and separate temporal growth objects (`StateSpaceCardinality`), but no canonical bundled `D_t` object in core modules.

Why it blocks:

- The final theorem should quantify over time-indexed decision problems and their compatibility maps.

Strategies:

1. **Minimal bridge object (recommended first):**
   - Add `structure DynamicDecisionFamily` with fields:
     - `State : Nat -> Type`
     - `dp : (t : Nat) -> DecisionProblem A (State t)`
     - embeddings for `t1 <= t2`
     - functor-like laws (identity/composition)
2. **Slice-based object:**
   - Keep a fixed global state type and define `Accessible t : Set S_global`.
   - Define `dp_t` by restriction to `Accessible t`.
3. **Sigma-time object:**
   - Use single state type `Sigma t, State t`.
   - Encode time-evolution as subproblem projections.

Tradeoff:

- (1) is easiest to prove with cardinality/image lemmas.

## Gap B: Missing optimizer-compatibility law derivation (`Done`)

Current state:

- Dry-run monotonicity theorem requires explicit assumption:
  - `forall s, (dp t2).Opt (embed s) = (dp t1).Opt s`.
- TemporalCountingGap does not produce this law.

Why it blocks:

- State growth alone does not logically force optimizer-image growth or preservation.

Strategies:

1. **Assume compatibility axiomatically (clean conditional theorem):**
   - Publish theorem as conditional on `Opt`-compatibility.
2. **Derive compatibility from utility extension law:**
   - Assume utility extension: old-state utilities unchanged under embedding.
   - Prove this implies `Opt`-compatibility.
3. **Constructive extension model:**
   - Define `utility_t2` as extension of `utility_t1` on embedded states.
   - Then prove compatibility by construction.
4. **Bounded perturbation variant:**
   - Allow bounded utility perturbation and prove epsilon-compatibility.

Tradeoff:

- (2)/(3) are strongest mathematically; (1) is fastest for first theorem.

## Gap C: Strict increase requires a witness condition (`Done`)

Current state:

- Monotonic nondecrease is easy with embedding+compatibility.
- Strict entropy increase is not automatic.

Why it blocks:

- New states can map to old optimizer classes; then class count is unchanged.

Strategies:

1. **Existential new-class witness (recommended):**
   - Assume there exists a state at `t2` whose `Opt` set is not in embedded old image.
   - Prove strict class growth and strict entropy growth.
2. **Surjective-failure criterion:**
   - Show image of class map from `t1` to `t2` is proper subset.
3. **Lower-bound growth criterion:**
   - Prove at least `k` new classes from structural assumptions (harder, stronger).

## Gap D: TemporalCountingGap uses cardinalities, not decision utilities (`Partial`)

Current state:

- `TemporalCountingGap.lean` gives state-growth/cost-growth/noise structure.
- It does not define a corresponding `DecisionProblem` family tied to that growth.

Why it blocks:

- No direct path from `StateSpaceCardinality` theorem to `numOptClasses` theorem.

Progress update:

- A temporal adapter now exists (`TemporalUtilityFamily` in `InflationEntropyBridge.lean`) that lifts temporal-cardinality state indexing into dynamic utility/decision families.
- Remaining gap is not the adapter itself; it is model-specific instantiation of `dpAt` for your intended physical semantics.

Strategies:

1. **Add a bridging section inside `TemporalCountingGap.lean`:**
   - Define `StateAt t := Fin (StateSpaceCardinality ...)`.
   - Introduce `dpAt t` plus utility-extension assumptions.
2. **Keep bridge in separate file (recommended):**
   - New module `InflationEntropyBridge.lean` imports TemporalCountingGap and Information.
   - Keeps cosmology and optimizer algebra decoupled.
3. **Translate via accessibility slices in physics layer:**
   - Use light-cone/access predicates as state filters before decision layer.

## Gap E: Sequential regime is time-indexed but fixed-state-type per instance (`Open`)

Current state:

- Sequential machinery already exists, but its central object has fixed `S` type with horizon dynamics.

Why it blocks:

- Inflation bridge needs type-level or slice-level growth in accessible state domain across `t`.

Strategies:

1. **Adapter theorem:**
   - Build theorem translating sequential trajectories into dynamic family slices.
2. **Refactor sequential to indexed-state generalization:**
   - Introduce generalized sequential object `S t`.
3. **Do not refactor now (recommended):**
   - Treat sequential as orthogonal, prove inflation bridge in static-to-dynamic family first.

## Gap F: Static set-valued sufficiency vs stochastic singleton sufficiency mismatch (`Partial`)

Current state:

- Static core allows ties naturally (`Opt` as set).
- Stochastic `StochasticSufficient` currently encodes singleton fiber-optimal condition.

Why it matters:

- Your argument about "multiple valid answers" aligns with static semantics.
- Cross-regime unification currently has semantic friction.

Strategies:

1. **Add set-valued stochastic sufficiency variant (recommended):**
   - Preserve existing singleton notion as strict subcase.
2. **Bridge theorem:**
   - show singleton iff set-valued + uniqueness condition.
3. **Document regime distinction explicitly:**
   - keep both, avoid hidden conflation.

Progress update:

- A set-valued stochastic sufficiency layer is now explicitly formalized in `StochasticSequential/SetValued.lean`.
- Remaining work is to tighten the notion to a nontrivial bridge notion that is neither tautological nor strictly singleton-only, and then align paper claim labels to it.

## Gap G: Infinite/global vs finite/accessible semantics not unified yet (`Open`)

Current state:

- Existing entropy machinery uses `Fintype` state spaces.

Why it blocks:

- Cosmology discussion naturally raises infinite-space concerns.

Strategies:

1. **Accessible finite slice approach (recommended now):**
   - Keep theorem finite over `S_access(t)`.
2. **Measure-theoretic extension later:**
   - Extend to sigma-finite spaces and measurable optimizer partitions.
3. **Horizon-entropy track as separate branch:**
   - treat cosmological horizon entropy separately from decision-quotient entropy.

## Gap H: Claim-handle integration for temporal-counting bridge (`Partial`)

Current state:

- TemporalCountingGap claims are not currently surfaced in TOC handle auto tables under matching temporal handles.

Why it blocks publication clarity:

- Even if theorem exists, unmapped claims look ungrounded in paper artifacts.

Strategies:

1. Add explicit Lean handle aliases for new bridge theorems. (Done in `HandleAliases.lean`.)
2. Add `\leanmeta{}` anchors in relevant TOC section(s).
3. Regenerate auto files and verify mapping status goes to `Full`.

## Gap I: Axiom audit extension not yet updated (`Done`)

Current state:

- Existing `CheckAxioms.lean` does not print new bridge theorem axioms.

Why it matters:

- You want strict rigor and transparent premise boundaries.

Strategies:

1. Add `#print axioms` lines for new bridge theorems.
2. Verify no unintended non-kernel axioms enter.

---

## 3) Proof-path feasibility verdict from dry run

Verdict: **highly feasible**.

Reason:

- The mathematically hard-looking pieces are now confirmed routine in Lean once compatibility assumptions are explicit.
- The true remaining work is architectural and semantic integration (object design + assumptions + claim mapping), not raw proof impossibility.

---

## 4) Recommended theorem roadmap (post dry run)

Order that minimizes risk:

1. Add `DynamicDecisionFamily` in new `InflationEntropyBridge.lean`.
2. Port dry-run theorems into library-quality names:
   - class monotonicity,
   - entropy monotonicity,
   - strict growth via witness.
3. Add compatibility-derivation theorem from utility-extension assumptions.
4. Add finite accessible-state adapter from `TemporalCountingGap`.
5. Compose with `ThermodynamicLift.energy_ge_kbt_nat_entropy` for energy-floor corollaries.
6. Wire handles into TOC and regenerate claim mappings.

---

## 5) Short list of exact statements to implement next

1. `numOptClasses_mono_of_OptCompat` (general dynamic family form)
2. `quotientEntropy_mono_of_OptCompat`
3. `numOptClasses_strict_of_new_class_witness`
4. `quotientEntropy_strict_of_new_class_witness`
5. `OptCompat_of_utility_extension` (bridge lemma)
6. `energy_floor_mono_of_entropy_mono` (composition corollary)

These six statements will close the main formal gap with minimal conceptual overhead.

---

## 6) Exhaustion boundary (current session)

Implemented-to-date covers the core bridge and first irreducibility witnesses. Remaining work is now mostly scope-expansion rather than local proof blockage.

Remaining items not fully implemented yet:

- Full minimality for all matrix assumptions in the strongest (same-structure) form.
  - `A1` is currently witnessed in a weak/no-embedding family (`not_redundant_A1_for_mono_classes_weak`), not yet as an internal theorem over the full dynamic-family structure.
  - `F1`/`F2` are currently witnessed via weakened requirement theorems (`not_redundant_F1_for_finite_counting_requirement`, `not_redundant_F2_for_numOptClasses_pos`) rather than internalized variants of the main bridge theorem.
- `P3` witness is now present (`not_redundant_P3_for_energy_from_entropy_bridge`), but a tighter statement directly parameterized by a Landauer-floor assumption schema is still desirable.
- Sequential/stochastic semantic unification (set-valued stochastic sufficiency bridge).
- Sequential/stochastic semantic unification (strong, non-degenerate bridge version beyond the current set-valued baseline).
- Infinite/measure-theoretic extension (beyond finite accessible slices).
- TOC claim-handle publication pass (`lean_handle_ids_auto.tex`, `claim_mapping_auto.tex`) for new IEB handles.

Conclusion:

- No local proof obstacle remains for the finite conditional bridge stack.
- Remaining effort is architectural/generalization/publication integration work.
