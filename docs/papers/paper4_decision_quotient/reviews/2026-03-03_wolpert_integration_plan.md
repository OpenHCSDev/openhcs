# Wolpert Integration Plan for Paper 4

## Context

The bridge theorem is now formalized separately. The next diff should be the
Wolpert-facing thermodynamic refinement only.

The goal is not to rederive the full stochastic-thermodynamics machinery of the
cited papers. The goal is to mechanize the specific interface claims that matter
for this artifact:

1. Landauer is a minimum floor, not a generally tight actual-cost law.
2. Real constrained computational processes incur additional entropy production
   above that floor.
3. That additional irreversibility can be represented as a nonnegative overhead
   term, with a strictly positive overhead under stated process constraints.
4. The existing decision-theoretic and hardness-to-energy lower bounds remain
   valid and tighten monotonically under that stronger empirical premise.

This keeps the integration rigorous and honest: the external thermodynamic
results are cited as empirical/theoretical inputs, and the composition with the
existing Lean machinery is what gets fully mechanized.

## Source Papers and Relevant Extracted Claims

### 1. Wolpert et al. (PNAS 2024)

`Is stochastic thermodynamics the key to understanding the energy costs of computation?`

Relevant claims:

- Landauer's bound is only saturated when there are no constraints on the
  processes available to implement the computation.
- Real computers are constrained by finite-time operation, periodic driving,
  modularity, and hierarchy.
- Those constraints imply nonzero irreversible entropy production above the
  Landauer floor.
- Mismatch cost is one explicit source of that additional entropy production.

This paper is the cleanest source for the high-level physical interpretation:
Landauer gives a floor; constrained computation generically dissipates more.

### 2. Manzano et al. (Phys. Rev. X 2024)

`Thermodynamics of Computations with Absolute Irreversibility, Unidirectional Transitions, and Stochastic Computation Times`

Relevant claims:

- They derive lower and upper bounds on intrinsic dissipation (mismatch cost)
  for periodic processes.
- These bounds apply even with stochastic stopping times, absolute
  irreversibility, and unidirectional transitions.
- The computational setting they analyze explicitly includes the periodic
  processes underlying digital computation.

This paper is the strongest support for using a nonnegative (and in constrained
regimes, strictly positive) extra dissipation term while still talking about
real computational processes rather than idealized bit erasure alone.

### 3. Yadav, Yousef, Wolpert (arXiv 2026)

`Minimal Thermodynamic Cost of Computing with Circuits`

Relevant claims:

- Mismatch cost yields lower bounds on entropy production for repeated circuit
  operation.
- In circuits, modular structure itself contributes to mismatch-cost lower
  bounds.
- Mismatch cost is positioned as a thermodynamic resource cost, not merely an
  implementation detail.

This paper is the direct architecture-level bridge: modular circuit structure
can force positive lower bounds above the Landauer floor.

### 4. Van den Broeck & Esposito (Physica A 2015)

`Ensemble and trajectory thermodynamics: A brief introduction`

Relevant claims:

- Stochastic thermodynamics gives the modern entropy-production framework for
  nonequilibrium processes on discrete-state Markov systems.
- Entropy production is the relevant irreversible-dissipation object.

This paper functions as foundational background, not as the source of the
Wolpert-specific correction. It justifies the language of entropy production and
nonequilibrium cost.

## What Already Exists in Lean

### Current usable infrastructure

- `DecisionQuotient/ThermodynamicLift.lean`
  - `landauerJoulesPerBit`
  - `joulesPerBit_pos_of_landauer_floor`
  - `joulesPerBit_exceeds_landauer_of_positive_overhead`
  - floor-based and exact-calibration specializations

- `DecisionQuotient/Physics/BoundedAcquisition.lean`
  - the discrete counting theorem
  - the physical grounding bundle that uses the declared per-bit lower bound

- `DecisionQuotient/Bridges.lean`
  - prose-level and handle-level bridge language already refers to the
    Landauer floor and entropy-production consequences

### Current gap

The current Lean treats the extra term generically as an unnamed positive
overhead:

- this is mathematically sound
- but it does not yet encode the cited structure explicitly
- it does not distinguish:
  - unconstrained idealized process
  - constrained periodic/modular/finite-time process

That is the missing interface.

## What Should Be Mechanized Next

### New module

Create:

- `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/Physics/WolpertConstraints.lean`

### Scope

This module should formalize the *assumption interface*, not the internal
derivations of the cited papers.

It should introduce a small declared structure for process constraints and
overhead, then prove the consequences that matter to this artifact.

### Proposed formal objects

#### 1. Constrained computation overhead model

A structure expressing:

- a declared Landauer floor
- a declared nonnegative extra dissipation term
- optionally, named premises for:
  - periodic operation
  - modular architecture
  - finite-time or stopping-time regime

The important point is that the overhead term is explicit and typed.

#### 2. Floor-plus-overhead cost law

The main empirical interface theorem should say:

- actual per-bit lower bound = Landauer floor + overhead
- with overhead `>= 0`

This should then imply:

- actual per-bit lower bound `>=` Landauer floor

#### 3. Strict-overhead specialization

A second theorem should state:

- under a declared constrained-process regime (for example periodic or modular),
  if the cited premise supplies strictly positive overhead, then the actual
  per-bit lower bound is strictly greater than the Landauer floor

This is the theorem that should replace the current generic unnamed
`positive_overhead` interpretation in the Wolpert-facing diff.

#### 4. Monotone tightening lemmas

Prove explicitly that:

- all existing energy lower bounds in `ThermodynamicLift.lean`
  monotonically tighten when the per-bit lower bound is increased
- the physical grounding bundle in `BoundedAcquisition.lean` remains valid under
  the stronger floor-plus-overhead premise

These should be direct composition theorems, not restatements in comments.

## Handle Plan

Add a new handle family in `HandleAliases.lean`:

- `WC1`: floor-plus-overhead lower bound
- `WC2`: nonnegative overhead implies Landauer-floor dominance
- `WC3`: positive constrained-process overhead implies strict separation above
  Landauer
- `WC4`: monotone tightening of the mandatory energy lower bound
- `WC5`: monotone tightening of the physical grounding bundle

The existing `TL*` theorems should remain, but the new `WC*` family should
become the paper-facing way to cite the Wolpert refinement.

## Prose Update Plan

### Files to update after the Lean module compiles

- `latex_toc/content/abstract.tex`
- `latex_toc/content/02a_physical_grounding.tex`
- `latex_toc/content/08_related_work.tex`
- `latex_toc/content/09_conclusion.tex`

### Required prose changes

1. Replace any remaining generic “positive overhead” wording with:
   - a cited floor-plus-overhead formulation
2. State clearly that:
   - the extra term is a declared lower-bound premise justified by the cited
     literature
   - the Lean mechanizes the composition of that premise with the existing
     decision-theoretic lower bounds
3. In related work:
   - distinguish the four roles explicitly:
     - stochastic-thermodynamics foundation
     - constrained-computation perspective
     - periodic/stopping-time mismatch bounds
     - circuit/modularity mismatch-cost lower bounds

## What Not to Do

1. Do not try to mechanize the full CTMC or martingale framework now.
2. Do not claim to have rederived Wolpert’s internal proofs.
3. Do not replace the current conservative floor theorem with a stronger claim
   unless the new Lean theorem states it directly.
4. Do not cite the new module as if it proves the external physics from first
   principles; it proves the composition with this artifact.

## Implementation Order

1. Add `Physics/WolpertConstraints.lean`
2. Import it into:
   - `DecisionQuotient.lean`
   - `HandleAliases.lean`
   - `CheckAxioms.lean`
3. Prove the `WC*` theorems
4. Rebuild Lean
5. Update prose to cite `WC*`
6. Rebuild `paper4_toc`
7. Commit as a separate Wolpert-facing diff

## Acceptance Criteria

1. The Lean names the Wolpert-style floor-plus-overhead interface explicitly.
2. The main physical claim is no longer a generic unnamed positive-overhead
   statement.
3. The paper cites the four Wolpert-related papers with distinct roles.
4. `python3 scripts/build_papers.py lean paper4_toc` passes.
5. `python3 scripts/build_papers.py latex paper4_toc` passes.
6. The resulting diff clearly shows:
   - the cited empirical refinement
   - the new theorems
   - the unchanged downstream mechanical validity
