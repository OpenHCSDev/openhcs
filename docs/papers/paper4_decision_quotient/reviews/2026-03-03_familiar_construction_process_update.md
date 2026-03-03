# Paper 4 Process Update: Familiar Construction First

## Purpose

This note records a process correction prompted by expert feedback: before presenting a universal property as if it were sui generis, first check whether it is already a standard construction in a familiar mathematical category.

## Trigger

Tobias Fritz's feedback on the decision quotient universal property suggested that the construction should first be understood in `Set`, not framed as categorical probability.

## Updated process rule

1. Identify the carrier category before naming the abstraction.
2. Check whether the construction is already standard there:
   - image
   - coimage
   - quotient by kernel pair / equalizer relation
   - factorization through image/range
   - support of an indicator / cardinality of that support
   - normalized support fraction of a multivalued image
3. Use the familiar name in the prose if it is accurate.
4. Treat the novelty as the role the construction plays in the paper, not as the mere existence of the construction.

## Applied here

- The optimizer quotient object is the quotient of `S` by equality of `Opt`.
- In `Set`, that is the coimage of the optimizer map.
- The Lean artifact now includes the canonical equivalence between the quotient object and `range Opt`.
- The paper should therefore say:
  - the quotient object is familiar in `Set`
  - the novelty is that this coimage governs sufficiency, lower bounds, and collapse obstructions in one mechanized chain
- The structural-rank invariant should likewise be introduced in its most familiar finite form:
  - `srank` is the cardinality of the relevant-coordinate support
  - later Fisher/rate-distortion/thermodynamic theorems recover that same support-size quantity
- The decision-quotient score should be introduced as a normalized support fraction of the multivalued image of an equivalence class under `Opt`, not only as a bespoke score.

## Anti-pattern to avoid

- Do not invoke categorical probability when the theorem is not yet probabilistic.
- Do not imply a new categorical object when an existing standard construction already fits.
- Do not make readers normalize unfamiliar terminology before they have been given the familiar one.

## Acceptance criterion

For every major structural theorem in the introduction:
- the prose should first anchor it in the most familiar correct mathematical language available
- only then state what is specific to this artifact
