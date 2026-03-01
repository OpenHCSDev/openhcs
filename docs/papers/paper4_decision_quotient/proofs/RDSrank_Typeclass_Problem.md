# RDSrank.lean Typeclass Instance Problem

## Problem Summary

Trying to prove `equiv_preserves_decision` in `DecisionQuotient/Information/RDSrank.lean`:
- **Goal**: Show that states agreeing on relevant coordinates have the same optimal action
- **Status**: `sorry` placeholder - needs proof
- **Blocker**: Typeclass instance resolution problem when using `relevantSet_isSufficient`

## What We Tried

### Attempt 1: Direct use of existing machinery
```lean
theorem equiv_preserves_decision [ProductSpace S n] (dp : DecisionProblem A S)
    (hinj : ∀ s s' : S, (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s')
    (s₁ s₂ : S) (h : decisionEquiv dp s₁ s₂) :
    dp.Opt s₁ = dp.Opt s₂ := by
  have hsuff : dp.isSufficient (relevantCoords dp) :=
    relevantSet_isSufficient dp hinj  -- Type mismatch error
```

**Error**: Type mismatch between `Finset.univ.filter dp.isRelevant` (expected by theorem) and `relevantCoords dp` (which is `Finset.univ.filter (fun i => dp.isRelevant i)`).

### Attempt 2: Fix definitional equality
Added explicit equality proof:
```lean
have h_eq : relevantCoords dp = Finset.univ.filter dp.isRelevant := by
  simp [relevantCoords, Finset.filter]
  rfl
```

Still got type mismatch because of instance issues.

### Attempt 3: Add import for Information.lean
Added `import DecisionQuotient.Information` to bring `relevantSet_isSufficient` into scope.

**New Error**: Application type mismatch. The theorem `relevantSet_isSufficient` has type using `ProductSpace.toCoordinateSpace` but the context has a different `CoordinateSpace` instance.

### Attempt 4: Change variable declaration
Changed from `[CoordinateSpace S n]` to `[ProductSpace S n]` in the variable declaration.

**New Error**: Stuck typeclass instance problem at theorem signature line 82. Lean can't find `CoordinateSpace.proj` when processing the `hinj` parameter.

### Attempt 5: Add explicit instance
```lean
haveI : CoordinateSpace S n := inferInstance
```

Still stuck at theorem signature (before proof body).

## Problem Space

### Typeclass Hierarchy
```lean
class CoordinateSpace (S : Type*) (n : outParam ℕ) where
  Coord : Fin n → Type*
  proj : S → (i : Fin n) → Coord i

class ProductSpace (S : Type*) (n : ℕ) extends CoordinateSpace S n where
  replace : S → (i : Fin n) → S → S
  replace_proj_eq : ...
  replace_proj_ne : ...
```

`ProductSpace` extends `CoordinateSpace`, so any `ProductSpace` instance should provide a `CoordinateSpace` instance.

### Theorem We Want to Use

In `DecisionQuotient/Information.lean`:
```lean
theorem relevantSet_isSufficient [DecidableEq (Fin n)] [ProductSpace S n]
    (dp : DecisionProblem A S)
    (hinj : ∀ s s' : S, (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s') :
    dp.isSufficient (Finset.univ.filter dp.isRelevant)
```

This theorem proves exactly what we need: the set of relevant coordinates is sufficient for the decision problem.

### Our Theorem

```lean
theorem equiv_preserves_decision [ProductSpace S n] (dp : DecisionProblem A S)
    (hinj : ∀ s s' : S, (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s')
    (s₁ s₂ : S) (h : decisionEquiv dp s₁ s₂) :
    dp.Opt s₁ = dp.Opt s₂
```

Where `decisionEquiv dp s₁ s₂` means `agreeOn s₁ s₂ (relevantCoords dp)`.

## Machinery Available

### From Sufficiency.lean:
- `isSufficient I`: Knowing coordinates in I determines Opt
- `sufficient_erase_irrelevant'`: Can remove irrelevant coords from sufficient set
- `isRelevant i`: Coordinate i can change Opt when others are fixed
- `isIrrelevant i`: Coordinate i never affects Opt
- `irrelevant_iff_not_relevant`: Equivalence between definitions

### From Information.lean:
- `relevantSet_isSufficient`: The set of relevant coords IS sufficient (uses ProductSpace)
- `numOptClasses_le_pow_srank_binary`: Combinatorial bound
- `quotientEntropy_le_srank_binary`: Entropy bound

### Key Insight

The proof should be:
1. Use `relevantSet_isSufficient` to show `dp.isSufficient (Finset.univ.filter dp.isRelevant)`
2. Show `relevantCoords dp = Finset.univ.filter dp.isRelevant` (definitional equality)
3. Use definition of `isSufficient` with `h : agreeOn s₁ s₂ (relevantCoords dp)` to conclude `dp.Opt s₁ = dp.Opt s₂`

## Current Blocker

The typeclass instance problem is stuck because:
- `DecisionProblem A S` is defined with a `[CoordinateSpace S n]` constraint
- We're trying to use it in a context with `[ProductSpace S n]`
- Lean creates a `ProductSpace.toCoordinateSpace` coercion instance
- But the `DecisionProblem` expects the "original" CoordinateSpace instance
- This creates an instance mismatch that Lean can't resolve

## Possible Solutions

1. **Restructure variable declarations**: Have two versions of theorems - one for CoordinateSpace, one for ProductSpace
2. **Use `convert`**: Instead of `exact`, use `convert` to handle the instance mismatch
3. **Redefine relevantCoords**: Define it as `Finset.univ.filter dp.isRelevant` directly
4. **Avoid the theorem**: Prove directly using `sufficient_erase_irrelevant'` with finset induction
5. **Use `by exact` with explicit instances**: Pass instances explicitly to help Lean unify

## Files Involved

- `DecisionQuotient/Information/RDSrank.lean` (target file)
- `DecisionQuotient/Sufficiency.lean` (core definitions)
- `DecisionQuotient/Information.lean` (relevantSet_isSufficient theorem)

## Notes

The proof strategy is sound - the relevant set IS sufficient. The issue is purely technical around Lean's typeclass resolution with the ProductSpace/CoordinateSpace hierarchy.