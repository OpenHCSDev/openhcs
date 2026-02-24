# Dimensional.lean Proof Debugging Notes

## Current Status

**Compiling modules:**
- `DecisionQuotient.ClaimClosure` ✓ (3081 jobs, 0 errors)
- `DecisionQuotient.Tractability.BoundedActions` ✓
- `DecisionQuotient.Tractability.SeparableUtility` ✓
- `DecisionQuotient.Tractability.TreeStructure` ✓

**Non-compiling:**
- `DecisionQuotient.Tractability.Dimensional.lean` - has remaining proof errors

## Environment

- **Lean version:** `leanprover/lean4:v4.27.0-rc1`
- **Mathlib commit:** `a8227f463392ef51e5bd9f68975fe46f5d9057f3` (January 1, 2026)

## Key Definitions in Dimensional.lean

```lean
-- A dimensional state space where states are d-tuples over a finite alphabet
structure DimensionalStateSpace (k d : ℕ) where
  state : Fin d → Fin k

-- Orbit type: the multiset of coordinate values (ignoring order)
def DimensionalStateSpace.orbitType {k d : ℕ} (s : DimensionalStateSpace k d) :
    Finset (Fin k × ℕ) :=
  Finset.image (fun v : Fin k => (v, Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ))) Finset.univ

-- Permutation of coordinates
def DimensionalStateSpace.permute {k d : ℕ} (s : DimensionalStateSpace k d) (σ : CoordinatePermutation d) :
    DimensionalStateSpace k d where
  state := fun i => s.state (σ.symm i)

-- Coordinate permutation is just Equiv.Perm (Fin d)
abbrev CoordinatePermutation (d : ℕ) := Equiv.Perm (Fin d)
```

## Theorems Fixed

### 1. `orbitType_permute` ✓ (Fixed)
**Statement:** Permuting coordinates preserves the orbit type (value histogram)

**Fix applied:**
- Used `Finset.image_congr` with explicit unfolding
- Fixed the filter/image equivalence proof using proper `ext` tactic

### 2. `bruteForceCheckSufficiency_iff` ✓ (Fixed)
**Statement:** The brute-force checker correctly decides sufficiency

**Fix applied:**
- Simplified the proof using `Finset.filter_eq_empty_iff`
- Proper handling of the `not_and` connective

## Theorems With Remaining Errors

### 3. `orbitType_eq_iff` (Current focus)
**Statement:** Two states have the same orbit type iff they're in the same orbit

```lean
theorem orbitType_eq_iff {k d : ℕ} (s s' : DimensionalStateSpace k d) :
    s.orbitType = s'.orbitType ↔ ∃ σ : CoordinatePermutation d, s' = s.permute σ
```

**Proof strategy attempted:**
1. Extract `hcard : ∀ v, card (filter s.state = v) = card (filter s'.state = v)` from orbit equality
2. Construct fiber bijections: `{i // s.state i = v} ≃ {i // s'.state i = v}` using `Fintype.equivOfCardEq`
3. Define permutation `σ` by sending `i` to `fiberBijections (s.state i) ⟨i, rfl⟩`
4. Prove injectivity and surjectivity

**Current errors:**
- Line ~405: `rcases` fails with dependent elimination error on `Prod.ext_iff`
- Line ~410: `simp` makes no progress on `Fintype.card_fin`
- Line ~417: Type mismatch in injectivity proof - the `fiberBijections` application type doesn't unify
- Line ~430: Surjectivity proof has type mismatch with `rfl`

**Root cause:** The dependent types in the fiber bijections are causing unification issues. When we have:
```lean
fiberBijections (s.state i) ⟨i, rfl⟩ : {i' // s'.state i' = s.state i}
```
The return type depends on `s.state i`, but when comparing `i` and `j`, even if `s.state i = s.state j`, Lean doesn't always unify the types properly.

### 4. `orbitType_count` (Not yet debugged)
**Statement:** Number of orbit types is `(d+k-1 choose k-1)`

**Known issues:**
- Uses `Fintype.card_fun_sum_eq` - doesn't exist in this Mathlib version
- Uses `Finset.sum_le_sum_of_subset` - renamed/moved
- Uses `Nat.find_min_hex` - doesn't exist

## Mathlib API Changes Encountered

| Old API | Current Mathlib Equivalent |
|---------|---------------------------|
| `Equiv.ofCardEq` | `Fintype.equivOfCardEq` |
| `Subtype.ext_iff_val` | `Subtype.ext_iff` (deprecated, same meaning) |
| `Fintype.equiv_iff_card_eq.mp` | `Fintype.equivOfCardEq` |
| `Finset.sum_le_sum_of_subset` | Unknown - need to find replacement |
| `Nat.find_min_hex` | Unknown - need to find replacement |
| `Fintype.card_fun_sum_eq` | Unknown - need to find replacement |

## Potential Alternative Approaches

1. **Use `Classical.choice` directly** instead of `Fintype.equivOfCardEq` for more control
2. **Define σ as a `Fintype.equivOfCardEq` on the whole `Fin d`** using a more global approach
3. **Use `Finset.BijOn`** to construct the bijection more explicitly
4. **Avoid dependent types** by using a different encoding of the fiber bijections

## Files Changed

- `DecisionQuotient/Tractability/Dimensional.lean` - main file being debugged

## Commands to Check

```bash
cd /home/ts/code/projects/openhcs-sequential/docs/papers/paper4_decision_quotient/proofs
lake build 2>&1 | grep -E "^error:" | head -20
```

## Next Steps

1. Fix `orbitType_eq_iff` - try avoiding dependent type issues in fiber bijection construction
2. Find correct Mathlib names for `sum_le_sum_of_subset`, `Nat.find_min_hex`, `Fintype.card_fun_sum_eq`
3. Fix `orbitType_count` proof
4. Run full build to verify all tractability proofs compile
