# Handle Definition Standards for Lean Proof Papers

## Purpose

This document defines standards for creating paper handle aliases (abbreviations) in Lean proof developments to ensure consistency, proper dependency tracking, and maintainability across papers.

## The Problem

In Paper 4 (DecisionQuotient), handle definitions were inconsistent:

```lean
-- PH handles: Reference external PhysicalComplexity namespace directly
abbrev PH11 := @PhysicalComplexity.PhysicalCollapseAtRequirement

-- DC handles: Reference DecisionQuotient submodule  
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation

-- DE handles: Reference ClaimClosure submodule
abbrev DE1 := ClaimClosure.DE1
```

This inconsistency caused:
- PH handles to appear as orphans in dependency graphs
- Mixed reference patterns making maintenance difficult
- False positives in orphan detection analysis

## Standards

### 1. Namespace Consistency

**All handles MUST be defined in the `DecisionQuotient` namespace** (or the paper's main namespace).

```lean
namespace DecisionQuotient

-- GOOD: All handles defined in consistent namespace
abbrev PH11 := PhysicalComplexity.PhysicalCollapseAtRequirement
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation
abbrev DE1 := ClaimClosure.DE1

end DecisionQuotient
```

### 2. Reference Pattern

**Prefer direct submodule references over external root namespace references.**

```lean
-- GOOD: Reference through DecisionQuotient submodule
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation

-- AVOID: Direct root namespace reference (causes graph orphan issues)
abbrev PH11 := @PhysicalComplexity.PhysicalCollapseAtRequirement

-- GOOD: If needed, reference through DecisionQuotient.Physics
abbrev PH11 := Physics.PhysicalComplexity.PhysicalCollapseAtRequirement
```

### 3. @ Notation Usage

**Avoid `@` (explicit universe polymorphism) unless absolutely necessary.**

```lean
-- GOOD: Implicit universe polymorphism
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation

-- AVOID: Explicit universe polymorphism (can confuse dependency extraction)
abbrev PH11 := @PhysicalComplexity.PhysicalCollapseAtRequirement
```

If `@` is required for type resolution, ensure the reference still goes through the proper submodule path.

### 4. Export vs Abbrev

Use the appropriate mechanism based on the use case:

**Use `export` for bulk re-exporting from a module:**
```lean
namespace CC
export DecisionQuotient.ClaimClosure (
  RegimeSimulation
  anchor_sigma2p_complete_conditional
  -- ... many theorems
)
end CC
```

**Use `abbrev` for individual paper handles with specific names:**
```lean
-- Paper-specific handle pointing to specific theorem
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation
abbrev PH11 := Physics.PhysicalComplexity.PhysicalCollapseAtRequirement
```

### 5. Handle Naming Convention

**Format:** `[A-Z]+[0-9]+[a-z]?`

- Prefix: 1-4 uppercase letters indicating claim category
- Number: Sequential digits
- Optional suffix: lowercase letter for variants

Examples:
```lean
PH11     -- Physical Hardness claim 11
DC1      -- Dichotomy/Complexity claim 1  
CC85     -- Claim Closure claim 85
FP7a     -- First Principle 7 variant a
```

### 6. Prefix Categories (Paper 4 Standard)

| Prefix | Category | Example |
|--------|----------|---------|
| PH | Physical Hardness / Physical Complexity | PH11-PH36 |
| DC | Dichotomy/Complexity hierarchy | DC1-DC37 |
| CC | Claim Closure | CC1-CC100+ |
| IC | Integrity Competence | IC1-IC20 |
| DE | Decision Equivalence | DE1-DE4 |
| MI | Molecular Integrity | MI1-MI5 |
| SR | Self-Reference | SR1-SR5 |
| IA | Information Access | IA1-IA13 |
| GE | Gap Energy | GE1-GE9 |
| IE | Integrity Equilibrium | IE1-IE17 |
| FI | Functional Information | FI1-FI7 |
| BA | Bounded Acquisition | BA1-BA10 |
| IT | Information Theory | IT1-IT6 |
| EI | Energy-Information | EI1-EI5 |
| FS | Fisher Statistics | FS1-FS5 |
| QT | Quotient Theory | QT1-QT4 |
| WD | Witness-Checking Duality | WD1-WD5 |
| BC | Bayes from Counting | BC1-BC5 |
| EP | Empirical Premise | EP1-EP4 |
| FP | First Principle | FP1-FP15 |
| LP | Locality Physics | LP1-LP61 |

### 7. HandleAliases.lean Structure

The `HandleAliases.lean` file should follow this structure:

```lean
namespace DecisionQuotient

-- ============================================================
-- Category 1: Physical Complexity (PH)
-- ============================================================
namespace PH
export Physics.PhysicalComplexity (
  k_Boltzmann
  PhysicalComputer
  -- ...
)
end PH

-- Individual PH handles
abbrev PH11 := Physics.PhysicalComplexity.PhysicalCollapseAtRequirement
abbrev PH12 := Physics.PhysicalComplexity.no_physical_collapse_at_requirement
-- ...

-- ============================================================
-- Category 2: Dichotomy/Complexity (DC)
-- ============================================================
abbrev DC1 := StochasticSequential.static_stochastic_strict_separation
abbrev DC2 := StochasticSequential.stochastic_sequential_strict_separation
-- ...

-- ============================================================
-- Category 3: Claim Closure (CC)
-- ============================================================
namespace CC
export DecisionQuotient.ClaimClosure (
  -- ... bulk exports
)
end CC

end DecisionQuotient
```

### 8. Validation Checklist

Before committing HandleAliases.lean:

- [ ] All handles defined in `DecisionQuotient` namespace
- [ ] No direct `PhysicalComplexity.` references (use `Physics.PhysicalComplexity.`)
- [ ] Minimize `@` notation usage
- [ ] Handle names follow `[A-Z]+[0-9]+[a-z]?` pattern
- [ ] Prefix categories documented in comments
- [ ] Run dependency analyzer to verify no unexpected orphans

## Migration Guide

To fix existing inconsistencies (like PH11-PH36 in Paper 4):

1. **Identify the correct module path:**
   ```lean
   -- Instead of:
   abbrev PH11 := @PhysicalComplexity.PhysicalCollapseAtRequirement
   
   -- Use:
   abbrev PH11 := Physics.PhysicalComplexity.PhysicalCollapseAtRequirement
   ```

2. **Ensure PhysicalComplexity is imported through DecisionQuotient:**
   ```lean
   import DecisionQuotient.Physics.PhysicalHardness
   -- or
   import DecisionQuotient.Physics.PhysicalComplexity
   ```

3. **Verify the target exists at the submodule path**

4. **Regenerate dependency graph and confirm handles are connected**

## Tool Integration

Use the dependency analyzer to validate handles:

```bash
python docs/papers/graph_infra/dependency_analyzer.py \
  --graph paper4_toc.json \
  --output analysis.json \
  --verbose
```

The analyzer will flag:
- Mixed orphan status within same prefix
- Mixed namespaces for same prefix
- Handles with `@` notation
- External root namespace references

## Rationale

These standards ensure:

1. **Dependency graph accuracy**: Consistent namespace paths allow proper edge detection
2. **Maintainability**: Clear patterns make it easy to add/modify handles
3. **Documentation**: Prefix categories provide semantic meaning
4. **Tool compatibility**: Standardized references work with analysis tools
5. **Cross-paper consistency**: Reusable patterns across the paper series

## References

- Paper 4 HandleAliases.lean: `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/HandleAliases.lean`
- Dependency Analyzer: `docs/papers/graph_infra/dependency_analyzer.py`
- Paper 4 Proof Table: `docs/papers/paper4_decision_quotient/releases/paper4_toc.md` (lines 5248-5318)
