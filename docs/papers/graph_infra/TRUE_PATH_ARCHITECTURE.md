# True Path Architecture: Modular Enforcement of Shortest Paths Through Invariants

## Overview

This document specifies the architecture for enforcing **true paths** in proof dependency graphs:
- Shortest paths from claims to foundational axioms
- Through all unique invariants (no skipping)
- With non-triviality cycle detection

## Core Concepts from Paper 4 (GraphNontriviality.lean)

### 1. Graph Structure
```lean
structure Graph (V : Type u) where
  edge : V → V → Prop

def validPath (G : Graph V) : List V → Prop
def isCycle (G : Graph V) (p : List V) : Prop :=
  validPath G p ∧ 2 ≤ p.length ∧ p.head? = p.getLast?
```

### 2. Triviality (from LocalityPhysics.lean)
```lean
-- Triviality: |State| ≤ 1 → no information
theorem triviality_implies_no_information
    (hTriv : Fintype.card State ≤ 1) :
    ∀ (f : State → Output), (Finset.univ.image f).card = 1
```

### 3. Nontriviality Score
```lean
-- surprisal + novelty distance
noncomputable def nontrivialityScore
    (decode : H → List V) (prior : ProbDist H)
    (known : KnownPaths V) (p : List V) : ℝ :=
  pathSurprisal decode prior p + noveltyDistance known p
```

### 4. Thermodynamic Lower Bounds (Landauer)
```lean
theorem cycle_witness_implies_positive_landauer
    (hCycle : isCycle G p) :
    0 < ThermodynamicLift.energyLowerBound M (cycleWitnessBits G p)
```

## Modular Architecture

### Layer 1: Core Abstractions (TypeScript/JavaScript)

```typescript
// TruePath: A validated shortest path from claim to axiom
interface TruePath {
  claim: NodeId;          // Starting claim node
  axiom: NodeId;          // Ending axiom node
  nodes: NodeId[];        // All nodes in path
  length: number;         // Path length
  invariants: NodeId[];   // Invariant nodes traversed
  isShortest: boolean;    // Verified shortest path
}

// Invariant: A foundational theorem/definition
interface Invariant {
  id: NodeId;
  kind: 'physical_constant' | 'foundational_axiom' | 'type_invariant';
  source: string;         // Lean source location
}

// Cycle: Detected cycle with triviality classification
interface Cycle {
  nodes: NodeId[];
  isNontrivial: boolean;
  nontrivialityScore?: number;
  witnessBits: number;    // For Landauer lower bound
}
```

### Layer 2: Path Computation Module

```typescript
// path_computation.ts
export function dijkstraShortestPath(
  graph: Graph,
  start: NodeId,
  targets: Set<NodeId>,
  mustTraverse?: Set<NodeId>  // Invariants to pass through
): TruePath | null;

export function allShortestPaths(
  graph: Graph,
  claims: Set<NodeId>,
  axioms: Set<NodeId>
): Map<NodeId, TruePath>;

export function pathThroughInvariants(
  graph: Graph,
  claim: NodeId,
  axiom: NodeId,
  invariants: Set<NodeId>
): TruePath | null;
```

### Layer 3: Cycle Detection Module

```typescript
// cycle_detection.ts
export function detectCycles(graph: Graph): Cycle[];

export function classifyCycleTriviality(
  cycle: Cycle,
  stateCardinality: number
): boolean;

export function computeNontrivialityScore(
  cycle: Cycle,
  observer: ObserverModel
): number;

export function cycleWitnessBits(cycle: Cycle): number;
```

### Layer 4: Invariant Identification Module

```typescript
// invariant_identification.ts
export function identifyInvariants(
  leanSource: string
): Invariant[];

// Pattern matching for invariant detection
const INVARIANT_PATTERNS = [
  /physical_constant/,
  /foundational_axiom/,
  /invariant_set/,
  // Physical constants from Paper 4
  /lightSpeed|planckConstant|boltzmannConstant/,
];
```

### Layer 5: Build Pipeline Integration

```python
# In build_papers.py
def _validate_true_paths(self, paper_id: str) -> Dict[str, Any]:
    """Validate that all claims have true paths to axioms."""
    graph = self._load_graph_json(paper_id)
    claims = self._get_claim_nodes(graph)
    axioms = self._get_axiom_nodes(graph)
    invariants = self._identify_invariants(graph)
    
    validation_results = {
        'valid': True,
        'paths': {},
        'cycles': [],
        'warnings': []
    }
    
    for claim in claims:
        path = self._compute_shortest_path(graph, claim, axioms, invariants)
        if path is None:
            validation_results['valid'] = False
            validation_results['warnings'].append(
                f"No path from {claim} to any axiom through invariants"
            )
        else:
            validation_results['paths'][claim] = path
    
    # Detect and classify cycles
    cycles = self._detect_cycles(graph)
    for cycle in cycles:
        is_nontrivial = self._classify_triviality(cycle)
        validation_results['cycles'].append({
            'nodes': cycle,
            'nontrivial': is_nontrivial
        })
    
    return validation_results
```

## Implementation Plan

### Phase 1: Core Algorithms (graph_utils.js extensions)

Add to `graph_utils.js`:
```javascript
// Dijkstra shortest path with invariant waypoints
export function shortestPathThroughInvariants(data, start, targets, invariants) {
  // Returns shortest path that passes through all specified invariants
}

// Tarjan's algorithm for cycle detection
export function detectCycles(data) {
  // Returns array of cycles with node lists
}

// Classify cycle triviality based on state cardinality
export function classifyCycleTriviality(cycle, stateCount) {
  return stateCount > 1; // Nontrivial if |State| > 1
}
```

### Phase 2: Invariant Detection

Pattern-match Lean source for invariant nodes:
- Physical constants: `lightSpeed`, `planckConstant`, `boltzmannConstant`
- Foundational axioms: nodes with `kind: "axiom"`
- Invariant definitions: `invariant_set`, `shared_invariant`

### Phase 3: Build Pipeline

Add to `build_papers.py`:
```python
def _validate_true_paths(self, paper_id: str) -> bool:
    """Enforce true path invariant for all claims."""
    # 1. Load graph
    # 2. Identify claims, axioms, invariants
    # 3. For each claim, compute shortest path to axiom through invariants
    # 4. Detect cycles, classify triviality
    # 5. Report violations
```

### Phase 4: Visualization

Update `dependency-graph.jsx`:
- Highlight invariant nodes (distinct color/shape)
- Show true paths on hover/click
- Mark trivial vs nontrivial cycles
- Display nontriviality scores

## Invariant Rule

**ALL claim nodes MUST have a valid true path to at least one axiom passing through all required invariants. Trivial cycles (|State| ≤ 1) are flagged as warnings.**

This is enforced at build time and surfaced in the graph visualization.

