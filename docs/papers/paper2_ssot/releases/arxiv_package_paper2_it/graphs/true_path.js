/**
 * True Path Enforcement Module
 * 
 * Implements shortest path computation, cycle detection, and invariant
 * identification for proof dependency graphs.
 * 
 * Based on Paper 4 GraphNontriviality.lean:
 * - isCycle: valid path, length ≥ 2, same start/end
 * - triviality: |State| ≤ 1 → no information
 * - nontrivialityScore: surprisal + noveltyDistance
 */

// Note: Previously imported buildAdj and isArtifact from graph_utils.js
// to avoid circular dependencies, these are now defined locally below.

// ============================================================================
// Local copies (avoid circular dependency with graph_utils.js)
// ============================================================================

const ARTIFACT_PATTERNS = [
  /\._simp_/, /\.proxyType/, /_aux_/, /___macroRules_/, /___unexpand_/, /\.\./,
  /\.instRepr/, /\.instBEq/, /\.instHashable/, /\.instOrd/, /\.instToString/,
  /\.instInhabited/, /\.instDecidable/, /\.instSubsingleton/, /\.instNonempty/,
  /\.rec$/, /\.recOn$/, /\.casesOn$/, /\.noConfusion/, /\.noConfusionType/,
  /\.eliminator$/, /\.brecOn$/, /\.binductionOn$/,
  /\.mk\.inj/, /\.mk\.sizeOf_spec/, /\.inj/, /\.injEq/, /\.ind/,
  /\.sizeOf_spec/, /\.sizeOf/, /\.ctorIdx/, /\.ctorElim/,
  /\.match_/, /_match/, /\._main/, /\._cstage/,
  /_auxLemma/, /_eqn/, /_proof/, /_fun/, /_fix/,
  /_sunfold/, /_tactic/,
];

function isArtifact(id) {
  return ARTIFACT_PATTERNS.some((re) => re.test(id));
}

function buildAdj(nodes, edges) {
  const a = {};
  for (const n of nodes) a[n.id] = [];
  for (const e of edges) {
    const s = typeof e.source === 'object' ? e.source.id : e.source;
    const t = typeof e.target === 'object' ? e.target.id : e.target;
    if (a[s]) a[s].push(t);
  }
  return a;
}

// ============================================================================
// Core Types (documented in TRUE_PATH_ARCHITECTURE.md)
// ============================================================================

/**
 * @typedef {Object} TruePath
 * @property {string} claim - Starting claim node ID
 * @property {string} axiom - Ending axiom node ID
 * @property {string[]} nodes - All nodes in path (ordered)
 * @property {number} length - Path length
 * @property {string[]} invariants - Invariant nodes traversed
 * @property {boolean} isShortest - Verified shortest path
 */

/**
 * @typedef {Object} Invariant
 * @property {string} id - Node ID
 * @property {'physical_constant'|'foundational_axiom'|'type_invariant'} kind
 * @property {string} [source] - Lean source location
 */

/**
 * @typedef {Object} Cycle
 * @property {string[]} nodes - Nodes in cycle (first = last for closed cycle)
 * @property {boolean} isNontrivial - True if |State| > 1
 * @property {number} witnessBits - Cycle length for Landauer bound
 * @property {number} [nontrivialityScore] - Optional score
 */

// ============================================================================
// Invariant Detection Patterns
// ============================================================================

const INVARIANT_PATTERNS = [
  // Physical constants from Paper 4
  /lightSpeed|planckConstant|boltzmannConstant|kB_T/i,
  /invariant_set|shared_invariant/i,
  /physical_constant|fundamental_constant/i,
  // Thermodynamic
  /landauer|joulesPerBit|thermodynamic/i,
  // Foundational
  /^Nat\.|^Int\.|^Bool\.|^Prop$/,
];

/**
 * Identify invariant nodes in graph based on patterns and node kind.
 * @param {Object} data - Graph data with nodes array
 * @returns {Invariant[]} - Identified invariant nodes
 */
export function identifyInvariants(data) {
  const invariants = [];
  
  for (const node of data.nodes) {
    if (isArtifact(node.id)) continue;
    
    // Axioms are always invariants
    if (node.kind === 'axiom') {
      invariants.push({ id: node.id, kind: 'foundational_axiom' });
      continue;
    }
    
    // Check pattern matches
    for (const pattern of INVARIANT_PATTERNS) {
      if (pattern.test(node.id)) {
        const kind = node.id.toLowerCase().includes('physical') || 
                     node.id.toLowerCase().includes('constant')
          ? 'physical_constant'
          : 'type_invariant';
        invariants.push({ id: node.id, kind });
        break;
      }
    }
  }
  
  return invariants;
}

// ============================================================================
// Shortest Path Computation (Dijkstra/BFS)
// ============================================================================

/**
 * Compute shortest path from start to any target using BFS.
 * @param {Object} adj - Adjacency list (forward edges)
 * @param {string} start - Start node ID
 * @param {Set<string>} targets - Target node IDs
 * @returns {string[]|null} - Path as node array, or null if unreachable
 */
export function shortestPath(adj, start, targets) {
  if (targets.has(start)) return [start];
  
  const visited = new Set([start]);
  const parent = { [start]: null };
  const queue = [start];
  
  while (queue.length > 0) {
    const current = queue.shift();
    
    for (const neighbor of adj[current] || []) {
      if (visited.has(neighbor)) continue;
      
      visited.add(neighbor);
      parent[neighbor] = current;
      
      if (targets.has(neighbor)) {
        // Reconstruct path
        const path = [];
        for (let n = neighbor; n !== null; n = parent[n]) {
          path.unshift(n);
        }
        return path;
      }
      
      queue.push(neighbor);
    }
  }
  
  return null; // No path found
}

/**
 * Compute shortest path that passes through specified waypoints (invariants).
 * Uses multi-stage BFS: start → waypoint1 → waypoint2 → ... → target
 * @param {Object} adj - Adjacency list
 * @param {string} start - Start node ID
 * @param {Set<string>} targets - Target node IDs (axioms)
 * @param {string[]} waypoints - Invariant nodes to pass through
 * @returns {TruePath|null} - True path or null if impossible
 */
export function shortestPathThroughInvariants(adj, start, targets, waypoints = []) {
  if (waypoints.length === 0) {
    const path = shortestPath(adj, start, targets);
    if (!path) return null;
    return {
      claim: start,
      axiom: path[path.length - 1],
      nodes: path,
      length: path.length - 1,
      invariants: [],
      isShortest: true,
    };
  }
  
  // Multi-stage: start → wp[0] → wp[1] → ... → target
  const fullPath = [start];
  let current = start;
  const traversedInvariants = [];

  // Go through each waypoint
  for (const wp of waypoints) {
    const segment = shortestPath(adj, current, new Set([wp]));
    if (!segment) return null; // Can't reach waypoint

    // Append segment (skip first node as it's already in path)
    for (let i = 1; i < segment.length; i++) {
      fullPath.push(segment[i]);
    }
    traversedInvariants.push(wp);
    current = wp;
  }

  // Final segment to target
  const finalSegment = shortestPath(adj, current, targets);
  if (!finalSegment) return null;

  for (let i = 1; i < finalSegment.length; i++) {
    fullPath.push(finalSegment[i]);
  }

  return {
    claim: start,
    axiom: fullPath[fullPath.length - 1],
    nodes: fullPath,
    length: fullPath.length - 1,
    invariants: traversedInvariants,
    isShortest: true, // Shortest through required waypoints
  };
}

/**
 * Compute all true paths from claims to axioms.
 * @param {Object} data - Graph data
 * @returns {Map<string, TruePath>} - Map from claim ID to true path
 */
export function computeAllTruePaths(data) {
  const adj = buildAdj(data.nodes, data.edges);
  const claims = new Set(data.nodes.filter(n => n.paper === -1).map(n => n.id));
  const axioms = new Set(data.nodes.filter(n => n.kind === 'axiom').map(n => n.id));
  const invariants = identifyInvariants(data);
  const invariantIds = invariants.map(inv => inv.id);

  const paths = new Map();

  for (const claim of claims) {
    // Try path through invariants first
    const pathWithInv = shortestPathThroughInvariants(adj, claim, axioms, invariantIds);
    if (pathWithInv) {
      paths.set(claim, pathWithInv);
    } else {
      // Fallback: direct path
      const directPath = shortestPath(adj, claim, axioms);
      if (directPath) {
        paths.set(claim, {
          claim,
          axiom: directPath[directPath.length - 1],
          nodes: directPath,
          length: directPath.length - 1,
          invariants: [],
          isShortest: true,
        });
      }
    }
  }

  return paths;
}

// ============================================================================
// Cycle Detection (Tarjan's Algorithm)
// ============================================================================

/**
 * Detect all strongly connected components (cycles) using Tarjan's algorithm.
 * @param {Object} data - Graph data
 * @returns {Cycle[]} - Detected cycles
 */
export function detectCycles(data) {
  const adj = buildAdj(data.nodes, data.edges);
  const nodeIds = data.nodes.map(n => n.id);

  // Tarjan's algorithm state
  let index = 0;
  const indices = {};
  const lowlinks = {};
  const onStack = {};
  const stack = [];
  const sccs = [];

  function strongconnect(v) {
    indices[v] = index;
    lowlinks[v] = index;
    index++;
    stack.push(v);
    onStack[v] = true;

    for (const w of adj[v] || []) {
      if (indices[w] === undefined) {
        strongconnect(w);
        lowlinks[v] = Math.min(lowlinks[v], lowlinks[w]);
      } else if (onStack[w]) {
        lowlinks[v] = Math.min(lowlinks[v], indices[w]);
      }
    }

    // If v is a root node, pop SCC from stack
    if (lowlinks[v] === indices[v]) {
      const scc = [];
      let w;
      do {
        w = stack.pop();
        onStack[w] = false;
        scc.push(w);
      } while (w !== v);

      // Only keep SCCs with more than one node (actual cycles)
      if (scc.length > 1) {
        sccs.push(scc);
      }
    }
  }

  for (const v of nodeIds) {
    if (indices[v] === undefined) {
      strongconnect(v);
    }
  }

  // Convert SCCs to Cycle objects
  return sccs.map(scc => ({
    nodes: scc,
    isNontrivial: scc.length > 1, // |State| > 1
    witnessBits: scc.length, // cycleWitnessBits from Paper 4
  }));
}

/**
 * Classify cycle triviality based on Paper 4 criteria.
 * A cycle is trivial if it represents ≤1 distinguishable state.
 * @param {Cycle} cycle - Cycle to classify
 * @param {number} [stateCardinality] - Optional explicit state count
 * @returns {boolean} - True if nontrivial
 */
export function classifyCycleTriviality(cycle, stateCardinality = null) {
  // From Paper 4: triviality_implies_no_information
  // If |State| ≤ 1, the cycle is trivial (no information)
  const effectiveStateCount = stateCardinality ?? cycle.nodes.length;
  return effectiveStateCount > 1;
}

/**
 * Compute nontriviality score for a cycle.
 * Based on Paper 4: nontrivialityScore = surprisal + noveltyDistance
 * @param {Cycle} cycle - Cycle to score
 * @param {Set<string>} knownPaths - Known path signatures
 * @returns {number} - Nontriviality score
 */
export function computeNontrivialityScore(cycle, knownPaths = new Set()) {
  const cycleSignature = cycle.nodes.join('→');

  // Surprisal: -log(prob), approximate with cycle length
  const surprisal = Math.log2(cycle.nodes.length + 1);

  // Novelty distance: 0 if known, 1 if unknown
  const noveltyDistance = knownPaths.has(cycleSignature) ? 0 : 1;

  return surprisal + noveltyDistance;
}

// ============================================================================
// Validation and Reporting
// ============================================================================

/**
 * Validate true path invariant for a graph.
 * @param {Object} data - Graph data
 * @returns {Object} - Validation results
 */
export function validateTruePaths(data) {
  const results = {
    valid: true,
    claimCount: 0,
    pathCount: 0,
    missingPaths: [],
    cycles: [],
    trivialCycles: [],
    nontrivialCycles: [],
    invariants: [],
  };

  // Identify components
  const claims = data.nodes.filter(n => n.paper === -1);
  const axioms = data.nodes.filter(n => n.kind === 'axiom');
  const invariants = identifyInvariants(data);

  results.claimCount = claims.length;
  results.invariants = invariants;

  // Compute paths
  const paths = computeAllTruePaths(data);
  results.pathCount = paths.size;

  // Check for missing paths
  for (const claim of claims) {
    if (!paths.has(claim.id)) {
      results.valid = false;
      results.missingPaths.push(claim.id);
    }
  }

  // Detect and classify cycles
  const cycles = detectCycles(data);
  results.cycles = cycles;

  for (const cycle of cycles) {
    cycle.isNontrivial = classifyCycleTriviality(cycle);
    cycle.nontrivialityScore = computeNontrivialityScore(cycle);

    if (cycle.isNontrivial) {
      results.nontrivialCycles.push(cycle);
    } else {
      results.trivialCycles.push(cycle);
    }
  }

  return results;
}

/**
 * Generate validation report as formatted string.
 * @param {Object} results - Validation results from validateTruePaths
 * @returns {string} - Formatted report
 */
export function generateValidationReport(results) {
  const lines = [
    '═══════════════════════════════════════════════════════════════',
    '                    TRUE PATH VALIDATION REPORT                 ',
    '═══════════════════════════════════════════════════════════════',
    '',
    `Status: ${results.valid ? '✅ VALID' : '❌ INVALID'}`,
    '',
    '─── Claims ───',
    `  Total claims: ${results.claimCount}`,
    `  Paths found: ${results.pathCount}`,
    `  Missing paths: ${results.missingPaths.length}`,
  ];

  if (results.missingPaths.length > 0) {
    lines.push('');
    lines.push('  ⚠️  Claims without paths to axioms:');
    for (const claim of results.missingPaths.slice(0, 10)) {
      lines.push(`      - ${claim}`);
    }
    if (results.missingPaths.length > 10) {
      lines.push(`      ... and ${results.missingPaths.length - 10} more`);
    }
  }

  lines.push('');
  lines.push('─── Invariants ───');
  lines.push(`  Detected: ${results.invariants.length}`);
  for (const inv of results.invariants.slice(0, 5)) {
    lines.push(`    - ${inv.id} (${inv.kind})`);
  }
  if (results.invariants.length > 5) {
    lines.push(`    ... and ${results.invariants.length - 5} more`);
  }

  lines.push('');
  lines.push('─── Cycles ───');
  lines.push(`  Total cycles: ${results.cycles.length}`);
  lines.push(`  Nontrivial (|State| > 1): ${results.nontrivialCycles.length}`);
  lines.push(`  Trivial (|State| ≤ 1): ${results.trivialCycles.length}`);

  if (results.trivialCycles.length > 0) {
    lines.push('');
    lines.push('  ⚠️  Trivial cycles detected (no information):');
    for (const cycle of results.trivialCycles.slice(0, 3)) {
      lines.push(`      - ${cycle.nodes.slice(0, 3).join(' → ')}...`);
    }
  }

  lines.push('');
  lines.push('═══════════════════════════════════════════════════════════════');

  return lines.join('\n');
}

// Export for use in graph_utils.js FILTERS
export const TRUE_PATH_FILTERS = {
  /**
   * Filter to show only nodes on true paths from claims to axioms.
   */
  truePathsOnly: (data, _params) => {
    const paths = computeAllTruePaths(data);
    const nodesOnPaths = new Set();

    for (const [, path] of paths) {
      for (const node of path.nodes) {
        nodesOnPaths.add(node);
      }
    }

    const nodes = data.nodes.filter(n => nodesOnPaths.has(n.id));
    const nodeSet = new Set(nodes.map(n => n.id));
    const edges = data.edges.filter(e => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nodeSet.has(s) && nodeSet.has(t);
    });

    return { nodes, edges };
  },

  /**
   * Filter to highlight invariant nodes.
   */
  highlightInvariants: (data, _params) => {
    const invariants = identifyInvariants(data);
    const invariantIds = new Set(invariants.map(inv => inv.id));

    // Add isInvariant flag to nodes
    const nodes = data.nodes.map(n => ({
      ...n,
      isInvariant: invariantIds.has(n.id),
    }));

    return { nodes, edges: data.edges };
  },

  /**
   * Filter to exclude trivial cycles.
   */
  excludeTrivialCycles: (data, _params) => {
    const cycles = detectCycles(data);
    const trivialNodes = new Set();

    for (const cycle of cycles) {
      if (!classifyCycleTriviality(cycle)) {
        for (const node of cycle.nodes) {
          trivialNodes.add(node);
        }
      }
    }

    const nodes = data.nodes.filter(n => !trivialNodes.has(n.id));
    const nodeSet = new Set(nodes.map(n => n.id));
    const edges = data.edges.filter(e => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nodeSet.has(s) && nodeSet.has(t);
    });

    return { nodes, edges };
  },
};

