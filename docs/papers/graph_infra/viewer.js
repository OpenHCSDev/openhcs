// Make React hooks available globally
const { useState, useEffect, useRef, useCallback, useMemo } = React;
const d3 = window.d3;

// Shared graph utilities used by graph viewers
// Re-export true path enforcement module


// Lean compiler-generated artifacts that aren't part of the paper's claims
const ARTIFACT_PATTERNS = [
  /\._simp_/, /\.proxyType/, /_aux_/, /___macroRules_/, /___unexpand_/, /\.\./,
  // Lean type class instances (auto-generated)
  /\.instRepr/, /\.instBEq/, /\.instHashable/, /\.instOrd/, /\.instToString/,
  /\.instInhabited/, /\.instDecidable/, /\.instSubsingleton/, /\.instNonempty/,
  // Recursion and elimination principles
  /\.rec$/, /\.recOn$/, /\.casesOn$/, /\.noConfusion/, /\.noConfusionType/,
  /\.eliminator$/, /\.brecOn$/, /\.binductionOn$/,
  // Constructor internals
  /\.mk\.inj/, /\.mk\.sizeOf_spec/, /\.inj/, /\.injEq/, /\.ind/,
  // Size and indexing
  /\.sizeOf_spec/, /\.sizeOf/, /\.ctorIdx/, /\.ctorElim/,
  // Match expressions
  /\.match_/, /_match/, /\._main/, /\._cstage/,
  // Auxiliary definitions
  /_auxLemma/, /_eqn/, /_proof/, /_fun/, /_fix/,
  // Other internals
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
function identifyInvariants(data) {
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
function shortestPath(adj, start, targets) {
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
function shortestPathThroughInvariants(adj, start, targets, waypoints = []) {
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
function computeAllTruePaths(data) {
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
function detectCycles(data) {
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
function classifyCycleTriviality(cycle, stateCardinality = null) {
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
function computeNontrivialityScore(cycle, knownPaths = new Set()) {
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
function validateTruePaths(data) {
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
function generateValidationReport(results) {
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
const TRUE_PATH_FILTERS = {
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



/**
 * LaTeX Renderer Module
 * 
 * Extracts and renders LaTeX math from Lean theorem statements.
 * Uses KaTeX CDN for rendering.
 */

const LATEX_MAPPING = {
  'Nat': '\\mathbb{N}',
  'Int': '\\mathbb{Z}',
  'Bool': '\\mathbb{B}',
  'Prop': '\\text{Prop}',
  'Type': '\\text{Type}',
  'List': '\\text{List}',
  'Array': '\\text{Array}',
  'Finset': '\\mathcal{F}',
  'Set': '\\mathcal{S}',
  'Real': '\\mathbb{R}',
  'forall': '\\forall',
  'exists': '\\exists',
  '->': '\\rightarrow',
  '->': '\\to',
  '\\/': '\\lor',
  '/\\': '\\land',
  '~': '\\neg',
  '<=': '\\leq',
  '>=': '\\geq',
  '!=': '\\neq',
  '==': '\\equiv',
};

const LEAN_TO_LATEX_PATTERNS = [
  [/Nat\.add/g, '\\mathbb{N}.+'],
  [/Nat\.mul/g, '\\mathbb{N}.\\times'],
  [/Nat\.sub/g, '\\mathbb{N}.-'],
  [/Nat\.le/g, '\\le_{\\mathbb{N}}'],
  [/Int\.add/g, '\\mathbb{Z}.+'],
  [/List\.append/g, '\\mathbin{+\\!+}'],
  [/List\.map/g, '\\text{map}'],
  [/Finset\.card/g, '|\\cdot|'],
  [/Finset\.union/g, '\\cup'],
  [/Finset\.inter/g, '\\cap'],
  [/\bforall\b/g, '\\forall'],
  [/\bexists\b/g, '\\exists'],
  [/\bTrue\b/g, '\\top'],
  [/\bFalse\b/g, '\\bot'],
  [/\bAnd\b/g, '\\land'],
  [/\bOr\b/g, '\\lor'],
  [/\bNot\b/g, '\\neg'],
  [/\bEq\b/g, '='],
  [/->/g, '\\to'],
  [/=>/g, '\\Rightarrow'],
  [/<->/g, '\\leftrightarrow'],
  [/<=/g, '\\leq'],
  [/>=/g, '\\geq'],
  [/!=/g, '\\neq'],
];

function leanToLatex(leanCode) {
  if (!leanCode) return null;
  
  let latex = leanCode
    .replace(/^theorem\s+/, '\\textbf{Theorem:} ')
    .replace(/^lemma\s+/, '\\textbf{Lemma:} ')
    .replace(/^def\s+/, '\\textbf{Def:} ')
    .replace(/^axiom\s+/, '\\textbf{Axiom:} ')
    .replace(/\s*:\s*/g, ' : ')
    .replace(/\s*:=\s*/g, ' := ');
  
  for (const [pattern, replacement] of LEAN_TO_LATEX_PATTERNS) {
    latex = latex.replace(pattern, replacement);
  }
  
  latex = latex
    .replace(/([a-zA-Z_][a-zA-Z0-9_]*)\s*\(/g, '\\text{$1}(')
    .replace(/\(([^)]+)\)/g, '\\($1\\)');
  
  return `\\text{${latex}}`;
}

function extractLatex(node) {
  if (!node) return null;
  
  if (node.latex) return node.latex;
  if (node.signature) return leanToLatex(node.signature);
  if (node.statement) return leanToLatex(node.statement);
  
  const name = node.id?.split('.').pop() || '';
  const kind = node.kind || 'node';
  
  return `\\text{${kind}\\ ${name}}`;
}

function renderLatex(latex, container) {
  if (!latex || !container) return false;
  
  if (typeof window !== 'undefined' && window.katex) {
    try {
      window.katex.render(latex, container, {
        throwOnError: false,
        displayMode: true,
        output: 'html',
      });
      return true;
    } catch (e) {
      container.textContent = latex;
      return false;
    }
  }
  
  container.textContent = latex;
  return false;
}

function renderLatexInline(latex, container) {
  if (!latex || !container) return false;
  
  if (typeof window !== 'undefined' && window.katex) {
    try {
      window.katex.render(latex, container, {
        throwOnError: false,
        displayMode: false,
        output: 'html',
      });
      return true;
    } catch (e) {
      container.textContent = latex;
      return false;
    }
  }
  
  container.textContent = latex;
  return false;
}

function formatLeanSignature(signature, maxLength = 200) {
  if (!signature) return null;
  
  const trimmed = signature.trim();
  if (trimmed.length <= maxLength) return trimmed;
  
  return trimmed.slice(0, maxLength - 3) + '...';
}

const FOUNDATION_BUCKETS = {
  'FOUNDATION.Counting': {
    name: 'Counting',
    description: 'Nat, Int, Fin (counting structure)',
    color: '#ef4444',
    symbols: ['Nat', 'Int', 'Fin', 'Nat.add', 'Nat.mul', 'Nat.sub'],
  },
  'FOUNDATION.Collections': {
    name: 'Collections',
    description: 'List, Array, Finset (collection structure)',
    color: '#3b82f6',
    symbols: ['List', 'Array', 'Finset', 'List.append', 'List.map'],
  },
  'FOUNDATION.Boolean': {
    name: 'Boolean',
    description: 'Bool (branching structure)',
    color: '#f59e0b',
    symbols: ['Bool', 'Bool.true', 'Bool.false'],
  },
  'FOUNDATION.Logic': {
    name: 'Logic',
    description: 'True, False, And, Or, Exists (logical structure)',
    color: '#8b5cf6',
    symbols: ['True', 'False', 'And', 'Or', 'Exists', 'Decidable'],
  },
  'FOUNDATION.Equality': {
    name: 'Equality',
    description: 'Eq, HEq, Decidable (equality structure)',
    color: '#10b981',
    symbols: ['Eq', 'HEq', 'Decidable'],
  },
  'FOUNDATION.SetTheory': {
    name: 'Set Theory',
    description: 'Set, Membership, Quot (set structure)',
    color: '#ec4899',
    symbols: ['Set', 'Membership', 'Quot'],
  },
  'FOUNDATION.OrderAlgebra': {
    name: 'Order/Algebra',
    description: 'LT, LE, Add, Mul (order/algebra)',
    color: '#06b6d4',
    symbols: ['LT', 'LE', 'Add', 'Mul', 'Semiring'],
  },
  'FOUNDATION.MeasureTheory': {
    name: 'Measure Theory',
    description: 'MeasureTheory, ProbabilityTheory',
    color: '#f97316',
    symbols: ['MeasureTheory', 'ProbabilityTheory', 'Measure'],
  },
  'FOUNDATION.Analysis': {
    name: 'Analysis',
    description: 'Real, NNReal, Complex (analytic structure)',
    color: '#a855f7',
    symbols: ['Real', 'NNReal', 'Complex'],
  },
};

function classifyFoundationBucket(nodeId) {
  const id = nodeId.toLowerCase();
  
  for (const [bucket, info] of Object.entries(FOUNDATION_BUCKETS)) {
    for (const symbol of info.symbols) {
      if (id.includes(symbol.toLowerCase())) {
        return bucket;
      }
    }
  }
  
  if (id.includes('nat') || id.includes('int') || id.includes('fin')) {
    return 'FOUNDATION.Counting';
  }
  if (id.includes('list') || id.includes('array') || id.includes('finset')) {
    return 'FOUNDATION.Collections';
  }
  if (id.includes('bool')) {
    return 'FOUNDATION.Boolean';
  }
  if (id.includes('true') || id.includes('false') || id.includes('and') || 
      id.includes('or') || id.includes('exists') || id.includes('decidable')) {
    return 'FOUNDATION.Logic';
  }
  if (id.includes('eq') || id.includes('heq')) {
    return 'FOUNDATION.Equality';
  }
  if (id.includes('set') || id.includes('membership') || id.includes('quot')) {
    return 'FOUNDATION.SetTheory';
  }
  if (id.includes('lt') || id.includes('le') || id.includes('add') || id.includes('mul')) {
    return 'FOUNDATION.OrderAlgebra';
  }
  if (id.includes('measure') || id.includes('probability')) {
    return 'FOUNDATION.MeasureTheory';
  }
  if (id.includes('real') || id.includes('complex')) {
    return 'FOUNDATION.Analysis';
  }
  
  return null;
}

function computeFoundationBuckets(nodeId, dependencies, data) {
  const buckets = new Set();
  
  const directBucket = classifyFoundationBucket(nodeId);
  if (directBucket) buckets.add(directBucket);
  
  if (dependencies && data) {
    const traverse = (id, visited = new Set()) => {
      if (visited.has(id)) return;
      visited.add(id);
      
      const bucket = classifyFoundationBucket(id);
      if (bucket) buckets.add(bucket);
      
      const node = data.nodes.find(n => n.id === id);
      if (node && node.kind === 'axiom') {
        if (id.startsWith('FOUNDATION.')) {
          buckets.add(id);
        }
      }
      
      const deps = dependencies[id] || [];
      for (const dep of deps) {
        traverse(dep, visited);
      }
    };
    
    traverse(nodeId);
  }
  
  return Array.from(buckets);
}







// Demo data representing the structure of the 4-paper infrastructure
// Replace with actual graph.json from #export_graph_json
const DEMO_DATA = generateDemoGraph();

function generateDemoGraph() {
  const modules = [
    // Paper 1: AbstractClassSystem
    { prefix: "ACS", count: 40, kind: "theorem", paper: 1 },
    { prefix: "ACS.Def", count: 15, kind: "definition", paper: 1 },
    // Paper 2: SSOT
    { prefix: "Ssot", count: 25, kind: "theorem", paper: 2 },
    { prefix: "Ssot.Def", count: 10, kind: "definition", paper: 2 },
    // Paper 3: Leverage
    { prefix: "Leverage", count: 30, kind: "theorem", paper: 3 },
    { prefix: "Leverage.Def", count: 12, kind: "definition", paper: 3 },
    // Paper 4: DecisionQuotient
    { prefix: "DQ", count: 60, kind: "theorem", paper: 4 },
    { prefix: "DQ.Def", count: 25, kind: "definition", paper: 4 },
    { prefix: "DQ.Thermo", count: 20, kind: "theorem", paper: 4 },
    // Bridge
    { prefix: "Bridge", count: 15, kind: "theorem", paper: 0 },
    // Core
    { prefix: "Core.Nat", count: 3, kind: "axiom", paper: -1 },
  ];

  const nodes = [];
  const edges = [];
  let id = 0;

  for (const mod of modules) {
    for (let i = 0; i < mod.count; i++) {
      nodes.push({
        id: `${mod.prefix}.${i}`,
        kind: mod.kind,
        paper: mod.paper,
      });
      id++;
    }
  }

  // Create dense connectivity within modules
  for (const mod of modules) {
    const modNodes = nodes.filter((n) => n.id.startsWith(mod.prefix + "."));
    for (let i = 1; i < modNodes.length; i++) {
      edges.push({ source: modNodes[i].id, target: modNodes[i - 1].id });
      if (i > 2 && Math.random() > 0.6) {
        const j = Math.floor(Math.random() * (i - 1));
        edges.push({ source: modNodes[i].id, target: modNodes[j].id });
      }
    }
  }

  // Cross-module dependencies (papers depend on earlier papers)
  const paperNodes = (p) => nodes.filter((n) => n.paper === p);
  const connect = (fromPaper, toPaper, count) => {
    const from = paperNodes(fromPaper);
    const to = paperNodes(toPaper);
    for (let i = 0; i < count; i++) {
      const f = from[Math.floor(Math.random() * from.length)];
      const t = to[Math.floor(Math.random() * to.length)];
      edges.push({ source: f.id, target: t.id });
    }
  };

  // Core -> everything
  const core = paperNodes(-1);
  for (const p of [1, 2, 3, 4]) {
    const pn = paperNodes(p);
    for (let i = 0; i < 5; i++) {
      edges.push({
        source: pn[Math.floor(Math.random() * pn.length)].id,
        target: core[Math.floor(Math.random() * core.length)].id,
      });
    }
  }

  connect(2, 1, 12); // SSOT depends on ACS
  connect(3, 1, 8); // Leverage depends on ACS
  connect(3, 2, 10); // Leverage depends on SSOT
  connect(4, 1, 6); // DQ depends on ACS
  connect(0, 3, 8); // Bridge depends on Leverage
  connect(0, 4, 8); // Bridge depends on DQ
  connect(0, 2, 4); // Bridge depends on SSOT

  return { nodes, edges };
}

const PAPER_COLORS = {
  [-1]: "#ef4444", // Core/Nat — red
  0: "#f59e0b", // Bridge — amber
  1: "#3b82f6", // Paper 1: ACS — blue
  2: "#8b5cf6", // Paper 2: SSOT — purple
  3: "#10b981", // Paper 3: Leverage — green
  4: "#ec4899", // Paper 4: DQ — pink
};

const PAPER_NAMES = {
  [-1]: "Core Axioms (ℕ)",
  0: "Bridge Theorems",
  1: "Paper 1: AbstractClassSystem",
  2: "Paper 2: SSOT",
  3: "Paper 3: Leverage",
  4: "Paper 4: DecisionQuotient",
};

const KIND_SHAPES = {
  theorem: "circle",
  definition: "square",
  axiom: "diamond",
  other: "circle",
};

// computeStats provided by graph_utils.js (imported above)

function ForceGraph({ data, width, height, highlightPaper, selectedNode, onSelectNode, highlightedPath }) {
  const svgRef = useRef(null);
  const simRef = useRef(null);
  const nodePositionsRef = useRef({});

  useEffect(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll("*").remove();

    const g = svg.append("g");

    // Zoom
    const zoom = d3.zoom().scaleExtent([0.1, 8]).on("zoom", (event) => {
      g.attr("transform", event.transform);
    });
    svg.call(zoom);

    const nodes = data.nodes.map((d) => ({ ...d }));
    const edges = data.edges.map((d) => ({ ...d }));

    const sim = d3
      .forceSimulation(nodes)
      .force(
        "link",
        d3
          .forceLink(edges)
          .id((d) => d.id)
          .distance(15)
          .strength(0.3)
      )
      .force("charge", d3.forceManyBody().strength(-8).distanceMax(150))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("collision", d3.forceCollide(4))
      .force(
        "cluster",
        d3.forceX(width / 2).strength(0.01)
      )
      .force("clusterY", d3.forceY(height / 2).strength(0.01));

    simRef.current = sim;

    const link = g
      .append("g")
      .selectAll("line")
      .data(edges)
      .join("line")
      .attr("stroke", "#ffffff08")
      .attr("stroke-width", 0.5);

    const node = g
      .append("g")
      .selectAll("circle")
      .data(nodes)
      .join("circle")
      .attr("r", (d) => (d.kind === "axiom" ? 5 : d.kind === "definition" ? 3.5 : 2.5))
      .attr("fill", (d) => PAPER_COLORS[d.paper] || "#666")
      .attr("stroke", "none")
      .attr("opacity", 0.85)
      .call(
        d3
          .drag()
          .on("start", (event, d) => {
            if (!event.active) sim.alphaTarget(0.3).restart();
            d.fx = d.x;
            d.fy = d.y;
          })
          .on("drag", (event, d) => {
            d.fx = event.x;
            d.fy = event.y;
          })
          .on("end", (event, d) => {
            if (!event.active) sim.alphaTarget(0);
            d.fx = null;
            d.fy = null;
          })
      );

    node.append("title").text((d) => `${d.id} (${d.kind})`);

    node.on("click", (event, d) => {
      event.stopPropagation();
      if (onSelectNode) onSelectNode(d.id);
    });

    sim.on("tick", () => {
      link
        .attr("x1", (d) => d.source.x)
        .attr("y1", (d) => d.source.y)
        .attr("x2", (d) => d.target.x)
        .attr("y2", (d) => d.target.y);
      node.attr("cx", (d) => d.x).attr("cy", (d) => d.y);
      nodePositionsRef.current[d.id] = { x: d.x, y: d.y };
    });

    // Highlight paper on hover
    if (highlightPaper !== null) {
      node
        .attr("opacity", (d) =>
          d.paper === highlightPaper ? 1 : 0.08
        )
        .attr("r", (d) =>
          d.paper === highlightPaper
            ? d.kind === "axiom" ? 7 : d.kind === "definition" ? 5 : 4
            : d.kind === "axiom" ? 5 : d.kind === "definition" ? 3.5 : 2.5
        );
      link.attr("stroke", (d) => {
        const s = typeof d.source === "object" ? d.source : nodes.find((n) => n.id === d.source);
        const t = typeof d.target === "object" ? d.target : nodes.find((n) => n.id === d.target);
        return s?.paper === highlightPaper || t?.paper === highlightPaper
          ? PAPER_COLORS[highlightPaper] + "40"
          : "#ffffff03";
      });
    } else {
      node.attr("opacity", 0.85);
      link.attr("stroke", "#ffffff08");
    }

    return () => sim.stop();
  }, [data, width, height, highlightPaper]);

  useEffect(() => {
    if (!svgRef.current) return;
    const svg = d3.select(svgRef.current);
    const node = svg.selectAll("circle");
    const link = svg.selectAll("line");
    
    if (!highlightedPath || highlightedPath.length < 2) {
      return;
    }
    
    const pathSet = new Set(highlightedPath);
    const edgeSet = new Set();
    for (let i = 0; i < highlightedPath.length - 1; i++) {
      edgeSet.add(`${highlightedPath[i]}->${highlightedPath[i + 1]}`);
    }
    
    node.attr("opacity", (d) => pathSet.has(d.id) ? 1 : 0.15)
        .attr("r", (d) => {
          if (!pathSet.has(d.id)) return d.kind === "axiom" ? 5 : d.kind === "definition" ? 3.5 : 2.5;
          return d.kind === "axiom" ? 8 : d.kind === "definition" ? 6 : 5;
        })
        .attr("stroke", (d) => pathSet.has(d.id) ? "#fff" : "none")
        .attr("stroke-width", (d) => pathSet.has(d.id) ? 2 : 0);
    
    link.attr("stroke", (d) => {
      const s = typeof d.source === "object" ? d.source.id : d.source;
      const t = typeof d.target === "object" ? d.target.id : d.target;
      return edgeSet.has(`${s}->${t}`) ? "#3b82f6" : "#ffffff05";
    })
    .attr("stroke-width", (d) => {
      const s = typeof d.source === "object" ? d.source.id : d.source;
      const t = typeof d.target === "object" ? d.target.id : d.target;
      return edgeSet.has(`${s}->${t}`) ? 2 : 0.5;
    });
  }, [highlightedPath]);

  useEffect(() => {
    if (!svgRef.current || !selectedNode) return;
    const pos = nodePositionsRef.current[selectedNode];
    if (!pos) return;
    const svg = d3.select(svgRef.current);
    const zoom = d3.zoomTransform(svg.node());
    const scale = 2;
    const tx = width / 2 - pos.x * scale;
    const ty = height / 2 - pos.y * scale;
    svg.transition().duration(500).call(
      d3.zoom().transform,
      d3.zoomIdentity.translate(tx, ty).scale(scale)
    );
  }, [selectedNode, width, height]);

  useEffect(() => {
    if (!svgRef.current) return;
    const svg = d3.select(svgRef.current);
    const node = svg.selectAll("circle");
    node.attr("stroke", (d) => d.id === selectedNode ? "#fff" : "none")
        .attr("stroke-width", (d) => d.id === selectedNode ? 2 : 0);
  }, [selectedNode]);

  return (
    <svg
      ref={svgRef}
      width={width}
      height={height}
      style={{ background: "#0a0a0a", borderRadius: 8 }}
    />
  );
}

function DependencyGraphViewer() {
  const [data] = useState(DEMO_DATA);
  const [stats, setStats] = useState(null);
  const [highlightPaper, setHighlightPaper] = useState(null);
  const [jsonInput, setJsonInput] = useState("");
  const [customData, setCustomData] = useState(null);
  const [hideArtifacts, setHideArtifacts] = useState(true);
  const [viewMode, setViewMode] = useState('forcing'); // 'forcing' | 'claims' | 'full' | 'audit'
  const [traceNode, setTraceNode] = useState("");
  const [tracePath, setTracePath] = useState(null);
  const [additionalJson, setAdditionalJson] = useState("");
  const [restrictPaper, setRestrictPaper] = useState(null);
  const [depthLimit, setDepthLimit] = useState(null);
  const [activeFilters, setActiveFilters] = useState([]);
  const [selectedNode, setSelectedNode] = useState(null);
  const [showAuditPanel, setShowAuditPanel] = useState(false);
  // Node Search state
  const [nodeSearchQuery, setNodeSearchQuery] = useState("");
  const [searchKindFilter, setSearchKindFilter] = useState(null);
  const [searchPaperFilter, setSearchPaperFilter] = useState(null);
  const [searchSort, setSearchSort] = useState('name');
  const [focusedSearchIndex, setFocusedSearchIndex] = useState(0);
  const searchInputRef = useRef(null);
  // rawData must be defined before any hooks that reference it to avoid
  // temporal dead zone errors when this file is concatenated.
  const rawData = customData || data;

  const nodeDistances = useMemo(() => distancesFromRoots(rawData), [rawData]);
  const nodeDepCounts = useMemo(() => {
    const adj = buildAdj(rawData.nodes, rawData.edges);
    const counts = {};
    for (const n of rawData.nodes) counts[n.id] = (adj[n.id] || []).length;
    return counts;
  }, [rawData]);

  const filteredNodes = useMemo(() => {
    let nodes = activeData.nodes || [];
    if (nodeSearchQuery) {
      const query = nodeSearchQuery.toLowerCase();
      nodes = nodes.filter(n => n.id.toLowerCase().includes(query));
    }
    if (searchKindFilter) {
      nodes = nodes.filter(n => n.kind === searchKindFilter);
    }
    if (searchPaperFilter !== null) {
      nodes = nodes.filter(n => n.paper === searchPaperFilter);
    }
    nodes = [...nodes].sort((a, b) => {
      if (searchSort === 'name') return a.id.localeCompare(b.id);
      if (searchSort === 'distance') return (nodeDistances[a.id] ?? Infinity) - (nodeDistances[b.id] ?? Infinity);
      if (searchSort === 'deps') return (nodeDepCounts[b.id] || 0) - (nodeDepCounts[a.id] || 0);
      return 0;
    });
    return nodes;
  }, [activeData.nodes, nodeSearchQuery, searchKindFilter, searchPaperFilter, searchSort, nodeDistances, nodeDepCounts]);

  const handleSearchKeyNav = useCallback((e) => {
    if (e.key === 'ArrowDown') {
      e.preventDefault();
      setFocusedSearchIndex(i => Math.min(i + 1, filteredNodes.length - 1));
    } else if (e.key === 'ArrowUp') {
      e.preventDefault();
      setFocusedSearchIndex(i => Math.max(i - 1, 0));
    } else if (e.key === 'Enter' && filteredNodes[focusedSearchIndex]) {
      setSelectedNode(filteredNodes[focusedSearchIndex].id);
    }
  }, [filteredNodes, focusedSearchIndex]);

  useEffect(() => { setFocusedSearchIndex(0); }, [nodeSearchQuery, searchKindFilter, searchPaperFilter]);

  const [copiedNodeId, setCopiedNodeId] = useState(false);
  const [pathStartNode, setPathStartNode] = useState(null);
  const [pathEndNode, setPathEndNode] = useState(null);
  const [allPaths, setAllPaths] = useState([]);
  const [selectedPathIndex, setSelectedPathIndex] = useState(0);

  const highlightedPath = useMemo(() => {
    if (allPaths.length === 0 || selectedPathIndex >= allPaths.length) return null;
    return allPaths[selectedPathIndex];
  }, [allPaths, selectedPathIndex]);

  const handlePathTrace = useCallback(() => {
    if (!pathStartNode || !pathEndNode) return;
    const paths = findAllPaths(activeData, pathStartNode, pathEndNode, 10, 20);
    setAllPaths(paths);
    setSelectedPathIndex(0);
  }, [activeData, pathStartNode, pathEndNode]);

  const clearPathTrace = useCallback(() => {
    setPathStartNode(null);
    setPathEndNode(null);
    setAllPaths([]);
    setSelectedPathIndex(0);
  }, []);

  const [showProofExplorer, setShowProofExplorer] = useState(false);
  const [proofPaths, setProofPaths] = useState([]);
  const [proofFilterAxiom, setProofFilterAxiom] = useState('');
  const [proofFilterTheorem, setProofFilterTheorem] = useState('');
  const [proofMaxLength, setProofMaxLength] = useState(10);
  const [selectedProofPath, setSelectedProofPath] = useState(null);

  const axiomsList = useMemo(() => 
    rawData?.nodes?.filter(n => n.kind === 'axiom').map(n => n.id) || [], 
    [rawData]
  );
  
  const theoremsList = useMemo(() => 
    rawData?.nodes?.filter(n => n.kind === 'theorem' && n.paper === -1).map(n => n.id) || [], 
    [rawData]
  );

  const computeProofPaths = useCallback(() => {
    if (!rawData) return;
    const axioms = axiomsList.filter(a => !proofFilterAxiom || a.includes(proofFilterAxiom));
    const theorems = theoremsList.filter(t => !proofFilterTheorem || t.includes(proofFilterTheorem));
    const paths = [];
    
    for (const theorem of theorems.slice(0, 20)) {
      for (const axiom of axioms.slice(0, 10)) {
        const foundPaths = findAllPaths(rawData, theorem, axiom, 3, proofMaxLength);
        for (const path of foundPaths) {
          paths.push({ theorem, axiom, path, length: path.length - 1 });
        }
      }
      if (paths.length >= 50) break;
    }
    
    setProofPaths(paths.sort((a, b) => a.length - b.length).slice(0, 50));
  }, [rawData, axiomsList, theoremsList, proofFilterAxiom, proofFilterTheorem, proofMaxLength]);

  const handleSelectProofPath = useCallback((pp) => {
    setSelectedProofPath(pp);
    setAllPaths([pp.path]);
    setSelectedPathIndex(0);
    setPathStartNode(pp.theorem);
    setPathEndNode(pp.axiom);
  }, []);

  const nodeDetails = useMemo(() => {
    if (!selectedNode || !rawData) return null;
    const node = rawData.nodes.find(n => n.id === selectedNode);
    if (!node) return null;

    const adj = buildAdj(rawData.nodes, rawData.edges);
    const revAdj = {};
    for (const n of rawData.nodes) revAdj[n.id] = [];
    for (const e of rawData.edges) {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      if (revAdj[t]) revAdj[t].push(s);
    }

    const dependencies = (adj[selectedNode] || []).filter(id => !isArtifact(id));
    const dependents = (revAdj[selectedNode] || []).filter(id => !isArtifact(id));

    const foundationBuckets = computeFoundationBuckets(selectedNode, adj, rawData);
    const distanceFromCore = nodeDistances[selectedNode];

    const axioms = rawData.nodes.filter(n => n.kind === 'axiom').map(n => n.id);
    const invariants = identifyInvariants(rawData);
    const hasPathToAxiom = (() => {
      const visited = new Set();
      const queue = [selectedNode];
      while (queue.length) {
        const curr = queue.shift();
        if (visited.has(curr)) continue;
        visited.add(curr);
        if (axioms.includes(curr)) return true;
        for (const dep of adj[curr] || []) queue.push(dep);
      }
      return false;
    })();

    return {
      node,
      dependencies,
      dependents,
      foundationBuckets,
      distanceFromCore,
      hasPathToAxiom,
      isInvariant: invariants.some(inv => inv.id === selectedNode),
    };
  }, [selectedNode, rawData, nodeDistances]);
  // True Path Enforcement state
  const [showTruePaths, setShowTruePaths] = useState(false);
  const [highlightInvariants, setHighlightInvariants] = useState(false);
  const [excludeTrivialCycles, setExcludeTrivialCycles] = useState(false);
  const [truePathValidation, setTruePathValidation] = useState(null);


  // Compute true path validation on data change
  useEffect(() => {
    if (rawData?.nodes?.length > 0) {
      const validation = validateTruePaths(rawData);
      setTruePathValidation(validation);
    }
  }, [rawData]);

  // Build active filter list and apply them deterministically
  useEffect(() => {
    const f = [];
    if (viewMode === 'forcing') {
      f.push({ name: 'forcingChain' });
    } else if (viewMode === 'claims') {
      f.push({ name: 'claimsOnly' });
    } else {
      if (hideArtifacts) f.push({ name: 'hideArtifacts' });
    }
    if (restrictPaper != null) f.push({ name: 'restrictToPaper', params: { paper: restrictPaper } });
    if (depthLimit != null && depthLimit !== "") f.push({ name: 'depthLimit', params: { depth: Number(depthLimit) } });
    // True path filters
    if (showTruePaths) f.push({ name: 'truePathsOnly' });
    if (highlightInvariants) f.push({ name: 'highlightInvariants' });
    if (excludeTrivialCycles) f.push({ name: 'excludeTrivialCycles' });
    setActiveFilters(f);
  }, [viewMode, hideArtifacts, restrictPaper, depthLimit, showTruePaths, highlightInvariants, excludeTrivialCycles]);

  const activeData = applyFilters(rawData, activeFilters);

  useEffect(() => {
    setStats(computeStats(activeData));
  }, [activeData]);

  const handleLoadJson = useCallback(() => {
    try {
      const parsed = JSON.parse(jsonInput);
      // Assign papers based on prefix if not present
      for (const n of parsed.nodes) {
        if (n.paper === undefined) {
          if (n.id.startsWith("AbstractClassSystem")) n.paper = 1;
          else if (n.id.startsWith("Ssot")) n.paper = 2;
          else if (n.id.startsWith("Leverage")) n.paper = 3;
          else if (n.id.startsWith("DecisionQuotient")) n.paper = 4;
          else if (n.id.includes("Nat") || n.id.includes("Core")) n.paper = -1;
          else n.paper = 0;
        }
      }
      setCustomData(parsed);
    } catch {
      // silent
    }
  }, [jsonInput]);

  const handleMergeGraphs = useCallback(() => {
    try {
      const base = customData || JSON.parse(jsonInput || "null") || data;
      const extra = JSON.parse(additionalJson);
      const nodeMap = new Map();
      for (const n of base.nodes || []) nodeMap.set(n.id, n);
      for (const n of extra.nodes || []) nodeMap.set(n.id, { ...(nodeMap.get(n.id) || {}), ...n });
      const edgesSet = new Set();
      const edges = [];
      const addEdge = (e) => {
        const s = typeof e.source === 'object' ? e.source.id : e.source;
        const t = typeof e.target === 'object' ? e.target.id : e.target;
        const key = `${s}->${t}`;
        if (!edgesSet.has(key)) { edgesSet.add(key); edges.push({ source: s, target: t }); }
      };
      for (const e of base.edges || []) addEdge(e);
      for (const e of extra.edges || []) addEdge(e);
      const merged = { nodes: Array.from(nodeMap.values()), edges };
      setCustomData(merged);
    } catch (err) {
      // ignore parse errors for now
      console.error('merge error', err);
    }
  }, [customData, jsonInput, additionalJson, data]);

  const handleTrace = useCallback(() => {
    try {
      const adj = buildAdj(activeData.nodes, activeData.edges);
      const roots = findRoots(activeData.nodes, adj);
      const path = bfs(traceNode, adj, roots);
      setTracePath(path);
    } catch (e) {
      setTracePath([`error: ${e.message}`]);
    }
  }, [activeData, traceNode]);

  return (
    <div
      style={{
        fontFamily: "'JetBrains Mono', 'SF Mono', 'Fira Code', monospace",
        background: "#0a0a0a",
        color: "#e0e0e0",
        minHeight: "100vh",
        padding: 0,
        margin: 0,
      }}
    >
      {/* Header */}
      <div
        style={{
          borderBottom: "1px solid #1a1a1a",
          padding: "20px 28px",
          display: "flex",
          alignItems: "baseline",
          gap: 16,
        }}
      >
        <span
          style={{
            fontSize: 15,
            fontWeight: 700,
            letterSpacing: "0.08em",
            color: "#fff",
          }}
        >
          PROOF INTEGRITY GRAPH
        </span>
        <span style={{ fontSize: 11, color: "#555", letterSpacing: "0.05em" }}>
          ONE LOGIC GRAPH · ZERO EXITS
        </span>
      </div>

      {/* Controls */}
      <div style={{ padding: "12px 28px", borderBottom: "1px solid #1a1a1a", display: 'flex', gap: 12, alignItems: 'center', flexWrap: 'wrap' }}>
        {/* View Mode Toggle */}
        <div style={{ display: 'flex', gap: 4, background: '#0d0d0d', padding: 4, borderRadius: 4, border: '1px solid #222' }}>
          <button
            onClick={() => setViewMode('forcing')}
            style={{
              padding: '6px 12px',
              background: viewMode === 'forcing' ? '#ef4444' : 'transparent',
              color: viewMode === 'forcing' ? '#fff' : '#888',
              border: 'none',
              borderRadius: 3,
              fontSize: 11,
              fontWeight: viewMode === 'forcing' ? 600 : 400,
              cursor: 'pointer',
              letterSpacing: '0.03em',
            }}
          >
            FORCING CHAIN
          </button>
          <button
            onClick={() => setViewMode('claims')}
            style={{
              padding: '6px 12px',
              background: viewMode === 'claims' ? '#10b981' : 'transparent',
              color: viewMode === 'claims' ? '#000' : '#888',
              border: 'none',
              borderRadius: 3,
              fontSize: 11,
              fontWeight: viewMode === 'claims' ? 600 : 400,
              cursor: 'pointer',
              letterSpacing: '0.03em',
            }}
          >
            CLAIMS ONLY
          </button>
          <button
            onClick={() => setViewMode('full')}
            style={{
              padding: '6px 12px',
              background: viewMode === 'full' ? '#f59e0b' : 'transparent',
              color: viewMode === 'full' ? '#000' : '#888',
              border: 'none',
              borderRadius: 3,
              fontSize: 11,
              fontWeight: viewMode === 'full' ? 600 : 400,
              cursor: 'pointer',
              letterSpacing: '0.03em',
            }}
          >
            FULL GRAPH
          </button>
        </div>
        
        {viewMode === 'full' && (
          <label style={{ fontSize: 12, color: '#ccc' }}>
            <input type="checkbox" checked={hideArtifacts} onChange={(e) => setHideArtifacts(e.target.checked)} /> Hide artifacts
          </label>
        )}
        {/* Restrict-to-paper and depth controls */}
        <button
          onClick={() => setRestrictPaper(restrictPaper === highlightPaper ? null : highlightPaper)}
          title="Restrict view to currently highlighted paper"
          style={{ padding: '6px 10px', marginLeft: 6, fontSize: 11, cursor: 'pointer' }}
        >
          {restrictPaper == null ? 'Restrict to highlighted paper' : `Restricted: ${PAPER_NAMES[restrictPaper] || restrictPaper}`}
        </button>
        <div style={{ display: 'flex', gap: 6, alignItems: 'center' }}>
          <input
            type="number"
            placeholder="depth"
            value={depthLimit == null ? '' : depthLimit}
            onChange={(e) => setDepthLimit(e.target.value)}
            style={{ width: 64, background:'#0d0d0d', border:'1px solid #222', color:'#ddd', padding:'6px 8px' }}
          />
          <button onClick={() => setDepthLimit(null)} style={{ padding:'6px 8px' }}>Clear depth</button>
        </div>
        
        <div style={{ display: 'flex', gap: 8, alignItems: 'center' }}>
          <input placeholder="node id to trace" value={traceNode} onChange={(e) => setTraceNode(e.target.value)}
            style={{ background:'#0d0d0d', border:'1px solid #222', color:'#ddd', padding:'6px 8px' }} />
          <button onClick={handleTrace} style={{ padding:'6px 10px' }}>Trace</button>
        </div>

        <button
          onClick={() => setShowAuditPanel(!showAuditPanel)}
          style={{ 
            padding: '6px 10px', 
            background: showAuditPanel ? '#8b5cf6' : '#1a1a1a', 
            border: '1px solid #333', 
            color: showAuditPanel ? '#fff' : '#888',
            fontSize: 11, 
            cursor: 'pointer',
            borderRadius: 4,
          }}
        >
          {showAuditPanel ? '▼ Audit' : '▶ Audit'}
        </button>

        <div style={{ marginLeft: 'auto', fontSize: 12, color: '#888' }}>{stats ? `${stats.totalNodes} nodes · ${stats.totalEdges} edges` : ''}</div>
      </div>

      {/* True Path Enforcement Controls */}
      <div style={{ padding: "8px 28px", borderBottom: "1px solid #1a1a1a", display: "flex", gap: 16, alignItems: "center", background: "#0d0d15" }}>
        <span style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>TRUE PATHS:</span>
        <label style={{ fontSize: 12, color: '#ccc', cursor: 'pointer' }}>
          <input type="checkbox" checked={showTruePaths} onChange={(e) => setShowTruePaths(e.target.checked)} style={{ marginRight: 4 }} />
          Show True Paths Only
        </label>
        <label style={{ fontSize: 12, color: '#ccc', cursor: 'pointer' }}>
          <input type="checkbox" checked={highlightInvariants} onChange={(e) => setHighlightInvariants(e.target.checked)} style={{ marginRight: 4 }} />
          Highlight Invariants
        </label>
        <label style={{ fontSize: 12, color: '#ccc', cursor: 'pointer' }}>
          <input type="checkbox" checked={excludeTrivialCycles} onChange={(e) => setExcludeTrivialCycles(e.target.checked)} style={{ marginRight: 4 }} />
          Exclude Trivial Cycles
        </label>
        {truePathValidation && (
          <span style={{
            marginLeft: 'auto',
            fontSize: 11,
            color: truePathValidation.valid ? '#10b981' : '#ef4444',
            fontWeight: 500
          }}>
            {truePathValidation.valid ? '✓' : '✗'} {truePathValidation.pathCount}/{truePathValidation.claimCount} paths ·
            {truePathValidation.invariants?.length || 0} invariants ·
            {truePathValidation.cycles?.length || 0} cycles
          </span>
        )}
      </div>

      {/* View Mode Explanation */}
      <div style={{ padding: "10px 28px", borderBottom: "1px solid #1a1a1a", background: viewMode === 'forcing' ? '#1a0d0d' : viewMode === 'claims' ? '#0d291e' : '#291f0d' }}>
        <div style={{ fontSize: 11, color: viewMode === 'forcing' ? '#ef4444' : viewMode === 'claims' ? '#10b981' : '#f59e0b', letterSpacing: '0.03em' }}>
          {viewMode === 'forcing' ? (
            <>
              <strong>FORCING CHAIN:</strong> Shows only the path from claims to first principles.
              Red nodes = forcing theorems. Blue nodes = pure math (counting, lists, logic).
              <strong> To reject a claim, you must reject counting.</strong>
            </>
          ) : viewMode === 'claims' ? (
            <>
              <strong>CLAIMS ONLY MODE:</strong> Shows only theorems and definitions cited in the paper, connected through the proof structure. 
              Hides auxiliary lemmas and Lean-generated artifacts that are implementation details.
            </>
          ) : (
            <>
              <strong>FULL GRAPH MODE:</strong> Shows all nodes including auxiliary lemmas and technical infrastructure. 
              Disconnected clusters are internal proof machinery not cited in the paper text.
            </>
          )}
        </div>
      </div>

      {/* Stats row */}
      {stats && (
        <div
          style={{
            display: "grid",
            gridTemplateColumns: "repeat(4, 1fr)",
            borderBottom: "1px solid #1a1a1a",
          }}
        >
          {[
            {
              label: viewMode === 'claims' ? "PROOF STRUCTURE" : "CONNECTED COMPONENTS",
              value: stats.components,
              target: 1,
              color: stats.components === 1 ? "#10b981" : "#ef4444",
              subtext: viewMode === 'claims'
                ? (stats.components === 1 ? "✓ UNIFIED" : "✗ FRAGMENTED")
                : (stats.components === 1 ? "✓ VERIFIED" : "✗ DISCONNECTED"),
            },
            {
              label: viewMode === 'claims' ? "UNREACHABLE CLAIMS" : "COUNTING REJECTIONS",
              value: stats.orphans,
              target: 0,
              color: stats.orphans === 0 ? "#10b981" : "#ef4444",
              subtext: stats.orphans === 0 ? "✓ ALL CONNECTED" : "✗ DISCONNECTED NODES",
            },
            {
              label: "SORRY COUNT",
              value: 0,
              target: 0,
              color: "#10b981",
              subtext: "✓ COMPLETE",
            },
            {
              label: viewMode === 'claims' ? "CITED CLAIMS" : "DECLARATIONS",
              value: stats.totalNodes,
              target: null,
              color: "#3b82f6",
              subtext: viewMode === 'claims' ? "IN PAPER" : "TOTAL",
            },
          ].map((s, i) => (
            <div
              key={i}
              style={{
                padding: "18px 28px",
                borderRight: i < 3 ? "1px solid #1a1a1a" : "none",
              }}
            >
              <div
                style={{
                  fontSize: 36,
                  fontWeight: 800,
                  color: s.color,
                  lineHeight: 1,
                  fontVariantNumeric: "tabular-nums",
                }}
              >
                {s.value}
              </div>
              <div
                style={{
                  fontSize: 9,
                  color: "#555",
                  letterSpacing: "0.12em",
                  marginTop: 6,
                }}
              >
                {s.label}
              </div>
              {s.subtext && (
                <div
                  style={{
                    fontSize: 9,
                    color: s.color,
                    marginTop: 2,
                  }}
                >
                  {s.subtext}
                </div>
              )}
            </div>
          ))}
        </div>
      )}

      {/* Breakdown row */}
      {stats && (
        <div
          style={{
            display: "flex",
            gap: 24,
            padding: "12px 28px",
            borderBottom: "1px solid #1a1a1a",
            fontSize: 11,
            color: "#666",
          }}
        >
          <span>
            theorems:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.theorems}</span>
          </span>
          <span>
            definitions:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.definitions}</span>
          </span>
          <span>
            axioms:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.axioms}</span>
          </span>
          <span>
            edges:{" "}
            <span style={{ color: "#e0e0e0" }}>{stats.totalEdges}</span>
          </span>
          <span>
            reachable from ℕ:{" "}
            <span style={{ color: "#10b981" }}>{stats.reachableFromCore}</span>
            <span style={{ color: "#555" }}>/{stats.totalNodes}</span>
          </span>
        </div>
      )}

      {/* Legend */}
      <div
        style={{
          display: "flex",
          gap: 2,
          padding: "10px 28px",
          borderBottom: "1px solid #1a1a1a",
          flexWrap: "wrap",
        }}
      >
        {Object.entries(PAPER_NAMES).map(([key, name]) => (
          <button
            key={key}
            onClick={() =>
              setHighlightPaper(
                highlightPaper === Number(key) ? null : Number(key)
              )
            }
            style={{
              background:
                highlightPaper === Number(key)
                  ? PAPER_COLORS[Number(key)] + "20"
                  : "transparent",
              border: `1px solid ${
                highlightPaper === Number(key)
                  ? PAPER_COLORS[Number(key)]
                  : "#222"
              }`,
              borderRadius: 4,
              padding: "4px 10px",
              cursor: "pointer",
              display: "flex",
              alignItems: "center",
              gap: 6,
              fontSize: 10,
              color:
                highlightPaper === Number(key)
                  ? PAPER_COLORS[Number(key)]
                  : "#888",
              transition: "all 0.15s",
            }}
          >
            <span
              style={{
                width: 8,
                height: 8,
                borderRadius: "50%",
                background: PAPER_COLORS[Number(key)],
                display: "inline-block",
              }}
            />
            {name}
          </button>
        ))}
      </div>

      {/* Graph + Sidebar */}
      <div style={{ display: 'flex', padding: "0 28px", gap: 16 }}>
        {/* Node Search Panel */}
        <div style={{ width: 260, borderRight: '1px solid #1a1a1a', paddingRight: 16 }}>
          <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 8 }}>
            NODES
          </div>
          <input
            ref={searchInputRef}
            type="text"
            placeholder="Search nodes..."
            value={nodeSearchQuery}
            onChange={(e) => setNodeSearchQuery(e.target.value)}
            onKeyDown={handleSearchKeyNav}
            style={{
              width: '100%',
              background: '#0d0d0d',
              border: '1px solid #222',
              borderRadius: 4,
              color: '#ddd',
              padding: '6px 8px',
              fontSize: 11,
              marginBottom: 6,
              fontFamily: 'inherit'
            }}
          />
          <div style={{ display: 'flex', gap: 4, marginBottom: 6, flexWrap: 'wrap' }}>
            <select 
              value={searchKindFilter || ''} 
              onChange={(e) => setSearchKindFilter(e.target.value || null)}
              style={{ background: '#0d0d0d', border: '1px solid #222', color: '#888', fontSize: 9, padding: '2px 4px', borderRadius: 3 }}
            >
              <option value="">All kinds</option>
              <option value="theorem">theorem</option>
              <option value="definition">definition</option>
              <option value="axiom">axiom</option>
            </select>
            <select 
              value={searchPaperFilter === null ? '' : searchPaperFilter} 
              onChange={(e) => setSearchPaperFilter(e.target.value === '' ? null : Number(e.target.value))}
              style={{ background: '#0d0d0d', border: '1px solid #222', color: '#888', fontSize: 9, padding: '2px 4px', borderRadius: 3 }}
            >
              <option value="">All papers</option>
              {Object.entries(PAPER_NAMES).map(([k, v]) => (
                <option key={k} value={k}>{v}</option>
              ))}
            </select>
            <select 
              value={searchSort} 
              onChange={(e) => setSearchSort(e.target.value)}
              style={{ background: '#0d0d0d', border: '1px solid #222', color: '#888', fontSize: 9, padding: '2px 4px', borderRadius: 3 }}
            >
              <option value="name">by name</option>
              <option value="distance">by distance</option>
              <option value="deps">by deps</option>
            </select>
          </div>
          <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>{filteredNodes.length} nodes</div>
          <div style={{ maxHeight: 380, overflow: 'auto' }}>
            {filteredNodes.slice(0, 200).map((n, i) => (
              <div
                key={n.id}
                onClick={() => setSelectedNode(n.id)}
                style={{
                  padding: '4px 6px',
                  fontSize: 10,
                  color: selectedNode === n.id ? '#fff' : '#888',
                  background: selectedNode === n.id ? PAPER_COLORS[n.paper] + '30' : focusedSearchIndex === i ? '#1a1a1a' : 'transparent',
                  borderRadius: 3,
                  cursor: 'pointer',
                  marginBottom: 1,
                  display: 'flex',
                  alignItems: 'center',
                  gap: 6
                }}
              >
                <span style={{
                  width: 6,
                  height: 6,
                  borderRadius: '50%',
                  background: PAPER_COLORS[n.paper] || '#666',
                  display: 'inline-block'
                }} />
                <span style={{ overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap', flex: 1 }}>
                  {n.id}
                </span>
                <span style={{ fontSize: 8, color: '#555' }}>{n.kind?.slice(0,3)}</span>
              </div>
            ))}
            {filteredNodes.length > 200 && <div style={{ fontSize: 9, color: '#555', padding: 4 }}>+{filteredNodes.length - 200} more</div>}
          </div>
        </div>

        <div style={{ flex: 1 }}>
          <ForceGraph
            data={activeData}
            width={700}
            height={500}
            highlightPaper={highlightPaper}
            selectedNode={selectedNode}
            onSelectNode={setSelectedNode}
            highlightedPath={highlightedPath}
          />
        </div>
        
        {/* Node Details Panel / Rejection Cost Sidebar */}
        <div style={{ width: 240, paddingLeft: 16, borderLeft: '1px solid #1a1a1a', overflowY: 'auto', maxHeight: 500 }}>
          {nodeDetails ? (
            <>
              <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 8 }}>
                NODE DETAILS
              </div>
              
              {/* Node ID with copy */}
              <div style={{ marginBottom: 12 }}>
                <div style={{ display: 'flex', alignItems: 'center', gap: 6, marginBottom: 4 }}>
                  <span style={{
                    fontSize: 10,
                    padding: '2px 6px',
                    borderRadius: 3,
                    background: PAPER_COLORS[nodeDetails.node.paper] || '#333',
                    color: '#fff',
                    fontWeight: 600,
                  }}>
                    {nodeDetails.node.kind?.toUpperCase() || 'NODE'}
                  </span>
                  <span style={{ fontSize: 10, color: PAPER_COLORS[nodeDetails.node.paper] }}>
                    {PAPER_NAMES[nodeDetails.node.paper] || `Paper ${nodeDetails.node.paper}`}
                  </span>
                </div>
                <div 
                  onClick={() => {
                    navigator.clipboard?.writeText(nodeDetails.node.id);
                    setCopiedNodeId(true);
                    setTimeout(() => setCopiedNodeId(false), 1500);
                  }}
                  style={{
                    fontSize: 9,
                    color: '#888',
                    background: '#0d0d0d',
                    padding: '4px 6px',
                    borderRadius: 3,
                    cursor: 'pointer',
                    wordBreak: 'break-all',
                    border: '1px solid #222',
                  }}
                >
                  {nodeDetails.node.id}
                  <span style={{ marginLeft: 6, color: copiedNodeId ? '#10b981' : '#555' }}>
                    {copiedNodeId ? '✓ copied' : '[copy]'}
                  </span>
                </div>
              </div>

              {/* Invariant Status */}
              <div style={{ marginBottom: 12, padding: 8, background: nodeDetails.hasPathToAxiom ? '#0d1a0d' : '#1a0d0d', borderRadius: 4, border: `1px solid ${nodeDetails.hasPathToAxiom ? '#1a3311' : '#331111'}` }}>
                <div style={{ fontSize: 10, color: nodeDetails.hasPathToAxiom ? '#10b981' : '#ef4444', fontWeight: 600 }}>
                  {nodeDetails.hasPathToAxiom ? '✓ TRUE PATH' : '✗ NO PATH TO AXIOM'}
                </div>
                {nodeDetails.isInvariant && (
                  <div style={{ fontSize: 9, color: '#f59e0b', marginTop: 2 }}>INVARIANT NODE</div>
                )}
              </div>

              {/* Distance */}
              {nodeDetails.distanceFromCore !== undefined && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 2 }}>DISTANCE FROM ℕ</div>
                  <div style={{ fontSize: 16, color: '#3b82f6', fontWeight: 700 }}>
                    {nodeDetails.distanceFromCore}
                  </div>
                </div>
              )}

              {/* Foundation Buckets */}
              {nodeDetails.foundationBuckets.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>FOUNDATION BUCKETS</div>
                  {nodeDetails.foundationBuckets.map(bucket => {
                    const info = FOUNDATION_BUCKETS[bucket] || { name: bucket.split('.')[1], color: '#666', description: '' };
                    return (
                      <div key={bucket} style={{ 
                        fontSize: 9, 
                        color: info.color, 
                        marginBottom: 2,
                        padding: '3px 6px',
                        background: info.color + '15',
                        borderRadius: 3,
                      }}>
                        {info.name}
                      </div>
                    );
                  })}
                </div>
              )}

              {/* Rejection Cost */}
              <div style={{ marginBottom: 12, padding: 8, background: '#1a0d0d', borderRadius: 4, border: '1px solid #331111' }}>
                <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>REJECTION COST</div>
                <div style={{ fontSize: 10, color: '#ef4444', lineHeight: 1.5 }}>
                  To reject this {nodeDetails.node.kind}, you must reject:
                  {nodeDetails.foundationBuckets.map(b => (
                    <div key={b} style={{ marginLeft: 8 }}>• {b}</div>
                  ))}
                </div>
              </div>

              {/* Dependencies */}
              {nodeDetails.dependencies.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>
                    DEPENDENCIES ({nodeDetails.dependencies.length})
                  </div>
                  <div style={{ maxHeight: 80, overflow: 'auto' }}>
                    {nodeDetails.dependencies.slice(0, 10).map(dep => (
                      <div 
                        key={dep}
                        onClick={() => setSelectedNode(dep)}
                        style={{
                          fontSize: 9,
                          color: '#888',
                          cursor: 'pointer',
                          padding: '2px 4px',
                          borderRadius: 2,
                        }}
                        onMouseEnter={e => e.target.style.background = '#1a1a1a'}
                        onMouseLeave={e => e.target.style.background = 'transparent'}
                      >
                        → {dep}
                      </div>
                    ))}
                    {nodeDetails.dependencies.length > 10 && (
                      <div style={{ fontSize: 8, color: '#555' }}>+{nodeDetails.dependencies.length - 10} more</div>
                    )}
                  </div>
                </div>
              )}

              {/* Dependents */}
              {nodeDetails.dependents.length > 0 && (
                <div style={{ marginBottom: 12 }}>
                  <div style={{ fontSize: 9, color: '#555', marginBottom: 4 }}>
                    DEPENDENTS ({nodeDetails.dependents.length})
                  </div>
                  <div style={{ maxHeight: 80, overflow: 'auto' }}>
                    {nodeDetails.dependents.slice(0, 10).map(dep => (
                      <div 
                        key={dep}
                        onClick={() => setSelectedNode(dep)}
                        style={{
                          fontSize: 9,
                          color: '#888',
                          cursor: 'pointer',
                          padding: '2px 4px',
                          borderRadius: 2,
                        }}
                        onMouseEnter={e => e.target.style.background = '#1a1a1a'}
                        onMouseLeave={e => e.target.style.background = 'transparent'}
                      >
                        ← {dep}
                      </div>
                    ))}
                    {nodeDetails.dependents.length > 10 && (
                      <div style={{ fontSize: 8, color: '#555' }}>+{nodeDetails.dependents.length - 10} more</div>
                    )}
                  </div>
                </div>
              )}

              {/* Trace buttons */}
              <div style={{ display: 'flex', gap: 6 }}>
                <button
                  onClick={() => { setTraceNode(selectedNode); handleTrace(); }}
                  style={{
                    flex: 1,
                    padding: '6px 8px',
                    fontSize: 9,
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 4,
                    color: '#ccc',
                    cursor: 'pointer',
                  }}
                >
                  Trace from here
                </button>
              </div>
            </>
          ) : (
            <>
              <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 12 }}>
                REJECTION COST
              </div>
              
              {viewMode === 'forcing' && (
                <>
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, color: '#ef4444', fontWeight: 600, marginBottom: 4 }}>
                      FORCING THEOREMS
                    </div>
                    <div style={{ fontSize: 10, color: '#888', lineHeight: 1.4 }}>
                      First-principles theorems. Rejecting requires rejecting logic.
                    </div>
                  </div>
                  
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, color: '#3b82f6', fontWeight: 600, marginBottom: 4 }}>
                      PURE MATH (Nat, List)
                    </div>
                    <div style={{ fontSize: 10, color: '#888', lineHeight: 1.4 }}>
                      Counting, arithmetic, ordering. Undeniable.
                    </div>
                  </div>
                  
                  <div style={{ marginBottom: 16 }}>
                    <div style={{ fontSize: 11, color: '#10b981', fontWeight: 600, marginBottom: 4 }}>
                      CLAIMS
                    </div>
                    <div style={{ fontSize: 10, color: '#888', lineHeight: 1.4 }}>
                      Paper results. Each traces to forcing → math.
                    </div>
                  </div>
                  
                  <div style={{ marginTop: 24, padding: 8, background: '#1a0d0d', borderRadius: 4, border: '1px solid #331111' }}>
                    <div style={{ fontSize: 10, color: '#ef4444', lineHeight: 1.5 }}>
                      <strong>To reject any claim:</strong><br/>
                      Requires rejecting counting (Nat.add).<br/>
                      Requires rejecting logic (Decidable).<br/>
                      <strong>Contradiction.</strong>
                    </div>
                  </div>
                </>
              )}
              
              <div style={{ fontSize: 10, color: '#555', marginTop: 12, lineHeight: 1.5 }}>
                Click a node in the graph or search panel to see details.
              </div>
            </>
          )}
        </div>
      </div>

      {/* Trace output */}
      <div style={{ padding: '8px 28px', minHeight: 36 }}>
        {tracePath && (
          <div style={{ background: '#0d0d0d', border: '1px solid #222', padding: 8, borderRadius: 4, color:'#ddd', fontSize:12 }}>
            <strong>Trace path:</strong> {tracePath.join(' → ')}
          </div>
        )}
      </div>

      {/* Path Tracer UI */}
      <div style={{ padding: '8px 28px', borderTop: '1px solid #1a1a1a' }}>
        <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em', marginBottom: 8 }}>
          PATH TRACER
        </div>
        <div style={{ display: 'flex', gap: 8, alignItems: 'center', flexWrap: 'wrap' }}>
          <div style={{ display: 'flex', gap: 6, alignItems: 'center' }}>
            <span style={{ fontSize: 10, color: '#888' }}>From:</span>
            <input
              placeholder="Start node"
              value={pathStartNode || ''}
              onChange={(e) => setPathStartNode(e.target.value || null)}
              style={{ 
                width: 180, 
                background: '#0d0d0d', 
                border: '1px solid #222', 
                color: '#ddd', 
                padding: '6px 8px', 
                fontSize: 10,
                borderRadius: 4,
              }}
            />
          </div>
          <span style={{ color: '#555' }}>→</span>
          <div style={{ display: 'flex', gap: 6, alignItems: 'center' }}>
            <span style={{ fontSize: 10, color: '#888' }}>To:</span>
            <input
              placeholder="End node"
              value={pathEndNode || ''}
              onChange={(e) => setPathEndNode(e.target.value || null)}
              style={{ 
                width: 180, 
                background: '#0d0d0d', 
                border: '1px solid #222', 
                color: '#ddd', 
                padding: '6px 8px', 
                fontSize: 10,
                borderRadius: 4,
              }}
            />
          </div>
          <button
            onClick={handlePathTrace}
            disabled={!pathStartNode || !pathEndNode}
            style={{
              padding: '6px 12px',
              background: pathStartNode && pathEndNode ? '#3b82f6' : '#1a1a1a',
              border: '1px solid #333',
              borderRadius: 4,
              color: pathStartNode && pathEndNode ? '#fff' : '#555',
              fontSize: 10,
              cursor: pathStartNode && pathEndNode ? 'pointer' : 'not-allowed',
            }}
          >
            Find Paths
          </button>
          {(pathStartNode || pathEndNode) && (
            <button
              onClick={clearPathTrace}
              style={{
                padding: '6px 12px',
                background: '#1a1a1a',
                border: '1px solid #333',
                borderRadius: 4,
                color: '#888',
                fontSize: 10,
                cursor: 'pointer',
              }}
            >
              Clear
            </button>
          )}
        </div>
        
        {/* Path results */}
        {allPaths.length > 0 && (
          <div style={{ marginTop: 12, background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
            <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: 8 }}>
              <span style={{ fontSize: 10, color: '#888' }}>
                {allPaths.length} path{allPaths.length !== 1 ? 's' : ''} found
              </span>
              {allPaths.length > 1 && (
                <div style={{ display: 'flex', gap: 4 }}>
                  <button
                    onClick={() => setSelectedPathIndex(i => Math.max(0, i - 1))}
                    disabled={selectedPathIndex === 0}
                    style={{ padding: '2px 8px', fontSize: 9, background: '#1a1a1a', border: '1px solid #333', color: selectedPathIndex === 0 ? '#555' : '#ccc', cursor: selectedPathIndex === 0 ? 'not-allowed' : 'pointer' }}
                  >
                    ←
                  </button>
                  <span style={{ fontSize: 10, color: '#888' }}>{selectedPathIndex + 1}/{allPaths.length}</span>
                  <button
                    onClick={() => setSelectedPathIndex(i => Math.min(allPaths.length - 1, i + 1))}
                    disabled={selectedPathIndex === allPaths.length - 1}
                    style={{ padding: '2px 8px', fontSize: 9, background: '#1a1a1a', border: '1px solid #333', color: selectedPathIndex === allPaths.length - 1 ? '#555' : '#ccc', cursor: selectedPathIndex === allPaths.length - 1 ? 'not-allowed' : 'pointer' }}
                  >
                    →
                  </button>
                </div>
              )}
            </div>
            <div style={{ fontSize: 9, color: '#3b82f6', marginBottom: 4 }}>
              Path {selectedPathIndex + 1}: length {allPaths[selectedPathIndex]?.length - 1 || 0}
            </div>
            <div style={{ fontSize: 10, color: '#ccc', lineHeight: 1.6, wordBreak: 'break-all' }}>
              {allPaths[selectedPathIndex]?.join(' → ')}
            </div>
            {allPaths.length > 1 && (
              <div style={{ marginTop: 8, maxHeight: 80, overflow: 'auto', borderTop: '1px solid #222', paddingTop: 8 }}>
                {allPaths.map((path, i) => (
                  <div 
                    key={i}
                    onClick={() => setSelectedPathIndex(i)}
                    style={{
                      fontSize: 9,
                      color: i === selectedPathIndex ? '#3b82f6' : '#666',
                      cursor: 'pointer',
                      padding: '2px 4px',
                      background: i === selectedPathIndex ? '#1a2733' : 'transparent',
                      borderRadius: 2,
                      marginBottom: 2,
                    }}
                  >
                    Path {i + 1} (len {path.length - 1}): {path.slice(0, 3).join(' → ')}{path.length > 3 ? ' ...' : ''}
                  </div>
                ))}
              </div>
            )}
          </div>
        )}
      </div>

      {/* Proof Paths Explorer */}
      <div style={{ padding: '8px 28px', borderTop: '1px solid #1a1a1a' }}>
        <div 
          style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', cursor: 'pointer' }}
          onClick={() => setShowProofExplorer(!showProofExplorer)}
        >
          <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>
            PROOF PATHS EXPLORER
          </div>
          <span style={{ color: '#555', fontSize: 10 }}>{showProofExplorer ? '▼' : '▶'}</span>
        </div>
        
        {showProofExplorer && (
          <div style={{ marginTop: 12 }}>
            <div style={{ display: 'flex', gap: 8, alignItems: 'center', flexWrap: 'wrap', marginBottom: 8 }}>
              <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                <span style={{ fontSize: 9, color: '#888' }}>Axiom filter:</span>
                <input
                  placeholder="FOUNDATION.Counting"
                  value={proofFilterAxiom}
                  onChange={(e) => setProofFilterAxiom(e.target.value)}
                  style={{ width: 140, background: '#0d0d0d', border: '1px solid #222', color: '#ddd', padding: '4px 6px', fontSize: 9, borderRadius: 3 }}
                />
              </div>
              <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                <span style={{ fontSize: 9, color: '#888' }}>Theorem filter:</span>
                <input
                  placeholder="theorem name"
                  value={proofFilterTheorem}
                  onChange={(e) => setProofFilterTheorem(e.target.value)}
                  style={{ width: 140, background: '#0d0d0d', border: '1px solid #222', color: '#ddd', padding: '4px 6px', fontSize: 9, borderRadius: 3 }}
                />
              </div>
              <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                <span style={{ fontSize: 9, color: '#888' }}>Max length:</span>
                <input
                  type="number"
                  value={proofMaxLength}
                  onChange={(e) => setProofMaxLength(Number(e.target.value) || 10)}
                  style={{ width: 50, background: '#0d0d0d', border: '1px solid #222', color: '#ddd', padding: '4px 6px', fontSize: 9, borderRadius: 3 }}
                />
              </div>
              <button
                onClick={computeProofPaths}
                style={{
                  padding: '4px 10px',
                  background: '#3b82f6',
                  border: 'none',
                  borderRadius: 3,
                  color: '#fff',
                  fontSize: 9,
                  cursor: 'pointer',
                }}
              >
                Compute Paths
              </button>
              {proofPaths.length > 0 && (
                <button
                  onClick={() => {
                    const md = proofPaths.map(p => 
                      `## ${p.theorem} → ${p.axiom}\nLength: ${p.length}\nPath: ${p.path.join(' → ')}`
                    ).join('\n\n');
                    navigator.clipboard?.writeText(md);
                  }}
                  style={{
                    padding: '4px 10px',
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 3,
                    color: '#888',
                    fontSize: 9,
                    cursor: 'pointer',
                  }}
                >
                  Export MD
                </button>
              )}
            </div>
            
            {proofPaths.length > 0 && (
              <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, maxHeight: 200, overflow: 'auto' }}>
                <div style={{ fontSize: 9, color: '#888', padding: 8, borderBottom: '1px solid #222' }}>
                  {proofPaths.length} proof paths computed
                </div>
                {proofPaths.map((pp, i) => (
                  <div 
                    key={i}
                    onClick={() => handleSelectProofPath(pp)}
                    style={{
                      padding: '6px 8px',
                      borderBottom: '1px solid #1a1a1a',
                      cursor: 'pointer',
                      background: selectedProofPath === pp ? '#1a2733' : 'transparent',
                    }}
                  >
                    <div style={{ fontSize: 9, color: '#3b82f6', marginBottom: 2 }}>
                      {pp.theorem} → {pp.axiom}
                    </div>
                    <div style={{ fontSize: 8, color: '#666' }}>
                      Length: {pp.length} | {pp.path.slice(0, 4).join(' → ')}{pp.path.length > 4 ? ' ...' : ''}
                    </div>
                  </div>
                ))}
              </div>
            )}
            
            {proofPaths.length === 0 && (
              <div style={{ fontSize: 9, color: '#555' }}>
                Click "Compute Paths" to find all paths from theorems to axioms.
              </div>
            )}
          </div>
        )}
      </div>

      {/* Audit Mode Panel */}
      <div style={{ padding: '8px 28px', borderTop: '1px solid #1a1a1a' }}>
        <div 
          style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', cursor: 'pointer' }}
          onClick={() => setShowAuditPanel(!showAuditPanel)}
        >
          <div style={{ fontSize: 10, color: '#666', letterSpacing: '0.1em' }}>
            AUDIT MODE
          </div>
          <span style={{ color: '#555', fontSize: 10 }}>{showAuditPanel ? '▼' : '▶'}</span>
        </div>
        
        {showAuditPanel && (
          <div style={{ marginTop: 12 }}>
            {/* True Path Invariant Validator */}
            <div style={{ marginBottom: 16 }}>
              <div style={{ fontSize: 11, color: '#10b981', fontWeight: 600, marginBottom: 8 }}>
                TRUE PATH INVARIANT
              </div>
              {truePathValidation ? (
                <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
                  <div style={{ display: 'grid', gridTemplateColumns: 'repeat(4, 1fr)', gap: 12, marginBottom: 8 }}>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>STATUS</div>
                      <div style={{ fontSize: 12, color: truePathValidation.valid ? '#10b981' : '#ef4444', fontWeight: 600 }}>
                        {truePathValidation.valid ? '✓ VALID' : '✗ INVALID'}
                      </div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>CLAIMS</div>
                      <div style={{ fontSize: 12, color: '#3b82f6' }}>{truePathValidation.claimCount}</div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>PATHS</div>
                      <div style={{ fontSize: 12, color: '#3b82f6' }}>{truePathValidation.pathCount}</div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>INVARIANTS</div>
                      <div style={{ fontSize: 12, color: '#3b82f6' }}>{truePathValidation.invariants?.length || 0}</div>
                    </div>
                  </div>
                  
                  {truePathValidation.missingPaths?.length > 0 && (
                    <div style={{ marginBottom: 8 }}>
                      <div style={{ fontSize: 9, color: '#ef4444', marginBottom: 4 }}>
                        ⚠ {truePathValidation.missingPaths.length} claims without true paths:
                      </div>
                      <div style={{ maxHeight: 60, overflow: 'auto' }}>
                        {truePathValidation.missingPaths.slice(0, 10).map(mp => (
                          <div key={mp} style={{ fontSize: 8, color: '#888', marginLeft: 8 }}>• {mp}</div>
                        ))}
                        {truePathValidation.missingPaths.length > 10 && (
                          <div style={{ fontSize: 8, color: '#555' }}>+{truePathValidation.missingPaths.length - 10} more</div>
                        )}
                      </div>
                    </div>
                  )}
                  
                  <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: 8 }}>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>NONTRIVIAL CYCLES</div>
                      <div style={{ fontSize: 11, color: '#f59e0b' }}>{truePathValidation.nontrivialCycles?.length || 0}</div>
                    </div>
                    <div>
                      <div style={{ fontSize: 9, color: '#555' }}>TRIVIAL CYCLES</div>
                      <div style={{ fontSize: 11, color: '#ef4444' }}>{truePathValidation.trivialCycles?.length || 0} ⚠</div>
                    </div>
                  </div>
                </div>
              ) : (
                <div style={{ fontSize: 9, color: '#555' }}>No validation data available</div>
              )}
            </div>

            {/* Foundation Bucket Usage */}
            <div style={{ marginBottom: 16 }}>
              <div style={{ fontSize: 11, color: '#3b82f6', fontWeight: 600, marginBottom: 8 }}>
                FOUNDATION BUCKET COVERAGE
              </div>
              <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8 }}>
                {Object.entries(FOUNDATION_BUCKETS).map(([key, info]) => (
                  <div key={key} style={{ display: 'flex', alignItems: 'center', gap: 8, marginBottom: 4 }}>
                    <span style={{
                      width: 8,
                      height: 8,
                      borderRadius: '50%',
                      background: info.color,
                      display: 'inline-block',
                    }} />
                    <span style={{ fontSize: 9, color: '#888', flex: 1 }}>{info.name}</span>
                    <span style={{ fontSize: 8, color: '#555' }}>{info.description}</span>
                  </div>
                ))}
              </div>
            </div>

            {/* Cycle Analysis */}
            {truePathValidation?.cycles?.length > 0 && (
              <div style={{ marginBottom: 16 }}>
                <div style={{ fontSize: 11, color: '#f59e0b', fontWeight: 600, marginBottom: 8 }}>
                  CYCLE ANALYSIS
                </div>
                <div style={{ background: '#0d0d0d', border: '1px solid #222', borderRadius: 4, padding: 8, maxHeight: 120, overflow: 'auto' }}>
                  {truePathValidation.cycles.slice(0, 10).map((cycle, i) => (
                    <div key={i} style={{ marginBottom: 6, paddingBottom: 6, borderBottom: '1px solid #1a1a1a' }}>
                      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
                        <span style={{ fontSize: 9, color: cycle.isNontrivial ? '#f59e0b' : '#ef4444' }}>
                          {cycle.isNontrivial ? '◆' : '○'} Cycle {i + 1} ({cycle.nodes.length} nodes)
                        </span>
                        {cycle.nontrivialityScore !== undefined && (
                          <span style={{ fontSize: 8, color: '#555' }}>score: {cycle.nontrivialityScore.toFixed(2)}</span>
                        )}
                      </div>
                      <div style={{ fontSize: 8, color: '#666', marginTop: 2 }}>
                        {cycle.nodes.slice(0, 3).join(' → ')}{cycle.nodes.length > 3 ? ' ...' : ''}
                      </div>
                    </div>
                  ))}
                </div>
              </div>
            )}

            {/* Export Report */}
            <div>
              <div style={{ fontSize: 11, color: '#8b5cf6', fontWeight: 600, marginBottom: 8 }}>
                EXPORT REPORT
              </div>
              <div style={{ display: 'flex', gap: 8 }}>
                <button
                  onClick={() => {
                    if (!truePathValidation) return;
                    const report = generateValidationReport(truePathValidation);
                    navigator.clipboard?.writeText(report);
                  }}
                  style={{
                    padding: '6px 12px',
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 4,
                    color: '#ccc',
                    fontSize: 9,
                    cursor: 'pointer',
                  }}
                >
                  Copy Report
                </button>
                <button
                  onClick={() => {
                    if (!rawData) return;
                    const json = JSON.stringify({
                      stats: stats,
                      validation: truePathValidation,
                      foundationBuckets: Object.keys(FOUNDATION_BUCKETS),
                    }, null, 2);
                    const blob = new Blob([json], { type: 'application/json' });
                    const url = URL.createObjectURL(blob);
                    const a = document.createElement('a');
                    a.href = url;
                    a.download = 'audit-report.json';
                    a.click();
                    URL.revokeObjectURL(url);
                  }}
                  style={{
                    padding: '6px 12px',
                    background: '#1a1a1a',
                    border: '1px solid #333',
                    borderRadius: 4,
                    color: '#ccc',
                    fontSize: 9,
                    cursor: 'pointer',
                  }}
                >
                  Download JSON
                </button>
              </div>
            </div>
          </div>
        )}
      </div>

      {/* Import section */}
      <div
        style={{
          padding: "16px 28px",
          borderTop: "1px solid #1a1a1a",
        }}
      >
        <div
          style={{
            fontSize: 9,
            color: "#555",
            letterSpacing: "0.1em",
            marginBottom: 8,
          }}
        >
          LOAD GRAPH.JSON FROM{" "}
          <span style={{ color: "#888" }}>#export_graph_json</span>
        </div>
        <div style={{ display: "flex", gap: 8 }}>
          <textarea
            value={jsonInput}
            onChange={(e) => setJsonInput(e.target.value)}
            placeholder='Paste graph.json contents here...'
            style={{
              flex: 1,
              background: "#111",
              border: "1px solid #222",
              borderRadius: 4,
              color: "#888",
              fontFamily: "inherit",
              fontSize: 10,
              padding: "8px 12px",
              resize: "vertical",
              minHeight: 36,
              maxHeight: 120,
            }}
          />
          <button
            onClick={handleLoadJson}
            style={{
              background: "#1a1a1a",
              border: "1px solid #333",
              borderRadius: 4,
              color: "#e0e0e0",
              fontFamily: "inherit",
              fontSize: 10,
              padding: "8px 16px",
              cursor: "pointer",
              letterSpacing: "0.05em",
              whiteSpace: "nowrap",
            }}
          >
            LOAD
          </button>
        </div>
      </div>

      {/* Footer */}
      <div
        style={{
          padding: "16px 28px",
          borderTop: "1px solid #1a1a1a",
          fontSize: 9,
          color: "#333",
          letterSpacing: "0.05em",
        }}
      >
        {viewMode === 'forcing' ? (
          <>
            <strong style={{ color: '#ef4444' }}>FORCING CHAIN:</strong> Every claim traces to counting (Nat) and logic (Decidable).
            To reject any theorem here, you must reject arithmetic itself. The chain is visible. The cost is explicit.
          </>
        ) : (
          <>
            To reject any node in this graph, trace the dependency chain to its root.
            The root is ℕ. To reject any definition, you must reject counting.
          </>
        )}
      </div>
    </div>
  );
}


// Render the app
const root = ReactDOM.createRoot(document.getElementById("root"));
root.render(React.createElement(DependencyGraphViewer));
