// Shared graph utilities used by graph viewers
// Re-export true path enforcement module
export {
  identifyInvariants,
  shortestPath,
  shortestPathThroughInvariants,
  computeAllTruePaths,
  detectCycles,
  classifyCycleTriviality,
  computeNontrivialityScore,
  validateTruePaths,
  generateValidationReport,
  TRUE_PATH_FILTERS
} from './true_path.js';

// Lean compiler-generated artifacts that aren't part of the paper's claims
export const ARTIFACT_PATTERNS = [
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

export function isArtifact(id) {
  return ARTIFACT_PATTERNS.some((re) => re.test(id));
}

export function buildAdj(nodes, edges) {
  const a = {};
  for (const n of nodes) a[n.id] = [];
  for (const e of edges) {
    const s = typeof e.source === 'object' ? e.source.id : e.source;
    const t = typeof e.target === 'object' ? e.target.id : e.target;
    if (a[s]) a[s].push(t);
  }
  return a;
}

export function findRoots(nodes, adj) {
  return new Set(nodes.filter((n) => (adj[n.id] || []).length === 0).map((n) => n.id));
}

export function bfs(start, adj, targets) {
  if (targets.has(start)) return [start];
  const v = new Set([start]), par = {}, q = [start];
  while (q.length) {
    const c = q.shift();
    if (targets.has(c)) {
      const p = [];
      for (let n = c; n !== undefined; n = par[n]) p.unshift(n);
      return p;
    }
    for (const nb of adj[c] || []) if (!v.has(nb)) { v.add(nb); par[nb] = c; q.push(nb); }
  }
  return [start];
}

export function countComponents(nodes, edges) {
  const u = {};
  for (const n of nodes) u[n.id] = [];
  for (const e of edges) {
    const s = typeof e.source === 'object' ? e.source.id : e.source;
    const t = typeof e.target === 'object' ? e.target.id : e.target;
    u[s]?.push(t); u[t]?.push(s);
  }
  const v = new Set(); let c = 0;
  for (const n of nodes) {
    if (v.has(n.id)) continue;
    c++; const q = [n.id];
    while (q.length) {
      const x = q.shift(); if (v.has(x)) continue; v.add(x);
      q.push(...(u[x] || []).filter((y) => !v.has(y)));
    }
  }
  return c;
}

export function computeStats(data) {
  const nodeSet = new Set(data.nodes.map((n) => n.id));
  const adj = {};
  for (const n of data.nodes) adj[n.id] = [];
  for (const e of data.edges) {
    const s = typeof e.source === 'object' ? e.source.id : e.source;
    const t = typeof e.target === 'object' ? e.target.id : e.target;
    if (adj[s]) adj[s].push(t);
    if (adj[t]) adj[t].push(s);
  }

  // BFS for connected components
  const visited = new Set();
  let components = 0;
  for (const n of data.nodes) {
    if (!visited.has(n.id)) {
      components++; const queue = [n.id];
      while (queue.length) {
        const curr = queue.shift(); if (visited.has(curr)) continue; visited.add(curr);
        for (const neighbor of adj[curr] || []) if (!visited.has(neighbor)) queue.push(neighbor);
      }
    }
  }

  // Reachability from core
  const coreNodes = data.nodes.filter((n) => n.paper === -1).map((n) => n.id);
  const reachableFromCore = new Set();
  const queue = [...coreNodes];
  const reverseAdj = {};
  for (const n of data.nodes) reverseAdj[n.id] = [];
  for (const e of data.edges) {
    const s = typeof e.source === 'object' ? e.source.id : e.source;
    const t = typeof e.target === 'object' ? e.target.id : e.target;
    if (reverseAdj[t]) reverseAdj[t].push(s);
  }
  while (queue.length) {
    const curr = queue.shift(); if (reachableFromCore.has(curr)) continue; reachableFromCore.add(curr);
    for (const dep of reverseAdj[curr] || []) if (!reachableFromCore.has(dep)) queue.push(dep);
  }
  // forward from core
  const fwdQueue = [...coreNodes];
  while (fwdQueue.length) {
    const curr = fwdQueue.shift(); if (reachableFromCore.has(curr)) continue; reachableFromCore.add(curr);
    for (const dep of adj[curr] || []) if (!reachableFromCore.has(dep)) fwdQueue.push(dep);
  }

  const orphans = data.nodes.filter((n) => !reachableFromCore.has(n.id));

  const theorems = data.nodes.filter((n) => n.kind === 'theorem').length;
  const definitions = data.nodes.filter((n) => n.kind === 'definition').length;
  const axioms = data.nodes.filter((n) => n.kind === 'axiom').length;

  return {
    totalNodes: data.nodes.length,
    totalEdges: data.edges.length,
    components,
    orphans: orphans.length,
    theorems,
    definitions,
    axioms,
    reachableFromCore: reachableFromCore.size,
  };
}

// --- Filter rules (modular) -------------------------------------------------
export function distancesFromRoots(data) {
  const adj = buildAdj(data.nodes, data.edges);
  const roots = data.nodes.filter((n) => n.paper === -1).map((n) => n.id);
  const dist = {};
  const q = [];
  for (const r of roots) { dist[r] = 0; q.push(r); }
  while (q.length) {
    const u = q.shift();
    for (const v of adj[u] || []) {
      if (dist[v] === undefined) { dist[v] = dist[u] + 1; q.push(v); }
    }
  }
  return dist;
}

export const FILTERS = {
  hideArtifacts: (data, _params) => ({
    nodes: data.nodes.filter((n) => !isArtifact(n.id)),
    edges: data.edges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return !isArtifact(s) && !isArtifact(t);
    }),
  }),
  restrictToPaper: (data, params) => {
    if (params == null || params.paper == null) return data;
    const keep = new Set(data.nodes.filter((n) => n.paper === params.paper).map((n) => n.id));
    const nodes = data.nodes.filter((n) => keep.has(n.id));
    const edges = data.edges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return keep.has(s) && keep.has(t);
    });
    return { nodes, edges };
  },
  reachableFromCore: (data, _params) => {
    const adj = buildAdj(data.nodes, data.edges);
    const core = data.nodes.filter((n) => n.paper === -1).map((n) => n.id);
    const reachable = new Set(core);
    const q = [...core];
    // reverse edges
    const rev = {};
    for (const n of data.nodes) rev[n.id] = [];
    for (const e of data.edges) {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      rev[t].push(s);
    }
    while (q.length) {
      const u = q.shift();
      for (const p of rev[u] || []) if (!reachable.has(p)) { reachable.add(p); q.push(p); }
    }
    const nodes = data.nodes.filter((n) => reachable.has(n.id));
    const nodeSet = new Set(nodes.map((n) => n.id));
    const edges = data.edges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nodeSet.has(s) && nodeSet.has(t);
    });
    return { nodes, edges };
  },
  depthLimit: (data, params) => {
    if (!params || params.depth == null) return data;
    const dist = distancesFromRoots(data);
    const nodes = data.nodes.filter((n) => dist[n.id] !== undefined && dist[n.id] <= params.depth);
    const nodeSet = new Set(nodes.map((n) => n.id));
    const edges = data.edges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nodeSet.has(s) && nodeSet.has(t);
    });
    return { nodes, edges };
  },
  // Filter to show only the main proof claims (theorems/definitions cited in paper)
  // Removes: artifacts, orphaned auxiliary lemmas not reachable from core
  claimsOnly: (data, _params) => {
    // First remove artifacts
    const nonArtifacts = data.nodes.filter((n) => !isArtifact(n.id));
    const nonArtifactSet = new Set(nonArtifacts.map((n) => n.id));
    const filteredEdges = data.edges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nonArtifactSet.has(s) && nonArtifactSet.has(t);
    });
    // Then keep only nodes reachable from core (core = paper -1)
    const adj = {};
    for (const n of nonArtifacts) adj[n.id] = [];
    for (const e of filteredEdges) {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      adj[s].push(t);
    }
    // Reverse adjacency for reachability from core
    const rev = {};
    for (const n of nonArtifacts) rev[n.id] = [];
    for (const e of filteredEdges) {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      rev[t].push(s);
    }
    const coreNodes = nonArtifacts.filter((n) => n.paper === -1).map((n) => n.id);
    const reachable = new Set(coreNodes);
    const queue = [...coreNodes];
    while (queue.length) {
      const u = queue.shift();
      for (const p of rev[u] || []) if (!reachable.has(p)) { reachable.add(p); queue.push(p); }
    }
    // Forward reachability too (in case of bidirectional dependencies)
    const fwdQueue = [...coreNodes];
    while (fwdQueue.length) {
      const u = fwdQueue.shift();
      for (const p of adj[u] || []) if (!reachable.has(p)) { reachable.add(p); fwdQueue.push(p); }
    }
    const nodes = nonArtifacts.filter((n) => reachable.has(n.id));
    const nodeSet = new Set(nodes.map((n) => n.id));
    const edges = filteredEdges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nodeSet.has(s) && nodeSet.has(t);
    });
    return { nodes, edges };
  },
  
  // Forcing chain: claims + forcing theorems + pure math foundations
  // Derives categories from node naming conventions (SSOT: names are the source)
  forcingChain: (data, _params) => {
    const visibleNodes = data.nodes.filter((n) => !isArtifact(n.id));
    const visibleNodeSet = new Set(visibleNodes.map((n) => n.id));
    const visibleEdges = data.edges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return visibleNodeSet.has(s) && visibleNodeSet.has(t);
    });

    // Collapsed first-principle buckets exported by the Lean graph pass.
    const isFoundation = (id) => id.startsWith('FOUNDATION.');

    // Forcing theorems - derived from naming convention (last segment starts with uppercase + digit).
    const isForcingTheorem = (id) => {
      const parts = id.split('.');
      const lastPart = parts[parts.length - 1];
      return /^[A-Z]+\d+[a-z']*$/.test(lastPart);
    };

    // Claim nodes are theorem/definition nodes explicitly marked by the build system.
    const isClaim = (n) => n.paper === -1 && (n.kind === 'theorem' || n.kind === 'definition');

    const claimIds = new Set();
    const targetIds = new Set();
    for (const n of visibleNodes) {
      if (isClaim(n)) claimIds.add(n.id);
      if (isFoundation(n.id) || isForcingTheorem(n.id)) targetIds.add(n.id);
    }

    if (claimIds.size === 0) {
      return { nodes: [], edges: [] };
    }
    if (targetIds.size === 0) {
      return FILTERS.claimsOnly({ nodes: visibleNodes, edges: visibleEdges }, _params);
    }

    const adj = buildAdj(visibleNodes, visibleEdges);
    const rev = {};
    for (const n of visibleNodes) rev[n.id] = [];
    for (const e of visibleEdges) {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      if (rev[t]) rev[t].push(s);
    }

    const reachableFromClaims = new Set(claimIds);
    const forwardQueue = [...claimIds];
    while (forwardQueue.length) {
      const u = forwardQueue.shift();
      for (const v of adj[u] || []) {
        if (!reachableFromClaims.has(v)) {
          reachableFromClaims.add(v);
          forwardQueue.push(v);
        }
      }
    }

    const connectedTargetIds = new Set();
    for (const id of targetIds) {
      if (reachableFromClaims.has(id)) connectedTargetIds.add(id);
    }

    if (connectedTargetIds.size === 0) {
      return FILTERS.claimsOnly({ nodes: visibleNodes, edges: visibleEdges }, _params);
    }

    const canReachTargets = new Set(connectedTargetIds);
    const reverseQueue = [...connectedTargetIds];
    while (reverseQueue.length) {
      const u = reverseQueue.shift();
      for (const v of rev[u] || []) {
        if (!canReachTargets.has(v)) {
          canReachTargets.add(v);
          reverseQueue.push(v);
        }
      }
    }

    const keep = new Set();
    for (const id of reachableFromClaims) {
      if (canReachTargets.has(id)) keep.add(id);
    }
    for (const id of claimIds) keep.add(id);
    for (const id of connectedTargetIds) keep.add(id);

    const nodes = visibleNodes.filter((n) => keep.has(n.id));
    const nodeSet = new Set(nodes.map((n) => n.id));
    const edges = visibleEdges.filter((e) => {
      const s = typeof e.source === 'object' ? e.source.id : e.source;
      const t = typeof e.target === 'object' ? e.target.id : e.target;
      return nodeSet.has(s) && nodeSet.has(t);
    });

    return { nodes, edges };
  },
};

// TRUE_PATH_FILTERS will be lazily loaded from true_path.js to avoid circular deps
let _truePathFilters = null;
function getTruePathFilters() {
  if (!_truePathFilters) {
    // Dynamic import pattern - in browser ES modules, this avoids circular issues
    // since true_path.js is now self-contained (no imports from graph_utils.js)
    _truePathFilters = TRUE_PATH_FILTERS;
  }
  return _truePathFilters;
}

export function applyFilters(data, activeFilters) {
  let out = data;
  for (const f of activeFilters) {
    // Check FILTERS first, then TRUE_PATH_FILTERS
    let fn = FILTERS[f.name];
    if (!fn) {
      fn = getTruePathFilters()[f.name];
    }
    if (!fn) continue;
    out = fn(out, f.params || {});
  }
  return out;
}

export function findAllPaths(data, startId, endId, maxPaths = 20, maxLength = 15) {
  if (!startId || !endId || startId === endId) return [[startId]];
  
  const adj = buildAdj(data.nodes, data.edges);
  const paths = [];
  const visited = new Set();
  
  function dfs(current, target, path) {
    if (paths.length >= maxPaths) return;
    if (path.length > maxLength) return;
    if (current === target) {
      paths.push([...path, target]);
      return;
    }
    
    const neighbors = adj[current] || [];
    for (const next of neighbors) {
      if (path.includes(next)) continue;
      dfs(next, target, [...path, current]);
    }
  }
  
  dfs(startId, endId, []);
  return paths.sort((a, b) => a.length - b.length);
}

export function findShortestPath(data, startId, endId) {
  if (!startId || !endId) return null;
  if (startId === endId) return [startId];
  
  const adj = buildAdj(data.nodes, data.edges);
  const visited = new Set([startId]);
  const parent = { [startId]: null };
  const queue = [startId];
  
  while (queue.length > 0) {
    const current = queue.shift();
    
    if (current === endId) {
      const path = [];
      for (let n = endId; n !== null; n = parent[n]) {
        path.unshift(n);
      }
      return path;
    }
    
    for (const neighbor of adj[current] || []) {
      if (!visited.has(neighbor)) {
        visited.add(neighbor);
        parent[neighbor] = current;
        queue.push(neighbor);
      }
    }
  }
  
  return null;
}
