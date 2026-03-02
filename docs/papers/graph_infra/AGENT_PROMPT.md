# Agent Brief: Auditable Rejection Trace for Lean Proof Graph

## Mission

Build an auditable proof dependency visualizer for the OpenHCS paper series.
The key property: rejecting any theorem in Paper 4 must demonstrably force
rejection of counting (Nat). The graph must be derived from Lean's type
checker, not grep. Every edge must be a compile-time-justified inference.

---

## Repo

`/home/ts/code/projects/openhcs-sequential`

---

## Critical Diagnosis (do not re-derive, trust this)

The current graph in `docs/papers/graph_infra/graphs/paper4_toc.json` is
**broken for rejection tracing**. Here's why:

The Python source parser in `build_papers.py:_extract_graph_from_source`
produces two disconnected layers:

- **Nodes**: declaration-level — `DecisionQuotient.AlgorithmComplexity.Counted`
- **Edges**: module-level — `DecisionQuotient.AlgorithmComplexity → DecisionQuotient.Sufficiency`

They never connect. Result: all 2679 nodes are roots (zero outgoing edges),
BFS from any theorem finds nothing. The rejection-trace.jsx is sound — the
data it receives is not.

There are two valid graph types, pick one consistently:

| Type | Nodes | Edges | Auditable? |
|---|---|---|---|
| **Module graph** | `.lean` files | `import` statements | Source-level only |
| **Proof-term graph** | declarations | `foldConsts` references | Lean type-checker |

For the mission (rejection tracing to Nat), we need the **proof-term graph**.
Only Lean knows which proof terms reference which definitions.

---

## Existing Infrastructure

### `docs/papers/graph_infra/DependencyGraph.lean`

Contains two Lean 4 command elaborators:

**`#extract_dependency_graph`** — runs at elaboration time, logs stats,
validates that all project declarations are reachable from core axioms (Nat).

**`#export_graph_json "path"`** — dumps proof-term-level graph:
```
{ "nodes": [{"id": "DecisionQuotient.Foo.bar", "kind": "theorem"}],
  "edges": [{"source": "DecisionQuotient.Foo.bar", "target": "DecisionQuotient.Basic.baz"}] }
```
Edge `source→target` = "source's proof term contains a reference to target".
This is derived via `foldConsts` on the compiled `ConstantInfo` — Lean's
actual proof term, not source text. **This is the auditable graph.**

The filter `isProjectName` currently matches:
`Leverage | Ssot | DecisionQuotient | AbstractClassSystem`

Core axioms (graph sinks) are:
`Nat, Nat.zero, Nat.succ, Nat.rec, Nat.add, Eq, Eq.refl, Prop, True, False,
And, Or, Not, Iff, Exists, HAdd.hAdd, HMul.hMul, HDiv.hDiv, LE.le, LT.lt,
GE.ge, GT.gt, Bool, Bool.true, Bool.false`

### `docs/papers/graph_infra/rejection-trace.jsx`

React/D3 component. Already implements:
- `buildAdj(nodes, edges)` — adjacency list (outgoing)
- `findRoots(nodes, adj)` — nodes with no outgoing edges (the axioms)
- `bfs(start, adj, targets)` — shortest path from selected node to any root
- `Chain` panel — shows the rejection path hop-by-hop
- Node dimming: selected node + path highlighted, rest faded

**It is correct given proper data.** Edge direction must be:
`source → target` = "source depends on target" = "rejecting target undermines source"

BFS follows outgoing edges from a selected theorem toward axiom roots.
The chain panel shows "reject THIS → must reject THAT (N hops)."

### `docs/papers/graph_infra/dependency-graph.jsx`

Force-directed D3 graph. Separate viewer, also loads JSON via textarea.
Colors nodes by paper group. Node shapes: circle=theorem, square=definition,
diamond=axiom.

### `scripts/build_papers.py`

Unified build system. All config from `scripts/papers.yaml`.

Key methods relevant here:
- `build_lean(paper_id)` — runs `lake build` in `paper_dir/meta.proofs_dir/`
- `_collect_graph_json(paper_id)` — currently calls broken source parser,
  writes to `graph_infra/graphs/<paper_id>.json`
- `_extract_graph_from_source(paper_id)` — the broken source parser (nodes
  and edges at different granularity)
- `_iter_lean_roots_for_paper(paper_id)` — returns `(paper_id, proofs_dir)`
  for paper + transitive lean_dependencies
- `_iter_paper_lean_files(proofs_dir)` — .lean files excluding .lake/build/dep_*
- `_get_paper_proofs_dir(paper_id)` — `papers_dir / meta.dir_name / meta.proofs_dir`

### Paper 4 Lean structure

Lakefile: `docs/papers/paper4_decision_quotient/proofs/lakefile.lean`
```lean
package «decision_quotient»
require mathlib from git "..." @ "a8227f..."
@[default_target]
lean_lib «DecisionQuotient» where
  globs := #[.submodules `DecisionQuotient]
  srcDir := "."
```

Root aggregator: `DecisionQuotient.lean` — imports all ~50 submodules.
NOT compiled by lake (globs only covers `DecisionQuotient/` subdir).
`lake build` builds 3234 jobs successfully.

**The problem getting `#export_graph_json` to run:**
`GraphExport.lean` needs `import DecisionQuotient` → needs `DecisionQuotient.olean`
→ but lake never compiles `DecisionQuotient.lean` itself (only its submodules).
Compiling it separately causes double-import conflicts because submodules are
already in the environment.

We have NOT found the right invocation strategy yet. This is the open problem.

---

## The Open Problem

How do we invoke `#export_graph_json` for each paper in a way that:

1. Has access to the full compiled proof environment (all theorems in scope)
2. Does NOT require modifying the paper's own lakefile
3. Does NOT cause double-import conflicts
4. Is automatic — `build_papers.py` drives it for all papers from papers.yaml
5. Is auditable — edges come from `foldConsts` on compiled proof terms

Approaches to evaluate:
- **Separate lake project** that `require`s the paper as a path dependency,
  then has its own `GraphExport.lean` that imports the paper module + DependencyGraph
- **`lean --stdin`** with a heredoc that imports the package after `lake build`
  pre-populated the .olean cache
- **Inline into the paper's build as a separate lake exe** that is self-contained
- **Accept module-level graph** and fix the Python parser to produce a consistent
  graph (nodes=modules, edges=imports) — loses proof-term auditability but works

---

## What We Need

**Evaluate the approaches above.** For each:
- Does it work given the lakefile structure?
- Can build_papers.py drive it automatically?
- What does `_collect_graph_json` look like?

**If proof-term graph is feasible:** specify the exact invocation,
the JSON schema (must include `"core_axiom": true` flag on sink nodes),
and what changes to `_collect_graph_json`.

**If proof-term graph is not feasible without major restructuring:**
specify what the module-level graph needs to look like so `rejection-trace.jsx`
works correctly — i.e., nodes=modules, edges=imports, sinks=Mathlib/Nat modules,
and the rejection chain reads "reject this module → reject these downstream modules."

**Either way:** the graph must support:
1. Directed edges with clear rejection semantics
2. Identification of core axiom sinks (Nat, counting)
3. BFS rejection path from any node to the counting axioms
4. A `rejection_cost` field per node = number of nodes in its reverse-reachability
   set (how much of the proof collapses if this node is rejected)

**Do not produce code yet.** Produce a structured decision + specification.
Read the files, run experiments if needed, then give the answer.
