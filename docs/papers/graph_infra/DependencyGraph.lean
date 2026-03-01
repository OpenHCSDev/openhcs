/-
  DependencyGraph.lean — Build-time dependency graph extraction

  Extracts every declaration in the environment and its transitive
  dependencies, outputs JSON for visualization and integrity analysis.

  Usage: Add to lakefile as a build target, or run with `lean --run`.

  Produces:
    1. Full dependency graph (nodes + edges)
    2. Connected component analysis (should be exactly 1)
    3. "Counting rejection" analysis: definitions reachable from Nat/core axioms
       (should be ALL of them — 0 orphans)
-/

import Lean
import Lean.Util.FoldConsts

open Lean System

/-- Collect all constant names referenced in a ConstantInfo's type and value. -/
def collectDeps (info : ConstantInfo) : Array Name :=
  let deps := info.type.foldConsts #[] fun acc n => acc.push n
  match info with
  | .defnInfo v  => v.value.foldConsts deps fun acc n => acc.push n
  | .thmInfo v   => v.value.foldConsts deps fun acc n => acc.push n
  | .opaqueInfo v => v.value.foldConsts deps fun acc n => acc.push n
  | _ => deps

/-- Core axioms and foundational names that "counting" depends on. -/
def coreAxioms : Array Name := #[
  `Nat, `Nat.zero, `Nat.succ, `Nat.rec, `Nat.add,
  `Eq, `Eq.refl,
  `Prop, `True, `False,
  `And, `Or, `Not, `Iff,
  `Exists,
  `HAdd.hAdd, `HMul.hMul, `HDiv.hDiv,
  `LE.le, `LT.lt, `GE.ge, `GT.gt,
  `Bool, `Bool.true, `Bool.false
]

/-- Filter: keep only names from our project namespaces. -/
def isProjectName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Leverage" ||
  s.startsWith "Ssot" ||
  s.startsWith "DecisionQuotient" ||
  s.startsWith "AbstractClassSystem"

/-- BFS reachability from a set of root names through the dependency graph. -/
def reachableFrom (graph : HashMap Name (Array Name)) (roots : Array Name) : HashSet Name := Id.run do
  let mut visited : HashSet Name := {}
  let mut queue := roots.toList
  while !queue.isEmpty do
    match queue with
    | [] => break
    | n :: rest =>
      queue := rest
      if visited.contains n then continue
      visited := visited.insert n
      if let some deps := graph.find? n then
        queue := queue ++ deps.toList
  visited

/-- JSON escape for strings -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

/-- Main extraction: run as `lean --run DependencyGraph.lean` -/
def main : IO Unit := do
  -- Note: In practice, this would import your project and access the env.
  -- This is the template — integrate into your lakefile build step.
  IO.println "{"
  IO.println "  \"description\": \"Dependency graph extraction template\","
  IO.println "  \"usage\": \"Import your project modules above, then this script extracts the full graph.\","
  IO.println "  \"integration\": {"
  IO.println "    \"step1\": \"Add 'import Leverage.BridgeToDQ' (and all other root modules) at top of this file\","
  IO.println "    \"step2\": \"Run: lean --run DependencyGraph.lean > graph.json\","
  IO.println "    \"step3\": \"Feed graph.json into the visualization\""
  IO.println "  }"
  IO.println "}"

/-! ### The actual extraction command — paste into a file that imports your project -/

/-- Drop this into a file that imports your full project.
    It will dump the complete dependency graph as JSON to stdout.

    ```
    import Leverage.BridgeToDQ
    import «your other modules»
    -- paste extractGraph here
    #eval extractGraph
    ```
-/
elab "#extract_dependency_graph" : command => do
  let env ← Lean.Elab.Command.getEnv

  -- Build adjacency list for project declarations
  let mut graph : HashMap Name (Array Name) := {}
  let mut allProjectNames : Array Name := #[]
  let mut theoremCount := 0
  let mut defCount := 0

  for (name, info) in env.constants.map₁.toList do
    if isProjectName name then
      allProjectNames := allProjectNames.push name
      let deps := collectDeps info
      -- Filter deps to project names or core
      let projectDeps := deps.filter fun d =>
        isProjectName d || coreAxioms.contains d
      graph := graph.insert name projectDeps
      match info with
      | .thmInfo _  => theoremCount := theoremCount + 1
      | .defnInfo _ => defCount := defCount + 1
      | _ => pure ()

  -- Reachability analysis from core axioms
  let reachable := reachableFrom graph coreAxioms
  let orphans := allProjectNames.filter fun n => !reachable.contains n

  -- Also check: reachability from ANY single project node (connected component)
  let componentFromFirst :=
    if allProjectNames.size > 0 then
      reachableFrom graph #[allProjectNames[0]!]
    else
      HashSet.empty
  let disconnected := allProjectNames.filter fun n =>
    !componentFromFirst.contains n

  -- Output stats
  Lean.logInfo m!"Dependency Graph Extracted:"
  Lean.logInfo m!"  Total project declarations: {allProjectNames.size}"
  Lean.logInfo m!"  Theorems: {theoremCount}"
  Lean.logInfo m!"  Definitions: {defCount}"
  Lean.logInfo m!"  Connected components: {if disconnected.size == 0 then 1 else 2}+"
  Lean.logInfo m!"  Orphans (not reachable from counting): {orphans.size}"
  Lean.logInfo m!"  Disconnected from main graph: {disconnected.size}"

  if orphans.size == 0 then
    Lean.logInfo m!"  ✓ INTEGRITY: 0 definitions can collapse without rejecting counting"
  else
    Lean.logWarning m!"  ✗ {orphans.size} definitions not reachable from core axioms:"
    for o in orphans do
      Lean.logWarning m!"    - {o}"

/-! ### JSON export version for visualization pipeline -/

elab "#export_graph_json" path:str : command => do
  let env ← Lean.Elab.Command.getEnv
  let filePath := path.getString

  let mut nodes : Array String := #[]
  let mut edges : Array String := #[]

  for (name, info) in env.constants.map₁.toList do
    if isProjectName name then
      let kind := match info with
        | .thmInfo _    => "theorem"
        | .defnInfo _   => "definition"
        | .axiomInfo _  => "axiom"
        | .opaqueInfo _ => "opaque"
        | _             => "other"
      nodes := nodes.push
        s!"\{\"id\":\"{jsonEscape name.toString}\",\"kind\":\"{kind}\"}"

      let deps := collectDeps info
      for d in deps do
        if isProjectName d then
          edges := edges.push
            s!"\{\"source\":\"{jsonEscape name.toString}\",\"target\":\"{jsonEscape d.toString}\"}"

  let json := s!"\{\"nodes\":[{",".intercalate nodes.toList}],\"edges\":[{",".intercalate edges.toList}]}"

  IO.FS.writeFile ⟨filePath⟩ json
  Lean.logInfo m!"Graph exported to {filePath}: {nodes.size} nodes, {edges.size} edges"
