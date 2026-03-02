/-
  DependencyGraph.lean — Build-time dependency graph extraction

  Extracts every declaration in the environment and its transitive
  dependencies, outputs JSON for visualization and integrity analysis.

  Usage: Inlined into GraphExport.lean by build_papers.py.
  Do not import this file directly — it is never compiled by lake.
-/

import Lean
import Lean.Util.FoldConsts

open Lean System

/-- Collect all constant names referenced in a ConstantInfo's type and value. -/
def collectDeps (info : ConstantInfo) : Array Name :=
  let deps := info.type.foldConsts #[] fun n acc => acc.push n
  match info with
  | ConstantInfo.defnInfo v  => v.value.foldConsts deps fun n acc => acc.push n
  | ConstantInfo.thmInfo v   => v.value.foldConsts deps fun n acc => acc.push n
  | ConstantInfo.opaqueInfo v => v.value.foldConsts deps fun n acc => acc.push n
  | _ => deps

/-- Filter: keep only names from our project namespaces. -/
def isProjectName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "Leverage" ||
  s.startsWith "Ssot" ||
  s.startsWith "DecisionQuotient" ||
  s.startsWith "AbstractClassSystem"

/-- JSON escape for strings -/
def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

/-! ### JSON export for visualization pipeline -/

elab "#export_graph_json" path:str : command => do
  let env ← getEnv
  let filePath := path.getString

  let mut nodes : Array String := #[]
  let mut edges : Array String := #[]

  let entries := (Lean.Environment.constants env).fold
    (init := #[]) fun acc name info => acc.push (name, info)

  for (name, info) in entries do
    if isProjectName name then
      let kind := match info with
        | ConstantInfo.thmInfo _    => "theorem"
        | ConstantInfo.defnInfo _   => "definition"
        | ConstantInfo.axiomInfo _  => "axiom"
        | ConstantInfo.opaqueInfo _ => "opaque"
        | _                         => "other"
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
