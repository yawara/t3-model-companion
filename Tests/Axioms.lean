/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

import T3
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
public meta import Lean.Data.Json

/-!
# Axiom audit for every project declaration

Run `lake env lean Tests/Axioms.lean` from the repository root after `lake build`.
The audit checks every declaration originating in a `T3` module, including private declarations
and declarations in standard namespaces. A separate environment loads private module data so that
unused private declarations are checked as well. It also checks that `T3` imports every source file.
A separate public environment records which declarations are exported through `T3`.

Set `T3_DECLARATIONS_JSON` to a file path to export the checked declaration inventory as JSON.
This file is a test program and must not be imported by the mathematical library.
-/

open Lean Elab Command

public meta section

namespace T3Tests

/-- Discover the project modules from their source files, including the root module. -/
def sourceModules : IO (Array Name) := do
  unless ← ("T3.lean" : System.FilePath).pathExists do
    throw <| IO.userError "Run the axiom audit from the repository root containing T3.lean."
  let paths ← ("T3" : System.FilePath).walkDir
  let mut modules := #[`T3]
  for path in paths do
    if path.extension == some "lean" && !(← path.isDir) then
      modules := modules.push <|
        (path.withExtension "").components.foldl Name.str .anonymous
  return modules.qsort Name.lt

/-- Check the complete imported project and optionally export its declaration inventory. -/
def auditAxioms : CommandElabM Unit := do
  let modules ← sourceModules
  let imported := (← getEnv).header.moduleNames
  for moduleName in modules do
    unless imported.contains moduleName do
      throwError "Project source module `{moduleName}` is not imported by T3."
  -- Normal module imports may omit private declarations. Load their complete data explicitly.
  -- With extensions left unloaded, collectAxioms traverses the kernel declaration bodies.
  let env ← Lean.importModules #[{ module := `T3 }] {} (level := .private)
  let publicEnv ← Lean.importModules #[{ module := `T3, isExported := true }] {}
    (level := .exported)
  let publicEnv := publicEnv.setExporting true
  let declarations := env.constants.map₁.fold (init := #[]) fun names name _ => Id.run do
    let some index := env.getModuleIdxFor? name | return names
    let moduleName := env.header.moduleNames[index]!
    if moduleName.getRoot == `T3 then
      return names.push (name, moduleName)
    return names
  let declarations := declarations.qsort fun left right => left.1.lt right.1
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut inventory := #[]
  for (name, moduleName) in declarations do
    let axioms ← withEnv env <| Lean.collectAxioms name
    let disallowed := axioms.filter fun axiomName => !allowed.contains axiomName
    unless disallowed.isEmpty do
      throwError "`{name}` from `{moduleName}` uses disallowed axioms: {disallowed}"
    inventory := inventory.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("private", toJson (isPrivateName name)),
      ("exported", toJson (publicEnv.contains name)),
      ("axioms", toJson (axioms.map Name.toString))]
  if let some path ← IO.getEnv "T3_DECLARATIONS_JSON" then
    let report := Json.mkObj [
      ("modules", toJson (modules.map Name.toString)),
      ("declarations", Json.arr inventory)]
    IO.FS.writeFile path (report.pretty ++ "\n")
  logInfo m!"Axiom audit passed: {declarations.size} declarations in {modules.size} source modules."

run_cmd auditAxioms

end T3Tests
