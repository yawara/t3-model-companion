/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public meta import Lean.Linter.Init
public meta import Mathlib.Tactic.Linter.TextBased

/-!
# Text and module-name lint for all mathematical source files

Run `lake env lean Tests/TextLint.lean` from the repository root.
This program discovers `T3.lean` and every Lean source file below `T3`, and includes the separate
Challenge and Solution entrypoints. It applies the pinned Mathlib text and module-name linters
with no exceptions. It does not modify any source files.
This file is a test program and must not be imported by the mathematical library.
-/

open Lean Lean.Linter Mathlib.Linter.TextBased

public meta section

namespace T3Tests

/-- Lint every mathematical source module, including files missing from the umbrella. -/
def lintSources : IO Unit := do
  unless ← ("T3.lean" : System.FilePath).pathExists do
    throw <| IO.userError "Run the text lint from the repository root containing T3.lean."
  let paths ← ("T3" : System.FilePath).walkDir
  let mut modules := #[`T3, `Challenge, `Solution]
  for path in paths do
    if path.extension == some "lean" && !(← path.isDir) then
      modules := modules.push <|
        (path.withExtension "").components.foldl Name.str .anonymous
  modules := modules.qsort Name.lt
  -- Each text and module-name linter is enabled by default in the pinned Mathlib source.
  -- No linter sets are needed here, and the exception list is deliberately empty.
  let options : LinterOptions := { toOptions := {}, linterSets := {} }
  let textErrors ← lintModules options #[] modules .humanReadable false
  let nameErrors := (← modulesNotUpperCamelCase options modules) +
    (← modulesOSForbidden options modules)
  unless textErrors == 0 && nameErrors == 0 do
    throw <| IO.userError
      s!"Text lint failed: {textErrors} files with text errors; {nameErrors} module-name errors."
  IO.println s!"Text lint passed: {modules.size} source modules; no exceptions."

run_cmd liftM lintSources

end T3Tests
