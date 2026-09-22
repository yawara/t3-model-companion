# Palomar readiness evidence, Lean v4.34.0

This directory records local checks for the
[2026-09-22 preparation checkpoint](../../../palomar-readiness-2026-09-22.md).
It does not record a Palomar submission, remote CI run, editorial review, or
registration. The repository remains private.

## Files

- `upstream-versions.json`: live-resolved Lean, mathlib, Palomar policy, exporter,
  renderer, and checker revisions, together with the starting repository commit.
- `source-tree.json`: local source-tree, Challenge size, and dependency checks.
- `dependency-update.log`: dependency update and mathlib cache retrieval. Two
  cache misses were handled by the subsequent successful build.
- `build-migration.log`: successful project build after the API migration.
- `checks.json` and the corresponding gate logs: all seven project checks
  passed with zero warnings and unchanged input hashes.
- `declarations.json` and `declaration-inventory-diff.json`: 3,120 declarations
  in 117 source modules, their permitted axiom dependencies, and the compiler
  inventory differences from the preceding v4.33.1 snapshot.
- `comparator-verification.json` and `comparator.log`: successful comparison of
  both selected statements and proof replay by NanoDa and Lean's default kernel.
- `verso-verification.json`: actual Challenge extraction/rendering evidence,
  tool/dependency revisions, input/output hashes, and upstream anchor checks.
- `verso-*.log` and `verso-smoke-*.txt`: isolated renderer logs and minimal smoke
  input files. The actual Challenge input is the unchanged root `Challenge.lean`.

Compiled `.olean`/`.ilean` files, executables, and renderer build caches are not
part of this evidence directory. Their hashes in the renderer report identify
local outputs, not files to include in a submitted repository.

The two Challenge holes are deliberate and occur only in the independent
specification. The mathematical library gate requires zero warnings and only
`propext`, `Classical.choice`, and `Quot.sound`. Verso dependency setup has the
upstream SubVerso missing-manifest warning; the extraction and rendering
commands themselves have no warnings. The renderer check does not reproduce
Palomar's complete sandbox and asset-sanitization workflow.

Older verification directories are unchanged. Their source hashes and
toolchains continue to describe their own historical snapshots.
