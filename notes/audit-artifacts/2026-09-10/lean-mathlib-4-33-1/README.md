# Lean/mathlib v4.33.1 verification

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

Final local upgrade verification on 2026-09-10, starting from `[historical revision omitted]`.
The [upgrade record](../../../lean-mathlib-4-33-1-upgrade.md) explains the migration
and the official Palomar version-support rule. No publication, registration,
submission, or remote CI run is represented by these artifacts.

## Final project gates

`checks.json` records all seven passing stages of `python3 scripts/check.py`,
each with exit code 0 and zero warnings. Its input hashes match the final
sources, and the runner confirmed that inputs did not change during verification.
The corresponding seven logs are stored here.

- Mathematical source revision:
  `39c01de9e5e5b1789f938f3f73d67164f2507fa9739dba1efc9a331e05eaf522`.
- Manuscript SHA256:
  `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Text lint: 111 source modules, no exceptions.
- Axiom audit: 2,969 declarations in 110 source modules; only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Paper map: 50 items / 75 parts; actual bindings match the kernel inventory.

`declarations.json` is the final kernel inventory. `declaration-comparison.json`
compares it with the frozen preparation inventory: four added names, seven
removed names, and ten changed common entries. The name additions/removals are
the new private `appendOrderEmbedding_apply` helper and generated equation,
proof, or simplifier declarations. One common generated congruence lemma changes
module ownership; nine common declarations change axiom dependencies within
the existing allowlist. Handwritten public statements are reviewed separately,
because this inventory does not serialize declaration types.

`source-fidelity-review.json` records the final independent review of all 59
changed mathematical files, their hashes, and no findings. It retains the
earlier 40-file review as `source-fidelity-initial-review.json`; only the final
review describes the final mathematical snapshot. The sole handwritten addition
is a private definitional-equality helper. The review preserves the manuscript
statements, hypotheses, constants, principal constructions, and source attribution.

## Palomar tool compatibility

`comparator-verification.json` and `comparator.log` record the successful full
script invocation. Both selected statements and their definition closures pass
Comparator; NanoDa and Lean's kernel accept the solution. The independent
Challenge has exactly two intended theorem holes, so its two warnings are
expected in this separate check. The project mathematical gate above remains
warning-free.

`dependency-comparison.json` records all nine manifest revision updates with
unchanged package names and URLs. `upgrade-exporter-tool.json` and its log
record the pinned v4.33.0 exporter source built with the project's exact v4.33.1
toolchain. `upgrade-exporter-compatibility.json` records 12 passing compatibility
guard cases. The build uses the pinned mathlib cache, not a clean source rebuild
of every dependency.

`verso-compatibility.json` records an isolated minimal Challenge extraction and
raw HTML rendering with v4.33.0 Verso source under Lean v4.33.1. Both commands
pass with zero warnings; dependency setup separately emits the upstream
subverso missing-manifest warning. This is a renderer-version smoke check,
not rendering of the project's actual Challenge or a Palomar sandbox run.
Its input files are retained as `verso-smoke-*.txt`, and its logs as
`verso-setup.log`, `verso-literate.log`, and `verso-html.log`. The JSON's
`archived_files` maps the original smoke-workspace paths to these saved files.

Earlier verification records remain frozen. These local checks do not replace
the registry's eventual policy checks and human review.
