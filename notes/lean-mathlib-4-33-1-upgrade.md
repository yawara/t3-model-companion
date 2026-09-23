# Lean and mathlib v4.33.1 upgrade

> Historical T3 revision identifiers have been omitted for publication. Recorded commands, outcomes, and source hashes describe the original checks; this edited record does not certify the rewritten historical snapshots.

> 履歴資料（v4 原稿）。原稿は [archives/T3_modelcompanion_v4.tex](../archives/T3_modelcompanion_v4.tex) に保存。以下の番号・行・検証結果は当時のもの。
> 現行 v8 の対応は [対応表](../docs/paper-map.md) と [v8 移行記録](v8-migration.md) を参照。

2026-09-10. The selected target is the newest stable Lean/mathlib release
meeting Palomar's current version-support conditions. The starting revision
is `[historical revision omitted]`, using Lean/mathlib v4.32.2. The manuscript remains unchanged.

## Pinned versions and Palomar compatibility

- Project Lean: `leanprover/lean4:v4.33.1`.
- mathlib: `0df444a360eaa60ab8c11dca51a86af692955474` (v4.33.1).
- lean4export source: `15f6055e299ad5b89345e533cc2192f4cc00f659` (v4.33.0),
  rebuilt with the project's exact Lean v4.33.1 toolchain.
- Comparator, NanoDa, and Landrun retain their preceding exact pins.

PalomarSubmission `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` records minimum
Lean v4.28.0 and permits same-major/minor patch-zero sources for exporter and
Verso when an exact stable-patch tool tag is unavailable. It rebuilds those
sources with the submitted project's exact Lean version. The local comparison
script follows that rule and rejects unrelated release-line or RC fallbacks.
The version selection and official sources are explained in
[the Palomar documentation](../docs/palomar.md#lean-version-support).

## Migration scope

The new mathlib lint prefers tactic `have` and `let` over `haveI` and `letI`
inside proposition proofs. Only reported warning sites are adapted; term-mode
binders in mathematical definitions and the statement specification are retained.
No linter is suppressed.

Proof elaboration changes are repaired with explicit reductions and typed
commuting witnesses. The coproduct inverse on generators is proved by `rfl`;
the collection argument gives `noncommPiCoprod` an explicitly typed `Pairwise`
commutation witness; and a private `rfl` helper makes the action of the exterior
index order embedding available to `simp`. Mathematical statements, hypotheses,
constants, and principal constructions are preserved.

An independent review covered all 59 changed mathematical files: 46 contain only
the local-instance syntax update, and 13 contain explicit proof reductions or
typed witnesses. The only new handwritten declaration is the private
`appendOrderEmbedding_apply` helper. Copyright, authorship, `Paper-ID`, and TeX
source annotations are unchanged. A separate review of the dependency pins,
exporter script, and current documentation found no actionable issues.

## Verification

The mathematical source revision is
`39c01de9e5e5b1789f938f3f73d67164f2507fa9739dba1efc9a331e05eaf522`.
It is the SHA256 of the sorted JSON path-to-SHA256 dictionary for `T3.lean`
and `T3/**/*.lean`. The paper map points to this input and record. The complete
[verification artifacts](audit-artifacts/2026-09-10/lean-mathlib-4-33-1/README.md)
record the final inputs and results.

`python3 scripts/check.py` passed all seven stages with zero warnings and
unchanged inputs: metadata, build, import aggregation, environment lint, text
lint, axiom audit, and paper-map validation. Text lint covers 111 source modules
without exceptions; the axiom audit covers 2,969 declarations in 110 modules,
using only `propext`, `Classical.choice`, and `Quot.sound`. All 50 paper items
and their 75 parts retain their completed proof and fidelity status.

The elaborated inventory changes from 2,972 to 2,969 declarations (2,393 to
2,391 non-private names). Its additions and removals consist of the new private
helper and compiler-generated equation, proof, and simplifier declarations.
The comparison also records one generated congruence lemma's module change and
nine axiom-dependency changes, all within the same three-axiom allowlist.
This inventory is not a type-equivalence check; the source review separately
checks preservation of the existing mathematical statements.

`scripts/verify-comparator.sh` passed end to end with the final mathematical
sources, checking both selected statements and their definition closures.
NanoDa and Lean's kernel accepted the solution. The independent Challenge
emits exactly its two expected theorem-hole warnings; these are outside the
zero-warning mathematical library gate. All 12 exporter toolchain-compatibility
guard cases passed.

An isolated minimal Challenge already confirms that Verso v4.33.0 source
`3bdedf29bada13d8103e6c979001c51dcee210c8` can build its `Challenge:literate`
target and produce HTML using Lean v4.33.1. The extraction and render commands
both exited 0 with zero warnings. Its common dependency with mathlib, `plausible`,
has the same exact revision. This checks renderer-version compatibility; it is
not a rendering of this project's actual Challenge or a Palomar submission.

Earlier audit artifacts remain frozen. Source fidelity remains distinct from
kernel acceptance and from human peer review. Publication, remote CI execution,
and submission are outside this local upgrade. The build uses the pinned
mathlib cache; no clean rebuild of every dependency is claimed.
