# Simultaneous strictification verification

2026-09-10. All six steps in `python3 scripts/check.py` passed with exit code 0 and zero warnings.
Input hashes were compared with the live files before saving these artifacts.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or CI run.

- Mathematical source modules, including aggregation entrypoints: 84.
- Audited declarations, including private declarations: 2,545.
- Private-name declarations: 480. Public-name declarations: 2,065, all exported.
- Exported audited names: 2,081. Sixteen generated private-name equation lemmas and splitters
  are also exported; private and exported flags are not mutually exclusive.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 41 proved, 3 partial, 6 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `d86762cb017ab8a27f8e33c6f717027eb2f8930df5d71b17508576b04d3706f8`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axioms.

This checkpoint completes Lemmas 4.7 and 4.9. Representatives of bases of the actual graded
kernels generate each defect modulo the next intrinsic lower central term. The degree-two
defect uses the first strictness equality to identify its full numerator. Simultaneous
commutator and triple-commutator quotients give the exact additional-generator bounds
`2m` and `3 * binom(m,2)`, respectively. Total rank bounds and finite generation are also supplied.
Ambient groups need not be finite or nontrivial; empty defect families and zero bounds are covered.
The basis producer and both strictification constructions received independent source review.

Build, imports, environment lint, text lint, axiom audit, and paper-map checks took
3.454, 0.555, 2.276, 5.355, 177.065, and 0.224 seconds, respectively.

The 15n-squared envelope, main theorem, unconditional model-companion existence, and remaining
paper items are unfinished. The full goal stays active. See
[the checkpoint](../../../strictification-checkpoint.md).
Previous artifacts remain preserved under `../commutator-roots-support/`.
