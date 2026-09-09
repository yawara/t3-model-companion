# Positive graded Lie verification

2026-09-10. All six steps of `python3 scripts/check.py` passed with exit code 0 and zero warnings.
Input hashes matched the live files when these artifacts were saved.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or CI run.

- Mathematical source modules, including aggregation entrypoints: 94.
- Audited declarations, including private declarations: 2,642.
- Private-name declarations: 498. Public-name declarations: 2,144, all exported.
- Exported audited names: 2,160, including sixteen generated private-name equations/splitters.
  Private and exported flags are not mutually exclusive.
- Actual and allowed axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 47 proved, 2 partial, 1 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `2ef0132ae129a20ad6d8cc61a2dab5b9648d3882b57201f8d85bfa65feb4b915`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` also records configuration, tests, scripts, and
paper-map inputs; `declarations.json` records every module, declaration visibility, and axiom set.

This checkpoint completes Definition 2.7 and Remark 2.8. The native Lie classes satisfy the
paper's four axioms, and a biadditive alternating bracket with cyclic Jacobi constructs a
native Lie ring. Positive grading has degree zero equal to zero. Generation by degree one is
equivalent to the successor-bracket condition in every positive degree. The proof uses Jacobi,
iterated brackets, and actual direct-sum projections, over any commutative ring and in any rank.
The source correspondence received independent mathematical review.

The paper-map lexer now preserves Unicode identifiers such as `map₂`. Exact names and source
lines were checked directly, and all mapped declarations were checked against the kernel manifest.

Build, imports, environment lint, text lint, axiom audit, and paper-map checks took
1.203, 0.565, 2.253, 5.693, 188.835, and 0.237 seconds, respectively.

The main theorem and model-companion existence remain proved at the preceding checkpoint.
Remark 4.10, remaining examples and notation, and bridges for general semantic universes are
unfinished. The full-paper goal stays active. See
[the checkpoint](../../../positive-grading-checkpoint.md).
Previous artifacts remain preserved under `../main-theorem/`.
