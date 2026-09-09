# Graded Lie checkpoint verification

2026-09-10. All six steps in `python3 scripts/check.py` completed with exit code 0 and zero warnings.
The source hashes in `checks.json` were checked again when this record was saved.
The pinned Lean/mathlib cache was used; this is local verification, not a clean build of mathlib or a CI run.

- Mathematical modules, including aggregation entrypoints: 25.
- Audited source declarations, including private declarations: 1,094.
- Private declarations: 193. Exported declarations: 901.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 19 proved, 5 partial, 26 planned, across 50 items.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `b9195744eed2e24da93b089b98ccbb16d690fccdcc7807e98b0c092abff93132`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axiom dependencies.

This checkpoint supplies the actual associated graded Lie structure, its natural maps and
degree-one generation, the truncated exterior Lie algebra, arbitrary-rank free-group layer
coordinate equivalences, and the model-completeness bridge. The free-group exterior Lie
isomorphism and the general criterion's reverse implication remain open, as do the later
coproduct, root, bounded-envelope, and main-theorem obligations.

The previous checkpoint remains preserved under
`../../2026-09-09/infinite-normal-form-graded/`.
