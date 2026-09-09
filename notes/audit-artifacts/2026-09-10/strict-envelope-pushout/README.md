# Strict-envelope and pushout verification

2026-09-10. All six steps of `python3 scripts/check.py` passed with exit code 0 and zero warnings.
Input hashes matched the live files when these artifacts were saved.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or CI run.

- Mathematical source modules, including aggregation entrypoints: 87.
- Audited declarations, including private declarations: 2,590.
- Private-name declarations: 481. Public-name declarations: 2,109, all exported.
- Exported audited names: 2,125, including sixteen generated private-name equations/splitters.
  Private and exported flags are not mutually exclusive.
- Actual and allowed axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 43 proved, 4 partial, 3 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `74f7ca9dd544ffce1448cd86f75c50d9d379d721b2823d6ec23403fd845b6d6c`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` also records configuration, tests, scripts, and
paper-map inputs; `declarations.json` records every module, declaration visibility, and axiom set.

This checkpoint completes the canonical-universe conclusions of Proposition 4.12 and Proposition A.
The exact `15n²` bound follows from the two simultaneous strictifications and adjoining `F₂`.
The finite-diagram transfer fixes the whole original subgroup, and trivial inputs including `n = 0`
are handled separately. The algebraic extension construction works in every universe.
The main theorem's actual pushout, ordinary-amalgam criterion, arbitrary target universe bridge,
and both possible nontrivial factor witnesses are proved. Generating-family relators suffice.

Build, imports, environment lint, text lint, axiom audit, and paper-map checks took
5.109, 0.508, 2.236, 5.383, 182.492, and 0.227 seconds, respectively.

The bounded-witness theorem, unconditional model-companion existence, remaining paper items,
and bridges for general semantic universes remain unfinished. The full goal stays active.
See [the checkpoint](../../../strict-envelope-and-pushout-checkpoint.md).
Previous artifacts remain preserved under `../strictification/`.
