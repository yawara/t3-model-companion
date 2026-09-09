# Main theorem and model-companion verification

2026-09-10. All six steps of `python3 scripts/check.py` passed with exit code 0 and zero warnings.
Input hashes matched the live files when these artifacts were saved.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or CI run.

- Mathematical source modules, including aggregation entrypoints: 93.
- Audited declarations, including private declarations: 2,620.
- Private-name declarations: 488. Public-name declarations: 2,132, all exported.
- Exported audited names: 2,148, including sixteen generated private-name equations/splitters.
  Private and exported flags are not mutually exclusive.
- Actual and allowed axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 45 proved, 2 partial, 3 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `59bf3bacaa6981adddf1d216ff2a71f2b9d8bc23e3512909e25883280251f699`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` also records configuration, tests, scripts, and
paper-map inputs; `declarations.json` records every module, declaration visibility, and axiom set.

This checkpoint completes Theorem 3.3 and Corollary 3.4 in the canonical semantic universe.
The exact bound is `15*((3*m+4)*t(m)+1)^2`. The proof follows the logarithmic rank comparison,
the internal normal-closure support, the strict envelope, and the injective coproduct comparison.
Both factor-witness alternatives are proved. The general obstruction criterion receives the
same finite base and a bound on all generators, yielding unconditional `HasModelCompanion`.
The bound and the group/language conversion received independent mathematical review.

Build, imports, environment lint, text lint, axiom audit, and paper-map checks took
2.511, 0.583, 2.292, 5.562, 188.010, and 0.235 seconds, respectively.

Remaining definitions, remarks, examples, notation, and bridges for general semantic universes
are unfinished. The full-paper goal stays active. See
[the checkpoint](../../../main-theorem-checkpoint.md).
Previous artifacts remain preserved under `../strict-envelope-pushout/`.
