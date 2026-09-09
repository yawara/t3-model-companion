# Simultaneous commutator roots and bounded support verification

2026-09-10. All six steps in `python3 scripts/check.py` passed with exit code 0 and zero warnings.
Input hashes were compared with the live files before saving these artifacts.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or CI run.

- Mathematical source modules, including aggregation entrypoints: 80.
- Audited declarations, including private declarations: 2,481.
- Private-name declarations: 462. Public-name declarations: 2,019, all exported.
- Exported audited names: 2,035. Sixteen generated private-name equation lemmas and splitters
  are also exported; private and exported flags are not mutually exclusive.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 39 proved, 5 partial, 6 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `b6d901b5f03089873409af74e0de6236f8f35350ba89106b8a763e67926b4b64`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axioms.

This checkpoint completes the simultaneous commutator-root quotient and its injective base map
(Lemma 4.6), following Claims A, B, and C for arbitrary base groups and finite families.
It completes all three conclusions about existentially closed T3 models in Proposition 4.11,
using the actual root extensions and finite-diagram transfers. The existing canonical semantic
universe convention remains in force; general bridges to arbitrary universes are separate work.

Lemma 3.2 now has the exact support bound `3(m+1)n`. Collection uses a generating list of B;
the support certificate lies in the normal closure computed inside the generated subgroup.
The conclusion includes mathlib's generator rank, and covers empty relator sets and zero bounds.
All three paper results received independent source and proof review.

The main theorem, the 15n-squared envelope, both strictification steps, and remaining paper items
are unfinished. The full goal stays active. See
[the checkpoint](../../../commutator-roots-and-support-checkpoint.md).
Previous artifacts remain preserved under `../graded-coproduct-amalgamation/`.
