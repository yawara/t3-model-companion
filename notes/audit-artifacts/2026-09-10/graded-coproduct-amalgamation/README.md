# Graded coproduct and bounded amalgamation verification

2026-09-10. All six steps in `python3 scripts/check.py` passed with exit code 0 and zero warnings.
Input hashes were compared with the live files before saving these artifacts.
This is local verification using the pinned Lean/mathlib cache, not a clean mathlib build or a CI run.

- Mathematical source modules, including aggregation entrypoints: 75.
- Audited declarations, including private declarations: 2,316.
- Private-name declarations: 385. Public-name declarations: 1,931, all exported.
- Exported audited names: 1,946. Fifteen generated private-name equation lemmas and splitters
  are also exported; private and exported flags are not mutually exclusive.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 36 proved, 6 partial, 8 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `698dc3a221b576e31035d9440bcc24d9fba16ad95a9e882b6ef718084d660653`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axioms.

This checkpoint completes Proposition 4.3: the canonical coproduct maps in all three degrees,
their naturality, and the block bracket inclusions. The degree-two and degree-three isomorphisms
follow the paper's free-presentation and signed exterior/tensor quotient argument in arbitrary rank.
It also completes strict coproduct injectivity (Lemma 4.4) and the central-series result for
arbitrary nontrivial G with F2 (Lemma 4.5), following the paper's component separation cases.

Both directions of the general bounded-amalgamation criterion (Fact 2.6) are proved for finite
languages and Pi-two locally finite theories. Finite structures need not be models of T;
the bound is uniform after fixing the finite inclusion and counts all obstruction generators.
The companion and existential-closedness predicates retain the documented canonical semantic
universe convention. General bridges to arbitrary model universes remain separate work.

The actual group language and T3, its Pi-two property and local finiteness are supplied.
The final model-companion implication is still conditional on the paper's bounded obstruction.
Simultaneous normal words for derived relators and the two generator-based dimension estimates
are also supplied; these do not complete commutator roots or strictification.

The main theorem, the 15n-squared envelope, the support bound, and remaining paper items are
unfinished. The full goal stays active. See [the checkpoint](../../../graded-coproduct-and-amalgamation-checkpoint.md).
Previous artifacts remain preserved under `../coproduct-tensor-companion/`.
