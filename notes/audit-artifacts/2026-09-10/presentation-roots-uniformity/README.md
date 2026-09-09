# Presentation, roots, and uniformity verification

2026-09-10. All six steps in `python3 scripts/check.py` completed with exit code 0 and zero warnings.
The source hashes in `checks.json` were checked again when this record was saved.
The pinned Lean/mathlib cache was used; this is local verification, not a clean build of mathlib or a CI run.

- Mathematical modules, including aggregation entrypoints: 41.
- Audited source declarations, including private declarations: 1,472.
- Private-name declarations: 288. Public-name declarations: 1,184; all are exported.
- The exported environment contains 1,186 audited names, including two generated private-name
  equation lemmas for `TripleRoots.bundledRelator` and `TripleRoots.relationWord`.
  The private and exported flags in the inventory therefore overlap in these two entries.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 31 proved, 3 partial, 16 planned, across 50 items.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `88d4fa414ea6f4325b55f71fe25d94cac332589e26d49974b601fcc0132b06ee`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axiom dependencies.

This checkpoint supplies Proposition 4.1 for specified basis representatives, all three
statements of Lemma 4.2 for general groups, and the simultaneous triple-root quotient and
base embedding of Lemma 4.8. It supplies block homogeneity and the canonical quotient
isomorphism of Definition 2.10 and Proposition 2.11. The exterior basis blocks now have an
actual internal direct-sum decomposition, but their tensor identifications remain open.

It also supplies Fact 2.5, including a common bound for all generated subsets of size at
most n, and finite theory-equivalence representatives for the formulas in a tuple diagram.
Definition 2.2 is complete under the documented canonical semantic universe convention.
Bridges to arbitrary model universes remain separate work.

The coproduct maps and tensor blocks, simultaneous commutator roots, dimension estimates,
15n² envelope, general criterion, and main theorem remain unfinished. See
`../../../presentation-roots-and-uniformity-checkpoint.md` for the precise scope and next steps.

The previous checkpoint remains preserved under `../exterior-quotient-diagram/`.
