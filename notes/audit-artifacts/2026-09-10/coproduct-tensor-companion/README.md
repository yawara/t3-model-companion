# Coproduct tensor and model companion verification

2026-09-10. All six steps in `python3 scripts/check.py` completed with exit code 0 and zero warnings.
The source hashes in `checks.json` were checked again when this record was saved.
The pinned Lean/mathlib cache was used; this is local verification, not a clean build of mathlib or a CI run.

- Mathematical modules, including aggregation entrypoints: 53.
- Audited source declarations, including private declarations: 1,789.
- Private-name declarations: 309. Public-name declarations: 1,480; all are exported.
- Exported audited names: 1,484. This includes four generated private-name equation lemmas for
  `ExteriorTensor.appendOrderEmbedding`, `TripleRoots.bundledRelator`, `TripleRoots.relationWord`,
  and `Coproduct.Presentation.projectionLeft`. Private and exported flags overlap in these entries.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 32 proved, 3 partial, 15 planned, across 50 items.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `ab88bd971dc348f35c07e9402f1ee244391eaad8fd3709962be1a7c7a111b7d8`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axiom dependencies.

This checkpoint supplies both directions of Fact 2.3 for arbitrary Pi-two theories under
the documented canonical semantic universe convention. It reuses and extends the existing
existentially closed extension, elementary chain, and Robinson test arguments. Bridges to
arbitrary model universes remain separate work.

For Proposition 4.3 it supplies the actual free quotient presentation, its relation kernel,
the four degree-three relation blocks, and canonical exterior/tensor isomorphisms in arbitrary
degree and rank. It also supplies naturality of the free exterior identifications and the
three mixed bracket formulas, including the negative sign in bidegree (1, 2).

The canonical degree-one coproduct map is an isomorphism. The canonical degree-two and
degree-three maps and their naturality are present, but their bijectivity and the block
bracket inclusions remain open. Proposition 4.3 therefore remains partial. Its degree-one
proof uses the coproduct universal property directly; the canonical map is the paper's map.

Strict coproducts, the F2 argument, simultaneous commutator roots, dimension estimates,
the 15n-squared envelope, the general bounded-amalgamation criterion, and the main theorem
remain unfinished. The full paper-faithful goal remains active. See
[the checkpoint](../../../coproduct-tensor-and-companion-checkpoint.md) for scope and next steps.

The previous checkpoint remains preserved under `../presentation-roots-uniformity/`.
