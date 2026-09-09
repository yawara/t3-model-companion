# Exterior, quotient, and finite-diagram verification

2026-09-10. All six steps in `python3 scripts/check.py` completed with exit code 0 and zero warnings.
The source hashes in `checks.json` were checked again when this record was saved.
The pinned Lean/mathlib cache was used; this is local verification, not a clean build of mathlib or a CI run.

- Mathematical modules, including aggregation entrypoints: 34.
- Audited source declarations, including private declarations: 1,300.
- Private declarations: 242. Exported declarations: 1,058.
- Allowed and actual axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper-map states: 24 proved, 4 partial, 22 planned, across 50 items.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `e3de61dd26f9d1aae8103af7978dd3efdcb8656534e580c143c83938a8ec654a`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. `checks.json` additionally records configuration, tests, scripts,
and paper-map input hashes. `declarations.json` records source modules, visibility, and axiom dependencies.

This checkpoint supplies the free group's exterior graded Lie isomorphism in arbitrary rank,
the canonical quotient-layer isomorphisms, direct-product layer isomorphisms, and conjugate
width three. It also supplies finite structure and generated-tuple diagrams, existentially
closed transfer fixing a finite common structure, and the local-finiteness definition.

The finite-conjunction representation of a tuple's diagram does not yet supply the count of
its theory-equivalence classes. Uniform local finiteness and the general criterion's reverse
implication remain open, as do the later coproduct, simultaneous roots, bounded envelope,
and main-theorem obligations. See `../../../exterior-quotient-diagram-checkpoint.md` for scope.

The previous checkpoint remains preserved under `../graded-lie/`.
