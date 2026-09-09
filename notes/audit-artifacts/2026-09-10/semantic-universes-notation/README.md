# Semantic universes and group notation

2026-09-10. All six stages of `python3 scripts/check.py` passed, exit 0 and zero warnings.
The input hashes matched the live files when these artifacts were saved.
This is local verification using the pinned cache, not a clean mathlib build or a CI run.

- 102 mathematical source modules, including aggregation entrypoints.
- 2,768 declarations; 522 private names and 2,246 public names, all latter exported.
- 2,262 exported names, including sixteen generated private equations/splitters.
- Actual and permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Paper map: 49 proved, 0 partial, 1 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `a7c4521c9a402b1b112ae00824f55b728bf1dcdbd405d92c384c63c688ed0d49`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. All input hashes and kernel declarations are included here.

This completes Notation 2.1, with arbitrary generating cardinals and the finite-rank bridge.
Local and uniform finiteness, existential reflection, and the Pi-two companion/EC model-class
equivalence hold in arbitrary model universes. The original EC group, strict-envelope, and
bounded-witness proofs now apply directly to arbitrary models with the same explicit bounds.
Independent source/type/proof reviews found no discrepancies.

Build, imports, environment lint, text lint, axiom audit and paper-map verification took
2.614, 0.591, 2.282, 5.993, 199.156 and 0.263 seconds, respectively.

Remark 4.10 and the general-universe ordinary-amalgamation criterion remain unfinished at
this checkpoint. The full-paper goal stays active. See
[the checkpoint](../../../semantic-universes-and-notation-checkpoint.md).
All earlier artifacts remain unchanged.
