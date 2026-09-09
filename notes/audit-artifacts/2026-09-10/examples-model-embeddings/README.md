# Examples and arbitrary-universe model embeddings

2026-09-10. All six stages of `python3 scripts/check.py` passed with exit code 0 and zero warnings.
The recorded input hashes matched the live files when these artifacts were saved.
This is local verification using the pinned cache, not a clean mathlib build or a CI run.

- 96 mathematical source modules, including aggregation entrypoints.
- 2,734 declarations, including 514 private names and 2,220 public names, all of the latter exported.
- 2,236 exported names; sixteen generated private equations/splitters are also exported.
- Actual and allowed axiom set: `propext`, `Classical.choice`, `Quot.sound`.
- Paper map: 48 proved, 1 partial, 1 planned, across 50 items and 75 parts.
- TeX SHA256: `79745dfa1660a827c51ec3c6b2006ee9d6243cb4702f97a75e5b55357b89f50b`.
- Mathematical source revision: `4361f8312b86001a2ef7f9d59326d9165f8afa6e2e6f2aae37ff9169b2a2817d`.

The revision hashes the JSON serialization (`sort_keys=True`) of the mathematical-source
path-to-SHA256 dictionary. All input hashes and all kernel declarations are included here.

Example 2.21 is complete: actual abelian Lie equivalence, product layers, and the free-two
central series, named bases, complete graded coordinates, bracket and homogeneous subspaces.
The model-embedding condition in Definition 2.2(1) extends to arbitrary source universes
by small elementary Skolem hulls and compactness of quantifier-free diagrams.

Build, imports, environment lint, text lint, axiom audit and paper-map verification took
2.462, 0.511, 2.333, 5.768, 196.705 and 0.244 seconds, respectively.

Notation 2.1, Remark 4.10 and the remaining semantic universe bridges are unfinished here.
The full-paper goal stays active. See [the checkpoint](../../../examples-and-model-embeddings-checkpoint.md).
Earlier artifacts remain preserved under `../positive-grading/` and the other checkpoint folders.
