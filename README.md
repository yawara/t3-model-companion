# Existence of a Model Companion for Groups of Exponent 3: Lean Formalization

Lean 4 formalization of
[*Existence of a Model Companion for Groups of Exponent 3*](https://arxiv.org/abs/2609.30061)
by Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi.

This repository contains the formal proofs accompanying the paper and includes
the Challenge/Solution pair used by the **Palomar Registry**.

- Formalization author and responsible maintainer: **Yawara Ishida**.
- License: [Apache-2.0](LICENSE).

## Mathematical scope

The paper proves that the first-order theory of groups satisfying `x^3 = 1`
has a model companion. The main group-theoretic result gives an explicit bound
on the number of generators needed to witness failure of amalgamation with
an existentially closed group.

| Paper result | Lean declaration |
| --- | --- |
| Theorem 3.3: bounded witnesses to non-amalgamation | [`T3.exists_bounded_nonamalgamation_witness`](T3/Main/BoundedWitness.lean) |
| Corollary 3.4: existence of a model companion | [`T3.has_model_companion`](T3/Main/ModelCompanion.lean) |

The formalization covers the mathematical results proved in Sections 2–5,
including the supporting constructions and examples. Conjecture 1.1 and the
announced results for sufficiently large prime exponents are outside its proved scope.
The exponent condition includes the trivial group.

The proof library contains no `sorry` or project-specific axioms. Its axiom
dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.

## Reading the proofs

- [Paper-order entrypoint](T3/Paper.lean): a guide to the development following the paper.
- [Paper map](docs/paper-map.md): correspondence between paper statements and Lean declarations.
- [Challenge](Challenge.lean): independent statements of the two main results, importing only Mathlib.
- [Solution](Solution.lean): the corresponding completed proofs from the library.

Challenge contains two deliberate proof holes, one for each selected theorem.
They serve as specification placeholders for Comparator; the proofs are supplied
by Solution. Comparing these two declarations and reviewing the full paper
correspondence are separate checks.

## Build and verification

Install elan and Python 3.11 or later. The Lean version is fixed by
[lean-toolchain](lean-toolchain), and dependency revisions are pinned in
[lake-manifest.json](lake-manifest.json).

```sh
python3 -m pip install -r requirements-palomar.txt
lake exe cache get
python3 scripts/check.py
```

This builds the proof library and Solution, checks imports and mathlib lint,
audits axiom dependencies, and validates the metadata and paper map.
Warnings fail the library checks. Logs and input hashes are written to `.audit/`.

The separate statement comparison uses Lean's bundled Comparator, with Lean,
NanoDa, and con-ron checking the proofs:

```sh
scripts/verify-comparator.sh
```

This requires Linux and bubblewrap 0.12.0 with working user namespaces.
See [Palomar verification requirements](docs/palomar.md) for setup details
and the scope of the verification performed so far.

## Palomar registration and citation

Version 1 is registered as
[PALOMAR-2026-09-26-000004 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-26-000004&version=1),
at commit `dfefd8dab8a1f818dfe0ea2238d9edf086c6f8a6`. The registration selects
Theorem 3.3 and Corollary 3.4 through [comparator.json](comparator.json).
The current title adds **Lean Formalization** for the proposed version 2,
so citations can distinguish the formalization from the source paper.

Cite [the paper](https://arxiv.org/abs/2609.30061) by Yawara Ishida, Ryosuke Mizuno,
and Kota Takeuchi for the mathematical result, and the relevant Palomar version
by Yawara Ishida for this formalization. Version 1 retains its original title.
[Palomar documentation](docs/palomar.md) describes the statements, verification
history, and version-update requirements.

AI agents contributed to the implementation and review under Yawara Ishida's direction.
See [formalization.yaml](formalization.yaml) for provenance and review details.
