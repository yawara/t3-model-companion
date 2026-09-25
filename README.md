# t3-model-companion

Lean formalization of *Existence of a Model Companion for Groups of Exponent 3*.

- Manuscript authors: **Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi**.
- Formalization author and responsible maintainer: **Yawara Ishida**.
- License: [Apache-2.0](LICENSE).

The [manuscript](T3_modelcompanion_v9.tex) proves that the theory of groups satisfying
`x^3 = 1` has a model companion. The main group-theoretic theorem bounds the number
of generators needed to witness non-amalgamation with an existentially closed group by
`15 * ((3*m+4) * (m + choose(m,2) + choose(m,3)) + 1)^2`.
The proof includes the trivial group and arbitrary ranks and model universes as documented.

This repository contains the substantive formal proof development. GitHub confirmed it was private
on 2026-09-22. Palomar files prepare a future submission. No submission or registration has occurred.

## Reading the formalization

- [Paper-order Lean entrypoint](T3/Paper.lean)
- [Paper map: 57 active v9 items and 3 retained inactive items](docs/paper-map.md)
- [Module and namespace policy](notes/lean-architecture.md)
- [v9 manuscript PDF](T3_modelcompanion_v9.pdf)
- [v9 source migration and verification](notes/v9-migration.md)
- [Historical v7 formalization and verification](notes/v7-formalization.md)
- [Archived v7 Section 6 analysis and remaining questions](notes/section-six-analysis.md)
- [Paper correspondence](notes/paper-faithfulness-audit.md)
- [Historical v4 completion and encodings](notes/paper-faithful-completion.md)
- [Palomar statements, process, and verification scope](docs/palomar.md)
- [Structured authorship and review metadata](formalization.yaml)

`Challenge.lean` states Theorem 3.3 and Corollary 3.4 independently of the proof library.
`Solution.lean` imports their complete proofs. The two deliberate Challenge proof holes
are specification placeholders outside the mathematical import graph; all proof-library
and Solution declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The full paper map and the two selected Comparator declarations have distinct scopes.
The map records 56 proved active items and the open Conjecture 1.1 in v9,
including every Section 5 example and result. The former Section 6, removed
from v9 and preserved in the archived v8 source,
retains three separately marked inactive entries: its two open questions and
the proved Burnside/local-finiteness equivalence. Across both scopes, 57 items
and all 80 parts are proved. The separate-paper announcement about sufficiently
large prime exponents is outside this library's proof scope.
The additional notes on [finite residuals](notes/section-six-finite-residual.md),
[coprime joins](notes/section-six-coprime-joins.md),
[obstruction criteria](notes/section-six-obstruction-criteria.md), and
[finite A-groups](notes/section-six-a-groups.md) are mathematical research notes;
their arguments have not been formalized in Lean.
The previous manuscripts and PDFs are preserved in [archives](archives/README.md).

OpenAI Codex agents implemented and reviewed the Lean development under Yawara Ishida's
direction. The manuscript separately records its authors' mathematical work and use of AI.
Agent fidelity review is distinct from Lean's kernel checks and from human peer review.

## Verification

Lean is pinned to v4.34.0 and mathlib to `5ed2965256430c3649e86755f9576b54eca72435`.
The [v9 migration and review](notes/v9-migration.md) records the current source update,
mathematical correspondence review, and verification. The received TeX is preserved unchanged;
editorial suggestions are recorded separately and are not applied to the manuscript.
The [readiness checkpoint](notes/palomar-readiness-2026-09-22.md) records
verification of the v7 snapshot on these pins. The earlier [v7 checks](notes/v7-formalization.md)
used v4.33.1 and remain available as historical evidence.
With elan and Python 3.11 or later:

```sh
python3 -m pip install -r requirements-palomar.txt
lake exe cache get
python3 scripts/check.py
```

This checks metadata and source-map regression fixtures, builds the proof library and Solution,
checks imports and mathlib lint,
audits all proof declarations, and checks the paper map. Warnings fail the proof-library gate.
The text linters also cover Challenge and Solution. Logs and input hashes are in `.audit/`.

The separate statement comparison needs Linux, Cargo, Go, Git, Lake, and Python:

```sh
scripts/verify-comparator.sh
```

The script builds pinned Comparator, an exporter built with Lean v4.34.0, NanoDa, and Landrun in `.cache/`.
It verifies the selected statements and runs the independent NanoDa kernel checker.
Challenge's two intentional proof-hole warnings are expected only in this separate gate.
GitHub Actions runs both verification jobs without submitting or registering anything.

After adding mathematical modules or changing paper bindings:

```sh
lake exe mk_all --lib T3 --module
python3 scripts/paper_map.py --write
```

`mk_all` may return nonzero when it updates `T3.lean`; its `--check` mode must subsequently pass.
Numerical functions remain in the normal-form, strict-envelope, and main-theorem modules.
The manuscript's bibliography identifies the mathematical references. Locally stored reference
materials and build caches are not part of the submitted source tree.
